import Data.Set (Set)
import qualified Data.Set as Set
import Text.PrettyPrint
import Debug.Trace

-- -----------------------------------------------------------------------------
-- Expressions and helpers

type Var = String
type Pat = Expr
data Expr
  = App Expr Expr
  | Var Var
  | OpApp Expr Var Expr
  | Tuple [Expr]
  | Do [Stmt] Expr
  | Lam Pat Expr
  deriving Show

data Stmt = BindStmt { stmtPat :: Pat, stmtExpr ::  Expr }
  deriving Show

doE [] last = last
doE stmts (Do stmts' last) = doE (stmts++stmts') last
doE stmts last = Do stmts last

tupleE [one] = one
tupleE more = Tuple more

patVars :: Pat -> Set Var
patVars = exprVars

exprVars :: Expr -> Set Var
exprVars (Var v) = Set.singleton v
exprVars (App l r) = exprVars l `Set.union` exprVars r
exprVars (OpApp l op r) = Set.insert op (exprVars l `Set.union` exprVars r)
exprVars (Tuple pats) = Set.unions (map exprVars pats)
exprVars (Lam pat e) = exprVars e `Set.difference` patVars pat
exprVars (Do stmts e) =
  Set.unions (map exprVars [ e | BindStmt _ e <- stmts ])
    `Set.union`  exprVars e

applicativeLastStmt :: [Stmt] -> Expr -> Expr
applicativeLastStmt stmts expr = expr'
  where
   arity = length stmts
   (pats,exprs) = unzip [ (pat,expr) | BindStmt pat expr <- stmts ]
   ops = "<$>" : repeat "<*>"
   fun = foldr Lam expr pats
   expr' = App (Var "join") (foldl mk_app_call fun (zip ops exprs))
   mk_app_call l (op,r) = OpApp l op r

pprStmt :: Stmt -> Doc
pprStmt (BindStmt pat expr) = pprExpr pat <+> text "<-" <+> pprExpr expr

pprExpr :: Expr -> Doc
pprExpr (App f x) = pprExpr f <+> pprExpr9 x
pprExpr (OpApp l op r) =
  hang (pprExprL l) 2 (text op <+> pprExprR r)
pprExpr (Do stmts e) =
  hang (text "do") 2 (vcat (map pprStmt stmts) $$ pprExpr e)
pprExpr (Lam pat e) = text "\\" <> pprExpr pat <+> text "->" <+> pprExpr e
pprExpr other = pprExpr9 other

pprExprL (App f x) = pprExpr f <+> pprExpr9 x
pprExprL (OpApp l op r) =
  hang (pprExprL l) 2 (text op <+> pprExprR r)
pprExprL other = pprExpr9 other

pprExprR (App f x) = pprExpr f <+> pprExpr9 x
pprExprR other = pprExpr9 other

pprExpr9 :: Expr -> Doc
pprExpr9 (Var v) = text v
pprExpr9 (Tuple pats) = parens (hcat (punctuate comma (map pprExpr pats)))
pprExpr9 e = parens (pprExpr e)

-- -----------------------------------------------------------------------------
-- Simple ApplicativeDo

simpleAdo :: ([Stmt],Expr) -> ([Stmt],Expr)
simpleAdo ([],last) = ([],last)
simpleAdo (stmts@(stmt:more), last)
  | Just (group,[]) <- indep
  = ([],applicativeLastStmt group last)
  | Just (group, rest) <- indep
  = let (rest',last') = simpleAdo (rest,last) in
    (applicativeBindStmt group : rest', last')
  | otherwise
  = let (rest',last) = simpleAdo (more,last) in
    (stmt : rest', last)
  where
   indep = slurpIndep stmts

slurpIndep :: [Stmt] -> Maybe ([Stmt],[Stmt])
slurpIndep stmts = go [] Set.empty stmts
 where
  -- If we encounter a BindStmt that doesn't depend on a previous BindStmt
  -- in this group, then add it to the group.
  go indep bndrs (BindStmt pat body : rest)
    | Set.null (bndrs `Set.intersection` fvs)
    = go (BindStmt pat body : indep) bndrs' rest
    where bndrs' = bndrs `Set.union` patVars pat
          fvs = exprVars body
  go []  _ _ = Nothing
  go [_] _ _ = Nothing
  go indep _ stmts = Just (reverse indep, stmts)

applicativeBindStmt :: [Stmt] -> Stmt
applicativeBindStmt stmts =
  BindStmt (Tuple pats) expr'
  where
   arity = length stmts
   (pats,exprs) = unzip [ (pat,expr) | BindStmt pat expr <- stmts ]
   ops = "<$>" : repeat "<*>"
   tuple = Var ("(" ++ replicate arity ',' ++ ")")
   expr' = foldl mk_app_call tuple (zip ops exprs)
   mk_app_call l (op,r) = OpApp l op r


-- -----------------------------------------------------------------------------
-- General ApplicativeDo

-- T(s1;...;sn;L) =
--   - chop s1...sn into segments, where if there are no dependencies
--     across a statement boundary (not including from L) then that is
--     a segment boundary
--   - take each segment, si;...;sj, make it
--     s1;...;sj;return (tup (si..sj))
--   - if there are multiple segments, S1..Sk
--       L <$> T(S1) <*> ... <*> T(Sn)
--   - if there is a single segment, then
--     - find a good place to insert a bind: si
--       T(s1;...;si; do { si+1;..;sn;L })

betterAdo :: [Stmt] -> ([Stmt],Expr) -> ([Stmt],Expr)
betterAdo [] last = last
betterAdo [one] (stmts,last) = (one:stmts,last)
betterAdo stmts last@(last_stmts,last_expr) =
  case segments stmts of
    [] -> error "betterAdo"
    [one] -> betterAdo before (betterAdo after last)
      where (before,after) = splitSegment one
    more -> applicativeStmt (map trSeg more) last
      where
        lastvars = Set.unions (exprVars last_expr :
                      map (exprVars . stmtExpr) last_stmts)
        trSeg :: [Stmt] -> Stmt
        trSeg [one] = one
        trSeg stmts = BindStmt pat $ uncurry doE $
                         betterAdo stmts ([], App (Var "return") pat)
          where
            pvars = Set.unions (map patVars (map stmtPat stmts))
                      `Set.intersection` lastvars
            pat = tupleE (map Var (Set.toList pvars))


applicativeStmt :: [Stmt] -> ([Stmt],Expr) -> ([Stmt],Expr)
applicativeStmt stmts ([],last) = ([], applicativeLastStmt stmts last)
applicativeStmt stmts (rest,last) = (applicativeBindStmt stmts : rest, last)

segments :: [Stmt] -> [[Stmt]]
segments stmts = reverse $ map reverse $ walk (reverse stmts)
  where
    allvars = Set.unions (map (patVars . stmtPat) stmts)

    walk [] = []
    walk (BindStmt p e : stmts) = (BindStmt p e : seg) : walk rest
      where (seg,rest) = chunter (exprVars e `Set.intersection` allvars) stmts

    chunter vars rest
       | Set.null vars = ([],rest)
       | null rest = error ("chunter: " ++ show vars)
    chunter vars (BindStmt p e : rest)
       = (BindStmt p e : chunk, rest')
       where (chunk,rest') = chunter vars' rest
             evars = exprVars e `Set.intersection` allvars
             vars' = (vars `Set.difference` patVars p) `Set.union` evars

{-
  -- (a|b ; c|d)
  x <- a
  y <- b
  -- split here (x/y live)
  z <- c x
  w <- d y

  -- (a|b ; c)
  x <- a
  y <- b
  -- split here (x/y live)
  z <- c x y

  -- (a; b|c)
  x <- a
  -- split here (x live)
  y <- b x
  z <- c x

  -- (a|(b;c) ; d)
  -- could also (a; (b;c)|d)
  -- impossible to know which is better
  x <- a
  y <- b
  -- not here (x/y live)
  z <- c y
  -- split here (x/z live)
  w <- d x z
-}

splitSegment :: [Stmt] -> ([Stmt],[Stmt])
splitSegment [] = error "splitSegment"
splitSegment (s:ss) =
  case slurpIndep (s:ss) of -- ok for all but the last example above
    Nothing -> ([s], ss)
    Just r -> r

-- -----------------------------------------------------------------------------
-- Examples & test framework

runtest :: ([Stmt] -> Expr -> Expr) -> Expr -> Doc
runtest f (Do stmts last) =
  pprExpr (Do stmts last) $$
  text "===>" $$
  pprExpr (f stmts last)

t0 :: Expr -> Doc
t0 = runtest (\stmts last -> uncurry doE $ simpleAdo (stmts,last))

t1 :: Expr -> Doc
t1 = runtest (\stmts last -> uncurry doE $ betterAdo stmts ([],last))

(x1:x2:x3:x4:x5:x6:x7:_) = map Var (map (('x':) . show) [1..])
[w,x,y,z] = map Var ["w","x","y","z"]
[a,b,c,d,e,f,g,h] = map Var ["a","b","c","d","e","f","g","h"]

mkApps :: Expr -> [Expr] -> Expr
mkApps f args = foldl App f args

ex1 :: Expr
ex1 = Do
 [ BindStmt x a
 , BindStmt y b
 ] (foldl App f [x,y])
{-
a | b

(\x -> \y -> f x y) <$> a <*> b
-}

ex2 :: Expr
ex2 = Do
 [ BindStmt x a
 , BindStmt y (App g x)
 ] (foldl App f [x,y])
{-
no parallelism

do
  x <- a
  y <- g x
  f x y
-}

ex3 :: Expr
ex3 = Do
 [ BindStmt x a
 , BindStmt y b
 , BindStmt z (App g y)
 , BindStmt w e
 ] (foldl App f [x,y,z,w])
{-
a | (b;g) | e

(\x -> \(y,z) -> \w -> f x y z w) <$> a
  <*> (do
         y <- b
         z <- g y
         return (y,z))
  <*> e
-}

ex4 :: Expr
ex4 = Do
 [ BindStmt x a
 , BindStmt y b
 , BindStmt z (App g x)
 , BindStmt w c
 ] (foldl App f [y,z,w])
{-

(a ; b | g) | c
or
((a | b); g) | c

(\(y,z) -> \w -> f y z w)
  <$> (do
         x <- a
         (\y -> \z -> return (y,z)) <$> b <*> g x)
  <*> c

join ((\(y,z) -> \w -> f y z w)
        <$> (do
               (x,y) <- (,,) <$> a <*> b
               z <- g x
               return (y,z))
        <*> c)
-}

ex5 :: Expr
ex5 = Do
 [ BindStmt x a
 , BindStmt y b
 , BindStmt z c
 , BindStmt w (App g x)
 , BindStmt x1 (App h z)
 ] (foldl App f [y,w,x1])
{-
(a | b | c) ; (g | h)

join ((\x -> \y -> \z -> join ((\w -> \x1 -> f y w x1) <$> g x
                                 <*> h z))
        <$> a
        <*> b
        <*> c)
-}

ex6 :: Expr
ex6 = Do
 [ BindStmt x a
 , BindStmt x1 (App b x)
 , BindStmt x2 (App c x)
 , BindStmt y (App d x2)
 , BindStmt x3 (App e y)
 , BindStmt x4 (App f y)
 , BindStmt z (App g x4)
 ] (foldl App h [x,x1,x2,y,x3,x4,z])
{-
b/c in parallel, e/f in parallel:
a ; b | (c ; d ; (e | (f ; g)))

do
  x <- a
  (\x1 -> \(x2,x3,x4,y,z) -> h x x1 x2 y x3 x4 z) <$> b x
    <*> (do
           x2 <- c x
           y <- d x2
           (\x3 -> \(x4,z) -> return (x2,x3,x4,y,z)) <$> e y
             <*> (do
                    x4 <- f y
                    z <- g x4
                    return (x4,z)))
-}

ex7 :: Expr
ex7 = Do
 [ BindStmt x1 a
 , BindStmt x2 b
 , BindStmt x3 (App c x1)
 , BindStmt x4 (App d x2)
 ] (foldl App f [x3,x4])
{-
a/b in parallel, c/d in parallel

(\x1 -> \x2 -> (\x3 -> \x4 -> f x3 x4) <$> c x1 <*> d x2) <$> a
  <*> b
-}

ex8 :: Expr
ex8 = Do
 [ BindStmt x1 a
 , BindStmt x2 b
 , BindStmt x3 (App c x1)
 , BindStmt x4 (App d x2)
 , BindStmt x5 e
 ] (foldl App f [x3,x4,x5])
{-
a/b/e in parallel, c/d in parallel
((a | b) ; (c | d)) | e

(\(x3,x4) -> \x5 -> f x3 x4 x5)
  <$> ((\x1 -> \x2 -> (\x3 -> \x4 -> return (x3,x4)) <$> c x1
                        <*> d x2)
         <$> a
         <*> b)
  <*> e
-}


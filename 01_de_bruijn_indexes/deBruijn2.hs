import Data.List (elemIndex)


type Symb = String
infixl 2 :@:
infixl 2 :@

data Expr = Var Symb
          | Expr :@ Expr
          | Lam Symb Expr
          deriving (Eq, Read, Show)

data Term = Idx Int
          | Term :@: Term
          | Lmb Symb Term
          deriving (Read, Show)

instance Eq Term where
  Idx m     == Idx n      =  m == n
  (t1:@:s1) == (t2:@:s2)  =  t1 == t2 && s1 == s2
  Lmb _ t1  == Lmb _ t2   =  t1 == t2
  _         == _          =  False

type Context = [Symb]



e2t :: Expr -> (Context,Term)
e2t = go [] [] where
  go fs bs (Lam v ex) =
    Lmb v <$> go fs (v : bs) ex
  go fs bs (Var v)
    | Just i <- v `elemIndex` bs = (fs,        Idx i)
    | Just i <- v `elemIndex` fs = (fs,        Idx $ length bs + i)
    | otherwise                  = (fs ++ [v], Idx $ length bs + length fs)
  go fs bs (e1 :@ e2) =
    (t1 :@:) <$> (fs2, t2) where
      (fs1, t1) = go fs  bs e1
      (fs2, t2) = go fs1 bs e2


t2e :: Context -> Term -> Expr
t2e = go (iterate ('\'':) "'") where
  go :: [Symb] -> Context -> Term -> Expr
  go _      ctx (Idx i)     = Var $ ctx !! i
  go fresh  ctx (t1 :@: t2) = go fresh ctx t1 :@ go fresh ctx t2
  go (f:fs) ctx (Lmb v body)
    | v `elem` ctx = Lam newVar $ go fs (newVar : ctx) body
    | otherwise    = Lam v      $ go (f:fs)  (v : ctx) body
    where newVar = v ++ f

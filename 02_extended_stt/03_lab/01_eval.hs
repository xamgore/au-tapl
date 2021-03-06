import Control.Applicative ((<|>))
import Data.Function (on)
import Data.List (nubBy)

type Symb = String
infixl 2 :@:
infixr 3 :->
infixl 4 :/\

data Type = Boo
          | Type :-> Type
          | Type :/\ Type
    deriving (Read, Show, Eq)

data Pat = PVar Symb
         | PPair Pat Pat
    deriving (Read, Show, Eq)

data Term = Fls
          | Tru
          | If Term Term Term
          | Idx Int
          | Term :@: Term
          | Lmb Symb Type Term
          | Let Pat Term Term
          | Pair Term Term
          | Fst Term
          | Snd Term
          deriving (Read,Show)

instance Eq Term where
  Fls       == Fls          =  True
  Tru       == Tru          =  True
  If b u w  == If b1 u1 w1  =  b == b1 && u == u1 && w == w1
  Idx m     == Idx m1       =  m == m1
  (u:@:w)   == (u1:@:w1)    =  u == u1 && w == w1
  Lmb _ t u == Lmb _ t1 u1  =  t == t1 && u == u1
  Let p u w == Let p1 u1 w1 =  p == p1 && u == u1 && w == w1
  Pair u w  == Pair u1 w1   =  u == u1 && w == w1
  Fst z     == Fst z1       =  z == z1
  Snd z     == Snd z1       =  z == z1
  _         == _            =  False

newtype Env = Env [(Symb,Type)]
  deriving (Read,Show,Eq)

pairSize :: Term -> Int
pairSize (Pair u w) = pairSize u + pairSize w
pairSize _          = 1

shift :: Int -> Term -> Term
shift val = on 0 where
  on lvl (Idx i)        = Idx $ if lvl <= i then i + val else i
  on lvl (Lmb x t term) = Lmb x t $ on (lvl + 1) term
  on lvl (Let p t term) = Let p (on lvl t) $ on (lvl + pairSize t) term
  on lvl (If t1 t2 t3)  = If (on lvl t1) (on lvl t2) (on lvl t3)
  on lvl (tl :@: tr)    = on lvl tl :@: on lvl tr
  on lvl (Fst p)        = Fst $ on lvl p
  on lvl (Snd p)        = Snd $ on lvl p
  on lvl (Pair u w)     = Pair (on lvl u) (on lvl w)
  on lvl other          = other


substDB :: Int -> Term -> Term -> Term
substDB j s t@(Idx i)      = if i == j then s else t
substDB j s (Lmb x t body) = Lmb x t $ substDB (j + 1) (shift 1 s) body
substDB j s (Let x t body) = let psz = pairSize t in
                               Let x (substDB j s t) $
                                 substDB (j + psz) (shift psz s) body
substDB j s (tl :@: tr)    = substDB j s tl :@: substDB j s tr
substDB j s (If t1 t2 t3)  = If (substDB j s t1) (substDB j s t2) (substDB j s t3)
substDB j s (Fst p)        = Fst $ substDB j s p
substDB j s (Snd p)        = Snd $ substDB j s p
substDB j s (Pair u w)     = Pair (substDB j s u) (substDB j s w)
substDB _ _ other          = other

isValue :: Term -> Bool
isValue Tru         = True
isValue Fls         = True
isValue (Lmb _ _ _) = True
isValue (Pair u w) | isValue u && isValue w = True
isValue _           = False

match :: Pat -> Term -> Maybe [(Symb,Term)]
match (PVar x) v
  | isValue v = Just [(x, v)]
match (PPair pl pr) (Pair l r)
  | Just ml <- match pl l
  , Just mr <- match pr r
    = Just $ ml ++ mr
match _ _ = Nothing

betaRuleDB :: Term -> Term -> Term
betaRuleDB s t = shift (-1) $ substDB 0 (shift 1 t) s

betaRuleMatch :: Term -> [(Symb, Term)] -> Term
betaRuleMatch t = foldr (flip betaRuleDB) t . map snd

oneStep :: Term -> Maybe Term
oneStep (l@(Lmb x type' t1) :@: t2)
  | isValue t2         = Just $ betaRuleDB t1 t2
  | otherwise          = (l :@:) <$> oneStep t2
oneStep (tl :@: tr)    = (:@: tr) <$> oneStep tl
oneStep (If Tru t2 t3) = Just t2
oneStep (If Fls t2 t3) = Just t3
oneStep (If t1  t2 t3) = (\t -> If t t2 t3) <$> oneStep t1
oneStep l@(Let p t1 t2)
  | isValue t1, Just m <- match p t1 =
                Just $ betaRuleMatch t2 m
  | otherwise  = (\t -> Let p t t2) <$> oneStep t1
oneStep (Fst p@(Pair v1 v2))
  | isValue v1 && isValue v2 = Just v1
  | otherwise = Fst <$> oneStep p
oneStep (Snd p@(Pair v1 v2))
  | isValue v1 && isValue v2 = Just v2
  | otherwise = Snd <$> oneStep p
oneStep (t1 `Pair` t2)
  |      isValue t1  && not (isValue t2) = (t1 `Pair`) <$> oneStep t2
  | not (isValue t1) && not (isValue t2) = (`Pair` t2) <$> oneStep t1
oneStep _ = Nothing

whnf :: Term -> Term
whnf u | Just r <- oneStep u = whnf r
       | otherwise           = u


l = Let (PPair (PVar "a") (PVar "b")) (Pair (Lmb "x" Boo $ Idx 2) Fls) (Idx 1 :@: Idx 0 :@: Idx 2)
-- m = [("a",Lmb "x" Boo (Idx 1)),("b",Fls)]
-- z = foldr1 (.) (zipWith substDB [(-1),(-2)..] (snd <$> m)) (Idx 1 :@: Idx 0 :@: Idx 2)
--
-- test0 = Let (PPair (PVar "a") (PVar "b")) (Pair Tru Fls) (Idx 0)
-- test1 = Let (PPair (PVar "a") (PVar "b")) (Pair Tru Fls) (Idx 1)
-- test2 = Let (PPair (PVar "a") (PVar "b")) (Pair Tru Fls) (Idx 2)

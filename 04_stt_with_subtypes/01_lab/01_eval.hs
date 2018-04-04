import Control.Applicative ((<|>))
import Control.Monad (mapM, (>>=))
import Data.Function (on)
import Data.List (nubBy, find, findIndex, splitAt)
-- import qualified Data.Map as M

type Symb = String
infixl 2 :@:
infixr 3 :->

data Type = Boo
          | Type :-> Type
          | TRcd [(Symb,Type)]
    deriving (Read, Show, Eq)

data Pat = PVar Symb
         | PRcd [(Symb,Pat)]
    deriving (Read, Show, Eq)

data Term = Fls
          | Tru
          | If Term Term Term
          | Idx Int
          | Term :@: Term
          | Lmb Symb Type Term
          | Let Pat Term Term
          | Rcd [(Symb, Term)]
          | Prj Symb Term
          deriving (Read,Show)

instance Eq Term where
  Fls       == Fls          =  True
  Tru       == Tru          =  True
  If b u w  == If b1 u1 w1  =  b == b1 && u == u1 && w == w1
  Idx m     == Idx m1       =  m == m1
  (u:@:w)   == (u1:@:w1)    =  u == u1 && w == w1
  Lmb _ t u == Lmb _ t1 u1  =  t == t1 && u == u1
  Let p u w == Let p1 u1 w1 =  p == p1 && u == u1 && w == w1
  Rcd xs    == Rcd xs1      =  xs == xs1
  Prj l u   == Prj l1 u1    =  l == l1 && u == u1
  _         == _            =  False

newtype Env = Env [(Symb,Type)]
  deriving (Read,Show,Eq)

pvars :: Pat -> Int
pvars (PVar u)  = 1
pvars (PRcd ps) = sum $ map (pvars . snd) ps

shift :: Int -> Term -> Term
shift val = on 0 where
  on lvl (Idx i)        = Idx $ if lvl <= i then i + val else i
  on lvl (Lmb x t term) = Lmb x t $ on (lvl + 1) term
  on lvl (Let p t term) = Let p (on lvl t) $ on (lvl + pvars p) term
  on lvl (If t1 t2 t3)  = If (on lvl t1) (on lvl t2) (on lvl t3)
  on lvl (tl :@: tr)    = on lvl tl :@: on lvl tr
  on lvl (Prj l t)      = Prj l $ on lvl t
  on lvl (Rcd vs)       = Rcd $ map (fmap (on lvl)) vs
  on lvl other          = other


substDB :: Int -> Term -> Term -> Term
substDB j s t@(Idx i)      = if i == j then s else t
substDB j s (Lmb x t body) = Lmb x t $ substDB (j + 1) (shift 1 s) body
substDB j s (Let p t body) = let psz = pvars p in
                               Let p (substDB j s t) $
                                 substDB (j + psz) (shift psz s) body
substDB j s (tl :@: tr)    = substDB j s tl :@: substDB j s tr
substDB j s (If t1 t2 t3)  = If (substDB j s t1) (substDB j s t2) (substDB j s t3)
substDB j s (Prj l t)      = Prj l $ substDB j s t
substDB j s (Rcd vs)       = Rcd $ map (fmap (substDB j s)) vs
substDB _ _ other          = other

isValue :: Term -> Bool
isValue Tru         = True
isValue Fls         = True
isValue (Lmb _ _ _) = True
isValue (Rcd vs) | all (isValue . snd) vs = True
isValue _           = False


match :: Pat -> Term -> Maybe [(Symb,Term)]
match p v
  | not (isValue v) = Nothing
match (PVar x) v = Just [(x, v)]
match (PRcd fs) (Rcd vs)
  | namesAreSame = concat <$> (sequence matchedVars)
  where namesAreSame = (fst <$> fs) == (fst <$> vs)
        matchedVars  = zipWith match (snd <$> fs) (snd <$> vs)
match _ _ = Nothing


betaRule :: Term -> Term -> Term
betaRule s t = shift (-1) $ substDB 0 (shift 1 t) s

betaRuleMatch :: Term -> [(Symb, Term)] -> Term
betaRuleMatch t = foldr (flip betaRule) t . map snd

oneStep :: Term -> Maybe Term
oneStep (l@(Lmb x type' t1) :@: t2)
  | isValue t2         = Just $ betaRule t1 t2
  | otherwise          = (l :@:) <$> oneStep t2
oneStep (tl :@: tr)    = (:@: tr) <$> oneStep tl

oneStep (If Tru t2 t3) = Just t2
oneStep (If Fls t2 t3) = Just t3
oneStep (If t1  t2 t3) = (\t -> If t t2 t3) <$> oneStep t1

oneStep l@(Let p t1 t2)
  | isValue t1, Just m <- match p t1 =
                Just $ betaRuleMatch t2 m
  | otherwise  = (\t -> Let p t t2) <$> oneStep t1

oneStep (Prj s t@(Rcd kvs))
  | isValue t = fmap snd $ find ((s ==) . fst) kvs
oneStep (Prj s t) = (Prj s) <$> oneStep t

oneStep t@(Rcd kvs) = do
  firstNonValue <- findIndex (not . isValue . snd) kvs
  let (vs, nvs)  = splitAt (firstNonValue) kvs
  nvs' <- patch nvs
  return $ Rcd (vs ++ nvs')
  where
    patch []         = Nothing
    patch ((s,t):ts) = oneStep t >>= \t' -> Just ((s, t') : ts)

oneStep _ = Nothing

whnf :: Term -> Term
whnf u | Just r <- oneStep u = whnf r
       | otherwise           = u


-- l = Let (PPair (PVar "a") (PVar "b")) (Pair (Lmb "x" Boo $ Idx 2) Fls) (Idx 1 :@: Idx 0 :@: Idx 2)
-- m = [("a",Lmb "x" Boo (Idx 1)),("b",Fls)]
-- z = foldr1 (.) (zipWith substDB [(-1),(-2)..] (snd <$> m)) (Idx 1 :@: Idx 0 :@: Idx 2)
--
-- test0 = Let (PPair (PVar "a") (PVar "b")) (Pair Tru Fls) (Idx 0)
-- test1 = Let (PPair (PVar "a") (PVar "b")) (Pair Tru Fls) (Idx 1)
-- test2 = Let (PPair (PVar "a") (PVar "b")) (Pair Tru Fls) (Idx 2)

--
--
-- pat = PRcd [("lx",PVar "px"),("ly",PVar "py")]
-- rec = Rcd  [("lx",Tru),      ("ly",Fls)      ]
--
-- patHard = PRcd [("lx",PVar "px"), ("ly", PRcd [("la",PVar "pa"),("lz",PVar "pz")]) ]
-- recHard = Rcd  [("lx",Tru), ("ly", Rcd [("la",Fls), ("lz",Fls)]) ]
-- rc = Rcd  [("lx",Tru), ("ly", Rcd [("la", Tru), ("lz",Fls)]) ]
--
-- e1 = match pat rec
-- t1 = e1 == Just [("px",Tru),("py",Fls)]
--
-- e2 = oneStep $ Let pat rec $ If Tru (Idx 1) (Idx 0)
-- t2 = e2 == Just (If Tru Tru Fls)
--
-- e3 = whnf $ Let pat rec $ If Tru (Idx 1) (Idx 0)
-- t3 = e3 == Tru

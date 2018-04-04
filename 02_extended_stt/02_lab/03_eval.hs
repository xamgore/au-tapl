import Control.Applicative ((<|>))

type Symb = String
infixl 2 :@:
infixr 3 :->
infixl 4 :/\

data Type = Boo
          | Type :-> Type
          | Type :/\ Type
    deriving (Read,Show,Eq)

data Term = Fls
          | Tru
          | If Term Term Term
          | Idx Int
          | Term :@: Term
          | Lmb Symb Type Term
          | Let Symb Term Term
          | Pair Term Term
          | Fst Term
          | Snd Term
          deriving (Read,Show)

instance Eq Term where
  Fls       == Fls         =  True
  Tru       == Tru         =  True
  If b u w  == If b1 u1 w1 =  b == b1 && u == u1 && w == w1
  Idx m     == Idx m1      =  m == m1
  (u:@:w)   == (u1:@:w1)   =  u == u1 && w == w1
  Lmb _ t u == Lmb _ t1 u1 =  t == t1 && u == u1
  Let _ u w == Let _ u1 w1 =  u == u1 && w == w1
  Pair u w  == Pair u1 w1  =  u == u1 && w == w1
  Fst p     == Fst p1      =  p == p1
  Snd p     == Snd p1      =  p == p1
  _         == _           =  False

newtype Env = Env [(Symb,Type)]
  deriving (Read,Show,Eq)

shift :: Int -> Term -> Term
shift val = on 0 where
  on lvl (Idx i)        = Idx $ if lvl <= i then i + val else i
  on lvl (Lmb x t term) = Lmb x t $ on (lvl + 1) term
  on lvl (Let x t term) = Let x t $ on (lvl + 1) term
  on lvl (If t1 t2 t3)  = If (on lvl t1) (on lvl t2) (on lvl t3)
  on lvl (tl :@: tr)    = on lvl tl :@: on lvl tr
  on lvl (Fst p)        = Fst $ on lvl p
  on lvl (Snd p)        = Snd $ on lvl p
  on lvl (Pair u w)     = Pair (on lvl u) (on lvl w)
  on lvl other          = other

substDB :: Int -> Term -> Term -> Term
substDB j s t@(Idx i)      = if i == j then s else t
substDB j s (Lmb x t body) = Lmb x t $ substDB (j + 1) (shift 1 s) body
substDB j s (Let x t body) = Let x t $ substDB (j + 1) (shift 1 s) body
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

betaRuleDB :: Term -> Term
betaRuleDB (t@(Lmb _ _ _) :@: s) = body
  where (Lmb _ _ body) = shift (-1) $ substDB (-1) s t
betaRuleDB (t@(Let _ s _)) = body
  where (Let _ _ body) = shift (-1) $ substDB (-1) s t


oneStep :: Term -> Maybe Term
oneStep (l@(Lmb x type' t1) :@: t2)
  | isValue t2         = Just $ betaRuleDB (l :@: t2)
  | otherwise          = (l :@:) <$> oneStep t2
oneStep (tl :@: tr)    = (:@: tr) <$> oneStep tl
oneStep (If Tru t2 t3) = Just t2
oneStep (If Fls t2 t3) = Just t3
oneStep (If t1  t2 t3) = (\t -> If t t2 t3) <$> oneStep t1
oneStep l@(Let x t1 t2)
  | isValue t1 = Just $ betaRuleDB l
  | otherwise  = (\t -> Let x t t2) <$> oneStep t1
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


-- cSnd = Lmb "z" (Boo :/\ Boo) (Snd (Idx 0))
-- cCurry = Lmb "f" (Boo :/\ Boo :-> Boo) $ Lmb "x" Boo $ Lmb "y" Boo $ (Idx 2) :@: Pair (Idx 1) (Idx 0)
-- t1 = whnf (cCurry :@: cSnd :@: Fls :@: Tru) == Tru
-- t2 = whnf (cCurry :@: cSnd :@: Fls) == Lmb "y" Boo (Lmb "z" (Boo :/\ Boo) (Snd (Idx 0)) :@: Pair Fls (Idx 0))

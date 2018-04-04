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
  deriving (Read, Show)

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

newtype Env = Env [(Symb, Type)]
  deriving (Read, Show, Eq)

checkPat :: Pat -> Type -> Maybe Env
checkPat (PVar x)      t = Just $ Env [(x, t)]
checkPat (PPair p1 p2) (t1 :/\ t2)
  | Just (Env e1) <- checkPat p1 t1
  , Just (Env e2) <- checkPat p2 t2
    = Just $ Env (e1 ++ e2)
checkPat _ _ = Nothing

infer :: Env -> Term -> Maybe Type
infer _ Tru = Just Boo
infer _ Fls = Just Boo

infer (Env e) (Idx i) = Just $ snd $ e !! i

infer (Env e) (Lmb x ty body) = (ty :->) <$> sy
  where sy = infer (Env $ (x, ty) : e) body

infer (Env e) (Let p t body)
  | Just ty        <- infer (Env e) t
  , Just (Env ctx) <- checkPat p ty = infer (Env $ ctx ++ e) body

infer e (If t1 t2 t3)
  | Just ty1 <- infer e t1
  , Just ty2 <- infer e t2
  , Just ty3 <- infer e t3
  , ty1 == Boo && ty2 == ty3 = Just ty2

infer e (t1 :@: t2)
  | Just (ty1 :-> sy1) <- infer e t1
  , Just ty2           <- infer e t2
  , ty1 == ty2 = Just $ sy1

infer e (t1 `Pair` t2)
  | Just ty1 <- infer e t1
  , Just ty2 <- infer e t2
    = Just $ ty1 :/\ ty2

infer e (Fst p)
  | Just (ty1 :/\ ty2) <- infer e p
    = Just ty1

infer e (Snd p)
  | Just (ty1 :/\ ty2) <- infer e p
    = Just ty2

infer _ _ = Nothing


infer0 :: Term -> Maybe Type
infer0 = infer $ Env []

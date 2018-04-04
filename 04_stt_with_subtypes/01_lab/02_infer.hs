import Data.List (find)


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
          | Rcd [(Symb,Term)]
          | Prj Symb Term
  deriving (Read, Show)

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

newtype Env = Env [(Symb, Type)]
  deriving (Read, Show, Eq)

getEnv (Env e) = e

checkPat :: Pat -> Type -> Maybe Env
checkPat (PVar x) t = Just $ Env [(x, t)]
checkPat (PRcd fs) (TRcd ts)
  | namesAreSame = Env . concat . fmap getEnv <$> sequence matchedTypes
  where namesAreSame = (fst <$> fs) == (fst <$> ts)
        matchedTypes = zipWith checkPat (snd <$> fs) (snd <$> ts)
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

infer e (Rcd ps) = do
  let symbs = map fst ps
  let terms = map snd ps
  types <- traverse (infer e) terms
  return $ TRcd $ zip symbs types

infer e (Prj s rec)
  | Just (TRcd types) <- infer e rec
    = fmap snd $ find ((s ==) . fst) types

infer _ _ = Nothing


infer0 :: Term -> Maybe Type
infer0 = infer $ Env []



cK = Lmb "x" Boo (Lmb "y" Boo (Idx 1))
rec = Rcd  [("lB",Tru),     ("lK",cK)      ]
pat = PRcd [("lB",PVar "x"),("lK",PVar "y")]

e1 = infer0 rec
t1 = e1 == Just (TRcd [("lB",Boo),("lK",Boo :-> (Boo :-> Boo))])

e2 = checkPat pat <$> infer0 rec
t2 = e2 == Just (Just (Env [("x",Boo),("y",Boo :-> (Boo :-> Boo))]))

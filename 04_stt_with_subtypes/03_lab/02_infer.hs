import Data.List (find)
import qualified Data.Map.Strict as M
import Data.Map.Strict (isSubmapOfBy)
import Control.Monad (join)


type Symb = String
infix 1 <:
infixl 2 :@:
infixr 3 :->
infixl 4 \/
infix 5 /\

data Type = Boo
          | Type :-> Type
          | TRcd [(Symb,Type)]
          | Top
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


(<:) :: Type -> Type -> Bool
Boo       <: Boo         = True
t1        <: Top         = True
(s :-> t) <: (sd :-> ta) = (sd <: s) && (t <: ta)
(TRcd ks) <: (TRcd ls)   = ml `isSubmapOf` mk && mk `areDescendantsOf` ml
  where mk = M.fromList ks
        ml = M.fromList ls
        isSubmapOf       = isSubmapOfBy (const . const True)
        areDescendantsOf = (and .) . M.intersectionWith (<:)
_ <: _ = False


(\/) :: Type -> Type -> Type
s \/ t
  | (s == t) = s
(s :-> t) \/ (s' :-> t')
  | Just input <- (s /\ s') = input :-> (t \/ t')
(TRcd ss) \/ (TRcd ts) = TRcd $ M.toList union
  where union = M.intersectionWith (\/) (M.fromList ss) (M.fromList ts)
_ \/ _ = Top


(/\) :: Type -> Type -> Maybe Type
s /\ t
  | (s == t) = Just s
Top /\ t     = Just t
s   /\ Top   = Just s
(s :-> t) /\ (s' :-> t')
  | Just output <- (t /\ t') = Just $ (s \/ s') :-> output
(TRcd ss) /\ (TRcd ts) = TRcd <$> record
  where
    record = traverse sequence $ M.toList res
    res = M.unionWith intersect mss mts
    mss = Just <$> M.fromList ss
    mts = Just <$> M.fromList ts
    a1 `intersect` a2 = join $ (/\) <$> a1 <*> a2
_ /\ _ = Nothing


checkPat :: Pat -> Type -> Maybe Env
checkPat (PVar x)  t = Just $ Env [(x, t)]
checkPat (PRcd []) _ = Just $ Env []
checkPat (PRcd ((sym, pat):ps)) (TRcd ts) = do
  type'      <- snd <$> find ((sym ==) . fst) ts
  env        <- getEnv <$> checkPat pat type'
  (Env rest) <- checkPat (PRcd ps) (TRcd ts)
  return $ Env (env ++ rest)
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
  | Just Boo <- infer e t1
  , Just ty2 <- infer e t2
  , Just ty3 <- infer e t3
    = Just $ ty2 \/ ty3

infer e (t1 :@: t2)
  | Just (ty1 :-> sy1) <- infer e t1
  , Just ty2           <- infer e t2
  , ty2 <: ty1 = Just $ sy1

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



t1 = TRcd [("la",Boo),("lb",Boo)]
t2 = TRcd [("lb",Boo),("lc",Boo)]



-- body1 = Rcd [("lb",Prj "lb" (Idx 0)),("lc",Lmb "x" Boo $ Prj "lb" (Idx 1))]
-- func1 = Lmb "x" type1 body1
--
-- type2 = TRcd [("lb",Boo :-> Boo), ("lc",Boo :-> Boo :-> Boo)]
-- body2 = Rcd  [("lb",Prj "lb" (Idx 0)),("la",Prj "lb" (Idx 0) :@: Tru)]
-- func2 = Lmb "y" type2 body2
--
--
-- e1 = infer0 func1
-- t1 = e1 == Just (TRcd [("la",Boo),("lb",Boo :-> Boo)] :-> TRcd [("lb",Boo :-> Boo),("lc",Boo :-> (Boo :-> Boo))])
--
-- e2 = infer0 func2
-- t2 = e2 == Just (TRcd [("lb",Boo :-> Boo),("lc",Boo :-> (Boo :-> Boo))] :-> TRcd [("lb",Boo :-> Boo),("la",Boo)])
--
-- e3 = infer0 $ If Tru func1 func2
-- t3 = e3 == Just (TRcd [("la",Boo),("lb",Boo :-> Boo),("lc",Boo :-> (Boo :-> Boo))] :-> TRcd [("lb",Boo :-> Boo)])

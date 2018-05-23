import Data.Maybe (maybe)

type Symb = String

infixl 2 :@:
infixr 3 :->

data Expr = Idx Int          -- переменная как индекс Де Брауна
          | Ast              -- константа, базовый атом для кайндов
          | Box              -- константа высшего уровня
          | Expr :@: Expr    -- аппликация терма к терму или типа к типу
          | Lmb Decl Expr    -- абстракция терма или типа
          | Expr :-> Expr    -- стрелочный тип или кайнд
          | ForAll Symb Expr Expr -- полиморфный тип, второй аргумент - кайнд типовой переменной
    deriving (Read,Show,Ord)

instance Eq Expr where
  Idx n1      == Idx n2      = n1 == n2
  Ast         == Ast         = True
  Box         == Box         = True
  (u1 :@: u3) == (u2 :@: u4) = u1 == u2 && u3 == u4
  Lmb d1 u3   == Lmb d2 u4   = d1 == d2 && u3 == u4
  (t1 :-> t3) == (t2 :-> t4) = t1 == t2 && t3 == t4
  ForAll _ s1 t3 == ForAll _ s2 t4 = s1 == s2 && t3 == t4
  _           == _           = False

data Decl = EDecl Symb Expr --  объявление биндера с типом/кайндом, Symb - справочное имя переменной
    deriving (Read,Show,Ord)

instance Eq Decl where
  EDecl _ t1 == EDecl _ t2 = t1 == t2

type Env = [Decl]

lE :: Symb -> Expr -> Expr -> Expr
lE v = Lmb . EDecl v
----------------------

isKind :: Expr -> Bool
isKind e = e `elem` [Ast, Box]

isNF :: Expr -> Bool
isNF (Lmb (EDecl _ ex) body) = isNF ex && isNF body
isNF x = isNANF x

isNANF :: Expr -> Bool
isNANF (Idx _)   = True
isNANF (a :@: b) = isNANF a && isNF b
isNANF (a :-> b) = isNF a   && isNF b
isNANF (ForAll _ ty body) = isNF ty && isNF body
isNANF e         = isKind e

isNA :: Expr -> Bool
isNA (Idx _)   = True
isNA (_ :@: _) = True
isNA (_ :-> _) = True
isNA (ForAll _ _ _) = True
isNA _         = False

----------------------

validEnv :: Env -> Bool
validEnv [] = True
validEnv ((EDecl _ expr):ctx)
  = maybe False isKind (infer ctx expr) && validEnv ctx

shift :: Int -> Expr -> Expr
shift = shiftOn 0

shiftOn :: Int -> Int -> Expr -> Expr
shiftOn lvl val Ast = Ast
shiftOn lvl val Box = Box
shiftOn lvl val (Idx i)     = Idx $ if i < lvl then i else i + val
shiftOn lvl val (t1 :@: t2) = (shiftOn lvl val t1) :@: (shiftOn lvl val t2)
shiftOn lvl val (t1 :-> t2) = (shiftOn lvl val t1) :-> (shiftOn lvl val t2)
shiftOn lvl val (Lmb (EDecl n expr) term)
  = Lmb (EDecl n $ shiftOn lvl val expr) $ shiftOn (lvl + 1) val term
shiftOn lvl val (ForAll n ty body)
  = ForAll n (shiftOn lvl val ty) (shiftOn (lvl + 1) val body)

subst :: Int -> Expr -> Expr -> Expr
subst _ _ Ast = Ast
subst _ _ Box = Box
subst j s (Idx k)     = if k == j then s else Idx k
subst j s (t1 :@: t2) = (subst j s t1) :@: (subst j s t2)
subst j s (t1 :-> t2) = (subst j s t1) :-> (subst j s t2)
subst j s (Lmb (EDecl n expr) term)
  = Lmb (EDecl n $ subst j s expr) $ subst (j + 1) (shift 1 s) term
subst j s (ForAll n ty body)
  = ForAll n (subst j s ty) $ subst (j + 1) (shift 1 s) body

betaHelper :: Expr -> Expr -> Expr
betaHelper typ term = shift (-1) $ subst 0 (shift 1 typ) term

infer :: Env -> Expr -> Maybe Expr
infer env expr = if validEnv env then infer' env expr else Nothing

infer' :: Env -> Expr -> Maybe Expr
infer' _ Ast = Just Box

infer' env (Idx idx)
  | 0 <= idx && idx < length env
  , (EDecl _ expr) <- env !! idx
    = Just $ shift (idx + 1) expr

infer' env (ForAll name s b)
  | Just Box <- infer' env s
  , Just Ast <- infer (EDecl name s : env) b
    = Just Ast

infer' env (t1 :-> t2)
  | Just Ast <- infer' env t1, Just Ast <- infer' env t2 = Just Ast
  | Just Box <- infer' env t1, Just Box <- infer' env t2 = Just Box

infer' env (m :@: n)
  | Just (a :-> b) <- nf <$> infer' env m
  , Just a'        <-        infer' env n
  , nf a == nf a' = Just b

infer' env (m :@: a)
  | Just (ForAll x s b) <- nf <$> infer' env m
  , Just s'             <-        infer' env a
  , nf s' == nf s = Just $ betaHelper a b

infer' env (Lmb (EDecl x a) m)
  | Just b    <- infer (EDecl x a : env) m
  , Just True <- isKind <$> infer (EDecl x a : env) (shift 1 a :-> b)
    = Just $ a :-> shift (-1) b

infer' env (Lmb (EDecl name s) m)
  | Just b   <- infer (EDecl name s : env) m
  , Just Ast <- infer' env (ForAll name (shift 1 s) b)
    = Just $ ForAll name s b

infer' _ _ = Nothing


infer0 :: Expr -> Maybe Expr
infer0 = infer []

oneStep :: Expr -> Maybe Expr
oneStep (m :@: n)
  | isNA m,   Just m' <- oneStep m = Just $ m' :@: n
  | isNANF m, Just n' <- oneStep n = Just $ m  :@: n'
oneStep (a :-> b)
  | Just a'         <- oneStep a = Just $ a' :-> b
  | isNF a, Just b' <- oneStep b = Just $ a  :-> b'
oneStep (Lmb (EDecl name a) m)
  | Just a'         <- oneStep a = Just $ Lmb (EDecl name a') m
  | isNF a, Just m' <- oneStep m = Just $ Lmb (EDecl name a)  m'
oneStep ((Lmb (EDecl name a) m) :@: n)
  = Just $ betaHelper n m
oneStep (ForAll name s b)
  | isKind s, Just b' <- oneStep b = Just $ ForAll name s b'
oneStep _ = Nothing

nf :: Expr -> Expr
nf term | Just term' <- oneStep term = nf term'
        | otherwise                  = term


cD = lE "beta" Ast (Idx 0 :-> Idx 0)
test11 = infer0 cD
test12 = infer [EDecl "alpha" Ast] (lE "x" (cD :@: Idx 0) $ Idx 0) == Just ((cD :@: Idx 0) :-> (cD :@: Idx 0))
test13 = (nf <$> infer [EDecl "alpha" Ast] (lE "x" (cD :@: Idx 0) $ Idx 0)) == (nf <$> Just (cD :@: (cD :@: Idx 0)))
test14 = infer0 (lE "a" Ast $ lE "z" (Idx 0) $ Idx 0)

---------------------

-- Кодирование булевых значений в System F
boolT = ForAll "a" Ast $ Idx 0 :-> Idx 0 :-> Idx 0
fls = lE "a" Ast $ lE "t" (Idx 0) $ lE "f" (Idx 1) $ Idx 0
tru = lE "a" Ast $ lE "t" (Idx 0) $ lE "f" (Idx 1) $ Idx 1

ifThenElse = lE "a" Ast $ lE "v" boolT $ lE "x" (Idx 1) $ lE "y" (Idx 2) $ Idx 2 :@: Idx 3 :@: Idx 1 :@: Idx 0
notF = lE "v" boolT $ lE "a" Ast $ lE "t" (Idx 0) $ lE "f" (Idx 1) $ Idx 3 :@: Idx 2 :@: Idx 0 :@: Idx 1

-- Кодирование натуральных чисел в System F
natT = ForAll "a" Ast $ (Idx 0 :-> Idx 0) :-> Idx 0 :-> Idx 0
natAbs body = lE "a" Ast $ lE "s" (Idx 0 :-> Idx 0) $ lE "z" (Idx 1) body
zero  = natAbs $ Idx 0
one   = natAbs $ Idx 1 :@: Idx 0
two   = natAbs $ Idx 1 :@: (Idx 1 :@: Idx 0)
three = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0))
four  = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0)))
five  = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0))))
six   = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0)))))
seven = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0))))))
eight = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0)))))))
nine  = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0))))))))
ten   = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0)))))))))

-- Кодирование списков в System F omega
tListFo = lE "sigma" Ast $ ForAll "alpha" Ast $ (Idx 1 :-> Idx 0 :-> Idx 0) :-> Idx 0 :-> Idx 0

nilFo = lE "sigma" Ast
      $ lE "alpha" Ast
      $ lE "c" (Idx 1 :-> Idx 0 :-> Idx 0)
      $ lE "n" (Idx 1)
      $ (Idx 0)

consFo = lE "sigma" Ast
       $ lE "e" (Idx 0)
       $ lE "l" (tListFo :@: Idx 1)
       $ lE "alpha" Ast
       $ lE "c" (Idx 3 :-> Idx 0 :-> Idx 0)
       $ lE "n" (Idx 1)
       $ Idx 1 :@: Idx 4 :@: (Idx 3 :@: Idx 2 :@: Idx 1 :@: Idx 0)
---------------------

test21 = infer0 (lE "a" Ast $ lE "z" (Idx 0) $ Idx 0)
listNatT = nf $ tListFo :@: natT
test22 = (nf <$> infer0 (nilFo :@: natT)) == Just listNatT
test23 = (nf <$> infer0 (consFo :@: natT)) == Just (natT :-> listNatT :-> listNatT)
list12 = consFo :@: natT :@: one :@: (consFo :@: natT :@: two :@: (nilFo :@: natT))
test24 = (nf <$> infer0 list12) == Just listNatT

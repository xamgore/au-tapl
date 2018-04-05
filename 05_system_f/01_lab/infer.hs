type Symb = String

infixl 2 :@:, :@>
infixr 3 :->
infix 1 ||-

data Type = TIdx Int         -- типовой атом как индекс Де Брауна
          | Type :-> Type    -- стрелочный тип
          | ForAll Symb Type -- полиморфный тип, Symb - справочное имя связываемой переменной
    deriving (Read,Show,Ord)

instance Eq Type where
  TIdx n1     == TIdx n2     = n1 == n2
  (t1 :-> t3) == (t2 :-> t4) = t1 == t2 && t3 == t4
  ForAll _ t1 == ForAll _ t2 = t1 == t2
  _           == _           = False

-- Объявление либо переменная, либо тип
data Decl = VDecl Symb Type --  объявление термовой переменной с ее типом, Symb - справочное имя этой переменной
          | TDecl Symb      --  объявление типовой переменной, Symb - справочное имя этой переменной
    deriving (Read,Show,Ord)

instance Eq Decl where
  VDecl _ t1 == VDecl _ t2 = t1 == t2
  TDecl _    == TDecl _    = True
  _          == _          = False

type Env = [Decl]

data Term = Idx Int
          | Term :@: Term
          | Term :@> Type
          | Lmb Decl Term
    deriving (Read,Show,Eq,Ord)

lV :: Symb -> Type -> Term -> Term
lV v = Lmb . VDecl v

lT :: Symb -> Term -> Term
lT = Lmb . TDecl
------------------------------------

validEnv :: Env -> Bool
validEnv                  [] = True
validEnv ((TDecl _  ):decls) = validEnv decls
validEnv ((VDecl _ t):decls) = (decls ||- t) && (validEnv decls)

(||-) :: Env -> Type -> Bool
e ||- (TIdx i)     | i < length e, (TDecl _) <- (e !! i) = True
e ||- (l :-> r)    = (e ||- l) && (e ||- r)
e ||- (ForAll s t) = (TDecl s : e) ||- t
_ ||- _ = False


shiftT :: Int -> Type -> Type
shiftT val = on 0 where
  on lvl (TIdx i)     = TIdx $ if lvl <= i then i + val else i
  on lvl (tl :-> tr)  = on lvl tl :-> on lvl tr
  on lvl (ForAll s t) = ForAll s $ on (succ lvl) t

-- выполняет подстановку в целевой тип tau типа sigma
-- вместо свободной в tau переменной типа, связанной
-- с j-м связывателем во внешнем для tau контексте.
substTT :: Int -> Type -> Type -> Type
substTT j sigma tau@(TIdx i) = if i == j then sigma else tau
substTT j sigma (tl :-> tr)  = substTT j sigma tl :-> substTT j sigma tr
substTT j sigma (ForAll s t) = ForAll s $ substTT (succ j) (shiftT 1 sigma) t


infer :: Env -> Term -> Maybe Type
infer e (Idx i)
  | 0 <= i && i < length e
  , (VDecl _ sigma) <- e !! i
  , validEnv e = Just $ shiftT (i + 1) sigma

infer e (t1 :@: t2)
  | Just (sigma1 :-> tau) <- infer e t1
  , Just sigma2           <- infer e t2
  , sigma1 == sigma2 = Just $ tau

infer e (Lmb var@(VDecl x sigma) t)
  | e ||- sigma, Just tau <- infer (var:e) t
    = Just $ sigma :-> (shiftT (-1) tau)

infer e (t :@> tau)
  | e ||- tau
  , Just (ForAll alpha sigma) <- infer e t
    = Just $ shiftT (-1) $ substTT 0 (shiftT 1 tau) sigma

infer e (Lmb ty@(TDecl alpha) t)
  | Just sigma <- infer (ty:e) t
    = Just $ ForAll alpha sigma

infer _ _ = Nothing

infer0 :: Term -> Maybe Type
infer0 = infer []


-- типовой индекс в типе ссылается на номер объемлющего ForAll
botF = ForAll "a" (TIdx 0)
tArr  = TIdx 0 :-> TIdx 0
topF = ForAll "a" tArr
-- Кодирование самоприменения в System F (примеры из лекции)
sa0 = lV "z" botF $ lT "b" $ Idx 1 :@> (TIdx 0 :-> TIdx 0) :@: (Idx 1 :@> TIdx 0)
sa1 = lV "z" topF $ lT "b" $ Idx 1 :@> (TIdx 0 :-> TIdx 0) :@: (Idx 1 :@> TIdx 0)
sa2 = lV "z" topF $ Idx 0 :@> topF :@: Idx 0

-- Комбинатор $I$ (TIdx 0 в cIFopen ссылается в никуда, нужен контекст)
cIFopen = lV "x" (TIdx 0) $ Idx 0
cIF = lT "a" $ lV "x" (TIdx 0) $ Idx 0

-- Комбинаторы $K$ и $K_\ast$
tK    = TIdx 1 :-> TIdx 0 :-> TIdx 1
tKF = ForAll "a" $ ForAll "b" tK
cKF = lT "a" $ lT "b" $ lV "x" (TIdx 1) $ lV "y" (TIdx 1) $ Idx 1
tKast = TIdx 1 :-> TIdx 0 :-> TIdx 0
tKastF = ForAll "a" $ ForAll "b" tKast
cKastF = lT "a" $ lT "b" $ lV "x" (TIdx 1) $ lV "y" (TIdx 1) $ Idx 0

-- Комбинатор $C$
tFlip = (TIdx 2 :-> TIdx 1 :-> TIdx 0) :-> TIdx 1 :-> TIdx 2 :-> TIdx 0
tFlipF = ForAll "a" $ ForAll "b" $ ForAll "c" $ tFlip
cFlipF = lT "a" $ lT "b" $ lT "c" $ lV "f" (TIdx 2 :-> TIdx 1 :-> TIdx 0) $ lV "y" (TIdx 2) $ lV "x" (TIdx 4) $ Idx 2 :@: Idx 0 :@: Idx 1

-- Кодирование булевых значений в System F
boolT = ForAll "a" $ TIdx 0 :-> TIdx 0 :-> TIdx 0
tru = lT "a" $ lV "t" (TIdx 0) $ lV "f" (TIdx 1) $ Idx 0
fls = lT "a" $ lV "t" (TIdx 0) $ lV "f" (TIdx 1) $ Idx 1

ifThenElse = lT "a" $ lV "v" boolT $ lV "x" (TIdx 1) $ lV "y" (TIdx 2) $ Idx 2 :@> TIdx 3 :@: Idx 1 :@: Idx 0
notF = lV "v" boolT $ lT "a" $ lV "t" (TIdx 0) $ lV "f" (TIdx 1) $ Idx 3 :@> TIdx 2 :@: Idx 0 :@: Idx 1

-- Кодирование натуральных чисел в System F
natT = ForAll "a" $ (TIdx 0 :-> TIdx 0) :-> TIdx 0 :-> TIdx 0
natAbs body = lT "a" $ lV "s" (TIdx 0 :-> TIdx 0) $ lV "z" (TIdx 1) body
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



--
-- e1 = validEnv [VDecl "x" tArr, TDecl "a"]
-- t1 = e1 == True
--
-- e2 = validEnv [TDecl "a", VDecl "x" tArr]
-- t2 = e2 == False
--
-- e3 = [] ||- TIdx 0 :-> TIdx 0
-- t3 = e3 == False
--
-- e4 = [TDecl "a"] ||- TIdx 0 :-> TIdx 0
-- t4 = e4 == True
--
-- e5 = [] ||- ForAll "a" (TIdx 0 :-> TIdx 0)
-- t5 = e5 == True
--
-- e6 = [TDecl "b",TDecl "a"] ||- TIdx 1 :-> TIdx 0
-- t6 = e6 == True
--
-- e7 = [TDecl "a"] ||- ForAll "b" (TIdx 1 :-> TIdx 0)
-- t7 = e7 == True
--
-- e8 = [] ||- ForAll "a" (ForAll "b" (TIdx 1 :-> TIdx 0))
-- t8 = e8 == True
--
-- finaltest = and [t1, t2, t3, t4, t5, t6, t7, t8]

e1 = infer0 sa0
t1 = e1 == Just (ForAll "a" (TIdx 0) :-> ForAll "b" (TIdx 0))
e2 = infer0 sa1
t2 = e2 == Just (ForAll "a" (TIdx 0 :-> TIdx 0) :-> ForAll "b" (TIdx 0 :-> TIdx 0))
e3 = infer0 sa2
t3 = e3 == Just (ForAll "a" (TIdx 0 :-> TIdx 0) :-> ForAll "a" (TIdx 0 :-> TIdx 0))

tests = t1 && t2 && t3

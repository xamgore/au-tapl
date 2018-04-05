import Control.Applicative ((<|>))

type Symb = String

infixl 2 :@:, :@>
infixr 3 :->

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
shiftT = typeOn 0

typeOn lvl val (TIdx i)     = TIdx $ if lvl <= i then i + val else i
typeOn lvl val (tl :-> tr)  = typeOn lvl val tl :-> typeOn lvl val tr
typeOn lvl val (ForAll s t) = ForAll s $ typeOn (succ lvl) val t

-- выполняет подстановку в целевой тип tau типа sigma
-- вместо свободной в tau переменной типа, связанной
-- с j-м связывателем во внешнем для tau контексте.
substTT :: Int -> Type -> Type -> Type
substTT j sigma tau@(TIdx i) = if i == j then sigma else tau
substTT j sigma (tl :-> tr)  = substTT j sigma tl :-> substTT j sigma tr
substTT j sigma (ForAll s t) = ForAll s $ substTT (succ j) (shiftT 1 sigma) t

shiftV :: Int -> Term -> Term
shiftV val = on 0 where
  on lvl (Idx i)      = Idx $ if lvl <= i then i + val else i
  on lvl (tl :@: tr)  = on lvl tl :@: on lvl tr
  on lvl (tl :@> ty)  = on lvl tl :@> typeOn lvl val ty
  on lvl (Lmb d@(TDecl idx) t) = Lmb d $ on (succ lvl) t
  on lvl (Lmb (VDecl x ty) t)  =
    Lmb (VDecl x $ typeOn lvl val ty) (on (succ lvl) t)

-- выполняет подстановку в целевой терм u терма s
-- вместо свободной в u термовой переменной, связанной
-- с j-м связывателем во внешнем для u контексте.
substVV :: Int -> Term -> Term -> Term
substVV j s u@(Idx i)   = if i == j then s else u
substVV j s (t1 :@: t2) = substVV j s t1 :@: substVV j s t2
substVV j s (t1 :@> ty) = substVV j s t1 :@> ty
substVV j s (Lmb dec t) = Lmb dec $ substVV (succ j) (shiftV 1 s) t

-- выполняет подстановку в целевой терм u типа tau
-- вместо свободной в u переменной типа, связанной
-- с i-м связывателем во внешнем для u контексте.
substTV :: Int -> Type -> Term -> Term
substTV _ _   u@(Idx _)            = u
substTV i tau (t1 :@: t2)          = substTV i tau t1 :@: substTV i tau t2
substTV i tau (t1 :@> ty)          = substTV i tau t1 :@> substTT i tau ty
substTV i tau (Lmb (VDecl x ty) t) =
  Lmb (VDecl x $ substTT i tau ty) (substTV (succ i) (shiftT 1 tau) t)
substTV i tau (Lmb decl t) =
  Lmb decl $ substTV (succ i) (shiftT 1 tau) t


oneStep :: Term -> Maybe Term
oneStep (Lmb decl t)              = Lmb decl <$> oneStep t
oneStep (Lmb (VDecl _ _) t :@: s) = Just $ shiftV (-1) $ substVV 0 (shiftV 1 s) t
oneStep (Lmb (TDecl _)   t :@> s) = Just $ shiftV (-1) $ substTV 0 (shiftT 1 s) t
oneStep (tl :@: tr)               = (:@: tr) <$> oneStep tl <|> (tl :@:) <$> oneStep tr
oneStep (tl :@> tr)               = (:@> tr) <$> oneStep tl
oneStep _                         = Nothing


nf :: Term -> Term
nf t
  | Just next <- oneStep t = nf next
  | Nothing   <- oneStep t = t


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



-- Используя разработанную вами библиотеку для работы с System F
-- в стиле Черча, реализуйте следующие функции

isZero, suc, plus, mult, power :: Term
isZero = lV "num" natT $ lT "a" $
  (Idx 1 :@> (TIdx 0 :-> (TIdx 0 :-> TIdx 0))) :@:
    (lV "x" (TIdx 0 :-> (TIdx 0 :-> TIdx 0)) $ fls :@> TIdx 1) :@: (tru :@> TIdx 0)

suc = lV "num" natT $ lT "a" $ lV "s" tArr $ lV "z" (TIdx 1) $
  (Idx 1) :@: ((Idx 3 :@> TIdx 2) :@: Idx 1 :@: Idx 0)

plus = lV "n" natT $ lV "m" natT $ lT "a" $ lV "s" tArr $ lV "z" (TIdx 1) $
  (Idx 4 :@> TIdx 2) :@: (Idx 1) :@: ((Idx 3 :@> TIdx 2) :@: Idx 1 :@: Idx 0)

mult = lV "n" natT $ lV "m" natT $ lT "a" $ lV "s" tArr $
  (Idx 3 :@> TIdx 1) :@: (Idx 2 :@> TIdx 1 :@: Idx 0)

power = lV "n" natT $ lV "m" natT $ lT "a" $ lV "s" tArr $ lV "z" (TIdx 1) $
  ((Idx 3 :@> (TIdx 2 :-> TIdx 2)) :@: (Idx 4 :@> TIdx 2)) :@: (Idx 1) :@: (Idx 0)

pow = power

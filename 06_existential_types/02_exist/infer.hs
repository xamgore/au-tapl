import Control.Applicative ((<|>))

type Symb = String

infixl 2 :@:, :@>
infixr 3 :->

data Type = TIdx Int         -- типовой атом как индекс Де Брауна
          | Type :-> Type    -- стрелочный тип
          | ForAll Symb Type -- полиморфный тип, Symb - справочное имя связываемой переменной
          | Exists Symb Type -- экзистенциальный тип, Symb - справочное имя связываемой переменной
    deriving (Read,Show,Ord)

instance Eq Type where
  TIdx n1     == TIdx n2     = n1 == n2
  (t1 :-> t3) == (t2 :-> t4) = t1 == t2 && t3 == t4
  ForAll _ t1 == ForAll _ t2 = t1 == t2
  Exists _ t1 == Exists _ t2 = t1 == t2
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
          | As (Type,Term) Type       -- упаковка типа-свидетеля и терма в экзистенциальный тип
          | Let (Symb,Symb) Term Term -- распаковка пакета, имена типа и терма в паре - справочные
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
e ||- (TIdx i)     | 0 <= i && i < length e, (TDecl _) <- (e !! i) = True
e ||- (l :-> r)    = (e ||- l) && (e ||- r)
e ||- (ForAll s t) = (TDecl s : e) ||- t
e ||- (Exists s t) = (TDecl s : e) ||- t
_ ||- _ = False


shiftT :: Int -> Type -> Type
shiftT = typeOn 0

typeOn lvl val (TIdx i)     = TIdx $ if lvl <= i then i + val else i
typeOn lvl val (tl :-> tr)  = typeOn lvl val tl :-> typeOn lvl val tr
typeOn lvl val (ForAll s t) = ForAll s $ typeOn (succ lvl) val t
typeOn lvl val (Exists s t) = Exists s $ typeOn (succ lvl) val t

-- выполняет подстановку в целевой тип tau типа sigma
-- вместо свободной в tau переменной типа, связанной
-- с j-м связывателем во внешнем для tau контексте.
substTT :: Int -> Type -> Type -> Type
substTT j sigma tau@(TIdx i) = if i == j then sigma else tau
substTT j sigma (tl :-> tr)  = substTT j sigma tl :-> substTT j sigma tr
substTT j sigma (ForAll s t) = ForAll s $ substTT (succ j) (shiftT 1 sigma) t
substTT j sigma (Exists s t) = Exists s $ substTT (succ j) (shiftT 1 sigma) t


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

infer e (Let (alpha, x) t1 t2)
  | Just (Exists _ sigma) <- infer e t1
  , Just tau <- infer (VDecl x sigma : TDecl alpha : e) t2
  , result <- shiftT (-2) tau
  , e ||- result
    = Just result

infer e (Lmb ty@(TDecl alpha) t)
  | Just sigma <- infer (ty:e) t
    = Just $ ForAll alpha sigma

infer e ((tau, t) `As` ex@(Exists alpha sigma))
  | infer e t == Just (shiftT (-1) $ substTT 0 (shiftT 1 tau) sigma)
    = Just ex

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
fls = lT "a" $ lV "t" (TIdx 0) $ lV "f" (TIdx 1) $ Idx 0
tru = lT "a" $ lV "t" (TIdx 0) $ lV "f" (TIdx 1) $ Idx 1

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

suc = lV "num" natT $ lT "a" $ lV "s" tArr $ lV "z" (TIdx 1) $
  (Idx 1) :@: ((Idx 3 :@> TIdx 2) :@: Idx 1 :@: Idx 0)

plus = lV "n" natT $ lV "m" natT $ lT "a" $ lV "s" tArr $ lV "z" (TIdx 1) $
  (Idx 4 :@> TIdx 2) :@: (Idx 1) :@: ((Idx 3 :@> TIdx 2) :@: Idx 1 :@: Idx 0)

mult = lV "n" natT $ lV "m" natT $ lT "a" $ lV "s" tArr $
  (Idx 3 :@> TIdx 1) :@: (Idx 2 :@> TIdx 1 :@: Idx 0)


-- Пары
pF  = lT "sigma" $ lT "tau" $ lV "x" (TIdx 1) $ lV "y" (TIdx 1) $ lT "a" $ lV "f" (TIdx 4 :-> TIdx 3 :-> TIdx 0) $ Idx 0 :@: Idx 3 :@: Idx 2
pFT = ForAll "sigma" $ ForAll "tau" $ TIdx 1 :-> TIdx 0 :-> (ForAll "a" $ (TIdx 2 :-> TIdx 1 :-> TIdx 0) :-> TIdx 0)
pT = ForAll "a" $ (TIdx 2 :-> TIdx 1 :-> TIdx 0) :-> TIdx 0

fstP = lT "sigma" $ lT "tau" $ lV "p" pT $ Idx 0 :@> TIdx 2 :@: (cKF    :@> TIdx 2 :@> TIdx 1) where
  cKF = lT "a" $ lT "b" $ lV "x" (TIdx 1) $ lV "y" (TIdx 1) $ Idx 1
sndP = lT "sigma" $ lT "tau" $ lV "p" pT $ Idx 0 :@> TIdx 1 :@: (cKastF :@> TIdx 2 :@> TIdx 1) where
  cKastF = lT "a" $ lT "b" $ lV "x" (TIdx 1) $ lV "y" (TIdx 1) $ Idx 0



-- rec

-- xz (x: R) : pair R nat
-- xz x = pair x 0
xz = lT "R" $ lV "x" (TIdx 0) $ pF :@> TIdx 1 :@> natT :@: Idx 0 :@: zero


-- fs (f: sigma -> nat -> sigma) (pair sigma nat) : pair sigma nat
-- fs f p = pair (f (fst p) (snd p))  (succ (snd p))
fs =
  lT "sigma" $
  lV "f" (TIdx 0 :-> natT :-> TIdx 0) $
  lV "p" (ForAll "a" $ (sigma :-> natT :-> TIdx 0) :-> TIdx 0) $
    pair :@: (f :@: (fst :@: p) :@: (snd :@: p)) :@: (suc :@: (snd :@: p))
      where
        (p, f, sigma) = (Idx 0, Idx 1, TIdx 2)
        fst  = fstP :@> sigma :@> natT
        snd  = sndP :@> sigma :@> natT
        pair = pF   :@> sigma :@> natT


-- rec (m : nat) (f : sigma -> nat -> sigma) (x : sigma) : sigma
-- rec m f x = fst (m (fs f) (xz x))
rec =
  lT "sigma" $
  lV "m" natT $
  lV "f" (TIdx 1 :-> natT :-> TIdx 1) $
  lV "x" (TIdx 2) $
    fst :@: (m :@: step :@: start)
      where
        fst   = fstP :@> TIdx 3 :@> natT
        m     = Idx 2 :@> pairT
        step  = fs :@> TIdx 3 :@: Idx 1
        start = xz :@> TIdx 3 :@: Idx 0
        pairT = ForAll "a" $ (TIdx 4 :-> natT :-> TIdx 0) :-> TIdx 0



-- pred

pre = lV "n" natT $ rec :@> natT :@: Idx 0 :@: preFun :@: preIni
preFun = cKastF :@> natT :@> natT
preIni = zero


-- fact

fac = lV "n" natT $ rec :@> natT :@: Idx 0 :@: facFun :@: facIni
facFun = lV "acc" natT $ lV "num" natT $ mult :@: (Idx 1) :@: (suc :@: Idx 0)
facIni = one


-- existential types

tstP = pF :@> natT :@> (natT :-> natT) :@: two :@: (plus :@: three)

tstPT = ForAll "a" $ (natT :-> (natT :-> natT) :-> TIdx 0) :-> TIdx 0

tstPTEx = Exists "b" $ ForAll "a" $ (TIdx 1 :-> (TIdx 1 :-> natT) :-> TIdx 0) :-> TIdx 0

packedP = (natT,tstP) `As` tstPTEx

test = Let ("gamma","p") packedP testBody where
  testBody = snd_ :@: fst_
  fst_ = Idx 0 :@> TIdx 1            :@: (cKF    :@> TIdx 1 :@> (TIdx 1 :-> natT))
  snd_ = Idx 0 :@> (TIdx 1 :-> natT) :@: (cKastF :@> TIdx 1 :@> (TIdx 1 :-> natT))

test1 = Let ("gamma","p") packedP testBody where
  testBody = snd_ :@: seven   -- тип seven - это natT, в snd_ ожидается "gamma"
  snd_ = Idx 0 :@> (TIdx 1 :-> natT) :@: (cKastF :@> TIdx 1 :@> (TIdx 1 :-> natT))

test2 = Let ("gamma","p") packedP testBody where
  testBody = fst_             -- тип "gamma" локален и не может быть доступен извне
  fst_ = Idx 0 :@> TIdx 1            :@: (cKF    :@> TIdx 1 :@> (TIdx 1 :-> natT))

t1 = infer0 test == Just natT
t2 = infer0 test1 == Nothing
t3 = infer0 test2 == Nothing

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
    deriving (Read,Show,Ord)

instance Eq Term where
  Idx n1        == Idx n2        = n1 == n2
  (u1 :@: u3)   == (u2 :@: u4)   = u1 == u2 && u3 == u4
  (u1 :@> t3)   == (u2 :@> t4)   = u1 == u2 && t3 == t4
  Lmb d1 u3     == Lmb d2 u4     = d1 == d2 && u3 == u4
  As (t1,u3) t5 == As (t2,u4) t6 = t1 == t2 && u3 == u4 && t5 == t6
  Let _ u1 u3   == Let _ u2 u4   = u1 == u2 && u3 == u4
  _             == _             = False


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

shiftV :: Int -> Term -> Term
shiftV val = on 0 where
  on lvl (Idx i)      = Idx $ if lvl <= i then i + val else i
  on lvl (tl :@: tr)  = on lvl tl :@: on lvl tr
  on lvl (tl :@> ty)  = on lvl tl :@> typeOn lvl val ty
  on lvl (Lmb d@(TDecl idx) t) = Lmb d $ on (succ lvl) t
  on lvl (Lmb (VDecl x ty) t)  =
    Lmb (VDecl x $ typeOn lvl val ty) (on (succ lvl) t)
  on lvl ((ty, t) `As` sigma) =
    (typeOn lvl val ty, on lvl t) `As` (typeOn lvl val sigma)
  on lvl (Let def t1 t2) = Let def (on lvl t1) (on (lvl + 2) t2)

-- выполняет подстановку в целевой терм u терма s
-- вместо свободной в u термовой переменной, связанной
-- с j-м связывателем во внешнем для u контексте.
substVV :: Int -> Term -> Term -> Term
substVV j s u@(Idx i)   = if i == j then s else u
substVV j s (t1 :@: t2) = substVV j s t1 :@: substVV j s t2
substVV j s (t1 :@> ty) = substVV j s t1 :@> ty
substVV j s (Lmb dec t) = Lmb dec $ substVV (succ j) (shiftV 1 s) t
substVV j s ((ty, t) `As` sigma) = (ty, substVV j s t) `As` sigma
substVV j s (Let def t1 t2) =
  Let def (substVV j s t1) (substVV (j + 2) (shiftV 2 s) t2)

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
substTV i tau ((ty, t) `As` sigma) =
  (substTT i tau ty, substTV i tau t) `As` (substTT i tau sigma)
substTV i tau (Let def t1 t2) =
  Let def (substTV i tau t1) (substTV (i + 2) (shiftT 2 tau) t2)

isNANF :: Term -> Bool
isNANF (Idx _) = True
isNANF (t1 :@: t2) = isNANF t1 && isNF t2
isNANF (t1 :@> t2) = isNANF t1
isNANF _ = False

isNF :: Term -> Bool
isNF (Lmb _ t) = isNF t
isNF ((_, t) `As` _) = isNF t
isNF t = isNANF t


oneStep :: Term -> Maybe Term
oneStep (Lmb decl t)              = Lmb decl <$> oneStep t
oneStep (Lmb (VDecl _ _) t :@: s) = Just $ shiftV (-1) $ substVV 0 (shiftV 1 s) t
oneStep (Lmb (TDecl _)   t :@> s) = Just $ shiftV (-1) $ substTV 0 (shiftT 1 s) t
oneStep (tl :@: tr)               = (:@: tr) <$> oneStep tl <|> (tl :@:) <$> oneStep tr
oneStep (tl :@> tr)               = (:@> tr) <$> oneStep tl
oneStep ((ty, t) `As` sigma)      = (\t' -> (ty, t') `As` sigma) <$> oneStep t
oneStep (Let _ ((ty, t) `As` _) t2) | isNF t
  = Just $ shiftV (-1) $ substTV 0 (shiftT 1 ty) $
    shiftV (-1) $ substVV 0 (shiftV 2 t) $ t2
oneStep (Let def t1 t2)           = (\t' -> Let def t' t2) <$> oneStep t1
oneStep _                         = Nothing


nf :: Term -> Term
nf t
  | Just next <- oneStep t = nf next
  | Nothing   <- oneStep t = t

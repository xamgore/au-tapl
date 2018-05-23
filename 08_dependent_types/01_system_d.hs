type Symb = String

infixl 2 :@:
infixr 3 >-> -- теперь просто функция

data Expr = Idx Int          -- переменная как индекс Де Брауна
          | Ast              -- константа, базовый атом для кайндов
          | Box              -- константа высшего уровня
          | Expr :@: Expr    -- аппликация терма к терму или типа к типу
          | Lmb Decl Expr    -- абстракция терма или типа
          | Pi  Decl Expr    -- расширенный функциональный тип
    deriving (Read,Show,Ord)

instance Eq Expr where
  Idx n1      == Idx n2      = n1 == n2
  Ast         == Ast         = True
  Box         == Box         = True
  (u1 :@: u3) == (u2 :@: u4) = u1 == u2 && u3 == u4
  Lmb d1 u3   == Lmb d2 u4   = d1 == d2 && u3 == u4
  Pi d1 u3    == Pi d2 u4    = d1 == d2 && u3 == u4
  _           == _           = False

data Decl = EDecl Symb Expr --  объявление биндера с типом/кайндом, Symb - справочное имя переменной
    deriving (Read,Show,Ord)

instance Eq Decl where
  EDecl _ t1 == EDecl _ t2 = t1 == t2

type Env = [Decl]

lE, pE :: Symb -> Expr -> Expr -> Expr
lE v = Lmb . EDecl v
pE v = Pi  . EDecl v

(>->) :: Expr -> Expr -> Expr
a >-> b = pE "_" a (shift 1 b)

----------------------

isKind :: Expr -> Bool
isKind e = e `elem` [Ast, Box]

isNF :: Expr -> Bool
isNF (Lmb (EDecl _ ex) body) = isNF ex && isNF body
isNF x = isNANF x

isNANF :: Expr -> Bool
isNANF (Idx _)   = True
isNANF (a :@: b) = isNANF a && isNF b
isNANF (Pi (EDecl _ a) b) = isNF a   && isNF b
isNANF e         = isKind e

isNA :: Expr -> Bool
isNA (Idx _)   = True
isNA (_ :@: _) = True
isNA (Pi _ _)  = True
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
shiftOn lvl val (Lmb (EDecl n expr) term)
  = Lmb (EDecl n $ shiftOn lvl val expr) $ shiftOn (lvl + 1) val term
shiftOn lvl val ((EDecl n t1) `Pi` t2)
  = (EDecl n $ shiftOn lvl val t1) `Pi` (shiftOn (lvl + 1) val t2)

subst :: Int -> Expr -> Expr -> Expr
subst _ _ Ast = Ast
subst _ _ Box = Box
subst j s (Idx k)     = if k == j then s else Idx k
subst j s (t1 :@: t2) = (subst j s t1) :@: (subst j s t2)
subst j s (Lmb (EDecl n expr) term)
  = Lmb (EDecl n $ subst j s expr) $ subst (j + 1) (shift 1 s) term
subst j s (Pi (EDecl n t1) t2)
  = Pi (EDecl n $ subst j s t1) $ subst (j + 1) (shift 1 s) t2

betaHelper :: Expr -> Expr -> Expr
betaHelper ty term = shift (-1) $ subst 0 (shift 1 ty) term


infer :: Env -> Expr -> Maybe Expr
infer env expr = if validEnv env then infer' env expr else Nothing

infer' :: Env -> Expr -> Maybe Expr
infer' _ Ast = Just Box

infer' env (Idx idx)
  | 0 <= idx && idx < length env
  , (EDecl _ expr) <- env !! idx
    = Just $ shift (idx + 1) expr

infer' env (Pi decl@(EDecl x a) b)
  | Just Ast <- infer' env a
  , Just s   <- infer' (decl : env) b
  , isKind s = Just s

infer' env (m :@: n)
  | Just (Pi (EDecl _ a) b) <- nf <$> infer' env m
  , Just a'                 <-        infer' env n
  , nf a == nf a' = Just $ betaHelper n b

infer' env (Lmb d@(EDecl x a) m)
  | Just Ast <- infer' env a
  , Just b   <- infer (d : env) m
    = Just $ Pi d b

infer' _ _ = Nothing


infer0 :: Expr -> Maybe Expr
infer0 = infer []

oneStep :: Expr -> Maybe Expr
oneStep (m :@: n)
  | isNA m,   Just m' <- oneStep m = Just $ m' :@: n
  | isNANF m, Just n' <- oneStep n = Just $ m  :@: n'
oneStep ((EDecl x a) `Pi` b)
  | Just a'         <- oneStep a = Just $ (EDecl x a') `Pi` b
  | isNF a, Just b' <- oneStep b = Just $ (EDecl x a)  `Pi` b'
oneStep (Lmb (EDecl name a) m)
  | Just a'         <- oneStep a = Just $ Lmb (EDecl name a') m
  | isNF a, Just m' <- oneStep m = Just $ Lmb (EDecl name a)  m'
oneStep ((Lmb (EDecl name a) m) :@: n)
  = Just $ betaHelper n m
oneStep _ = Nothing

nf :: Expr -> Expr
nf term | Just term' <- oneStep term = nf term'
        | otherwise                  = term

-- cD = lE "beta" Ast (Idx 0 :-> Idx 0)
-- test1 = infer0 cD
-- test2 = infer [EDecl "alpha" Ast] (lE "x" (cD :@: Idx 0) $ Idx 0) == Just ((cD :@: Idx 0) :-> (cD :@: Idx 0))
-- test3 = (nf <$> infer [EDecl "alpha" Ast] (lE "x" (cD :@: Idx 0) $ Idx 0)) == (nf <$> Just (cD :@: (cD :@: Idx 0)))
-- test4 = infer0 (lE "a" Ast $ lE "z" (Idx 0) $ Idx 0)

gamma  = [EDecl "phi" (Idx 0 >-> Ast),EDecl "alpha" Ast]
gamma0 = EDecl "a" (Idx 1) : gamma
test11 = infer gamma0 (lE "x" (Idx 1 :@: Idx 0) (Idx 0)) == Just (Pi (EDecl "x" (Idx 1 :@: Idx 0)) (Idx 2 :@: Idx 1))
test12 = infer gamma (lE "a" (Idx 1) $ lE "x" (Idx 1 :@: Idx 0) (Idx 0)) == Just (Pi (EDecl "a" (Idx 1)) (Pi (EDecl "x" (Idx 1 :@: Idx 0)) (Idx 2 :@: Idx 1)))

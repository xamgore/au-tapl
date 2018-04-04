import Control.Monad (guard)
import Data.List (sort)


type Symb = String

infixr 3 :->

data Type = TVar Symb      -- типовой атом
          | Type :-> Type  -- стрелочный тип
    deriving (Read,Show,Eq,Ord)

type Ctx = [Type] -- контекст

data TNF = Meta Type | TNF [Type] Int [TNF]
    deriving (Read,Show,Eq,Ord)

uncurry2List :: Type -> (Symb,[Type])
uncurry2List (TVar s)  = (s, [])
uncurry2List (l :-> r) = let (s, rs) = uncurry2List r in (s, l:rs)

uncurry2RevList :: Type -> (Symb,[Type])
uncurry2RevList (TVar s)  = (s, [])
uncurry2RevList (l :-> r) = let (s, rs) = uncurry2RevList r in (s, rs ++ [l])

unMeta :: Ctx -> TNF -> [TNF]
unMeta ctx (Meta t@(_ :-> _)) = do
  let (res, args) = uncurry2RevList t
  (TNF [] idx tails) <- unMeta (args ++ ctx) (Meta $ TVar res)
  return $ TNF args idx tails

unMeta ctx (Meta (TVar a)) = do
  (idx, func)  <- zip [0..] ctx
  let (x, args) = uncurry2List func
  guard $ x == a
  return $ TNF [] idx (map Meta args)

unMeta ctx (TNF abstr idx tails) = do
  let ctx' = abstr ++ ctx
  expandedTail <- sequence $ map (unMeta ctx') tails
  return $ TNF abstr idx expandedTail


isTerm :: TNF -> Bool
isTerm (Meta _)        = False
isTerm (TNF _ _ tails) = all isTerm tails

allTNFGens :: Type -> [[TNF]]
allTNFGens tau = takeWhile (not . null) $ iterate approx [Meta tau] where
  approx set
    | (null set) || (all isTerm set) = []
  approx set
    = concatMap (unMeta []) $ filter (not . isTerm) set

inhabGens :: Type -> [[TNF]]
inhabGens = map (filter isTerm) . allTNFGens

inhabs :: Type -> [TNF]
inhabs = concat . inhabGens


tArr = TVar "a" :-> TVar "a"

tNat = tArr :-> tArr

tBool = TVar "a" :-> TVar "a" :-> TVar "a"

tK = TVar "a" :-> TVar "b" :-> TVar "a"

tKast = TVar "a" :-> TVar "b" :-> TVar "b"

tBiNat = (TVar "a" :-> TVar "a") :-> (TVar "a" :-> TVar "a") :-> TVar "a" :-> TVar "a"

tBiBiNat = (TVar "a" :-> TVar "b") :-> (TVar "b" :-> TVar "a") :-> TVar "a" :-> TVar "a"

tBinTree = (TVar "a" :-> TVar "a" :-> TVar "a") :-> TVar "a" :-> TVar "a"

hw3last1 = ((TVar "a" :-> TVar "b") :-> TVar "a") :-> (TVar "a" :-> TVar "a" :-> TVar "b") :-> TVar "a"

hw3last2 = ((TVar "a" :-> TVar "b") :-> TVar "a") :-> (TVar "a" :-> TVar "a" :-> TVar "b") :-> TVar "b"

tk3 = ((TVar "a" :-> TVar "a") :-> TVar "a") :-> TVar "a"

contFmapT = (TVar "a" :-> TVar "b") :->  ((TVar "a" :-> TVar "c") :-> TVar "d")
               :-> (TVar "b" :-> TVar "c") :-> TVar "d"

selFmapT = (TVar "a" :-> TVar "b") :->  ((TVar "a" :-> TVar "c") :-> TVar "a")
               :-> (TVar "b" :-> TVar "c") :-> TVar "b"

monsterT = (((TVar "a" :-> TVar "a") :-> TVar "a") :-> TVar "a") :-> TVar "a" :-> TVar "a"

fixT = (TVar "a" :-> TVar "a") :-> TVar "a"

peirceT = ((TVar "p" :-> TVar "q") :-> TVar "p") :-> TVar "p"




e1 = allTNFGens $ TVar "a"
t1 = e1 == [[Meta (TVar "a")]]

e2 = sort $ allTNFGens tArr
t2 = e2 == (sort $ [[Meta (TVar "a" :-> TVar "a")],[TNF [TVar "a"] 0 []]])

e3 = allTNFGens tNat !! 0
t3 = e3 == (sort $ [Meta ((TVar "a" :-> TVar "a") :-> (TVar "a" :-> TVar "a"))])

e4 = allTNFGens tNat !! 1
t4 = e4 == (sort $ [TNF [TVar "a",TVar "a" :-> TVar "a"] 1 [Meta (TVar "a")],TNF [TVar "a",TVar "a" :-> TVar "a"] 0 []])

e5 = allTNFGens tNat !! 2
t5 = e5 == (sort $ [TNF [TVar "a",TVar "a" :-> TVar "a"] 1 [TNF [] 1 [Meta (TVar "a")]],TNF [TVar "a",TVar "a" :-> TVar "a"] 1 [TNF [] 0 []]])

e6 = allTNFGens tNat !! 3
t6 = e6 == (sort $ [TNF [TVar "a",TVar "a" :-> TVar "a"] 1 [TNF [] 1 [TNF [] 1 [Meta (TVar "a")]]],TNF [TVar "a",TVar "a" :-> TVar "a"] 1 [TNF [] 1 [TNF [] 0 []]]])

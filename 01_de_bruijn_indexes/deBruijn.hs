import Control.Applicative ((<|>))
import Data.Maybe (fromJust)
import Control.Monad (join)

infixl 2 :@:

data Term = Idx Int
          | Term :@: Term
          | Lmb Term
          deriving (Eq, Read, Show)


shift :: Int -> Term -> Term
shift val = on 0 where
  on lvl (Idx i)     = Idx $ if lvl <= i then i + val else i
  on lvl (tl :@: tr) = on lvl tl :@: on lvl tr
  on lvl (Lmb term)  = Lmb $ on (lvl + 1) term


substDB :: Int -> Term -> Term -> Term
substDB j s t@(Idx i)   = if i == j then s else t
substDB j s (tl :@: tr) = substDB j s tl :@: substDB j s tr
substDB j s (Lmb body)  = Lmb $ substDB (j + 1) (shift 1 s) body


betaRuleDB :: Term -> Term
betaRuleDB (t@(Lmb _) :@: s) = body
  where (Lmb body) = shift (-1) $ substDB (-1) s t


oneStepDBN :: Term -> Maybe Term
oneStepDBN   (Lmb t)       = Lmb <$> oneStepDBN t
oneStepDBN t@(Lmb _ :@: _) = Just $  betaRuleDB t
oneStepDBN   (tl :@: tr)   = (:@: tr) <$> oneStepDBN tl <|> (tl :@:) <$> oneStepDBN tr
oneStepDBN _               = Nothing


oneStepDBA :: Term -> Maybe Term
oneStepDBA   (Lmb t)              = Lmb <$> oneStepDBA t
oneStepDBA t@(tl@(Lmb _) :@: tr)  = (tl :@:) <$> oneStepDBA tr <|> Just (betaRuleDB t)
oneStepDBA   (tl :@: tr)          = (:@: tr) <$> oneStepDBA tl <|> (tl :@:) <$> oneStepDBA tr
oneStepDBA _                      = Nothing


nfDB :: (Term -> Maybe Term) -> Term -> Term
nfDB f t = fromJust $ last $ takeWhile (/= Nothing) $ iterate (f =<<) (Just t)

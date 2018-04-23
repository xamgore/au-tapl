import Infer hiding (tArr)

topT = topF
botT = botF

{-
Следующие типы объявлены в вызывающем коде:
botT = ForAll "a" (TIdx 0)
topT = ForAll "a" (TIdx 0 :-> TIdx 0)
boolT = ForAll "a" (TIdx 0 :-> TIdx 0 :-> TIdx 0)
Их можно использовать для удобства.
-}

answer31 = lV "f" botT $ Idx 0 :@> (botT :-> botT) :@: Idx 0 :@> (botT :-> botT) :@: Idx 0
answer32 = lV "f" botT $ Idx 0 :@> (botT :-> botT :-> botT) :@: Idx 0 :@: Idx 0

answer33 = lV "f" botT $ Idx 0 :@> (botT :-> topT :-> botT) :@: Idx 0 :@: (Idx 0 :@> topT)
answer34 = lV "f" botT $ lT "beta" $ Idx 1 :@> (TIdx 0 :-> TIdx 0 :-> TIdx 0) :@: (Idx 1 :@> TIdx 0) :@: (Idx 1 :@> TIdx 0)

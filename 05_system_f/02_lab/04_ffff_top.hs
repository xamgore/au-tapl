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

answer41 = lV "f" topT $ Idx 0 :@> topT :@: Idx 0 :@> topT :@: (Idx 0 :@> topT :@: Idx 0)
answer42 = lV "f" topT $ Idx 0 :@> (topT :-> topT) :@: (Idx 0 :@> topT) :@: (Idx 0 :@> topT :@: Idx 0)
answer43 = lV "f" topT $ Idx 0 :@> (topT :-> topT) :@: (Idx 0 :@> topT) :@: (lT "beta" $ Idx 1 :@> (TIdx 0 :-> TIdx 0) :@: (Idx 1 :@> TIdx 0))

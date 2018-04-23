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

tArr  = TIdx 0 :-> TIdx 0

answer11 = lV "f" topT $ Idx 0 :@> topT :@: Idx 0 :@> topT :@: Idx 0
answer12 = lV "f" topT $ Idx 0 :@> (topT :-> topT) :@: (Idx 0 :@> topT) :@: Idx 0
answer13 = lV "f" topT $ lT "a" $ (Idx 1 :@> (tArr :-> tArr)) :@: (Idx 1 :@> tArr) :@: (Idx 1 :@> TIdx 0)

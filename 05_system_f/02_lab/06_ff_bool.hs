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

tArr  = TIdx 0 :-> TIdx 0 :-> TIdx 0

answer61 = lV "f" boolT $ Idx 0 :@> boolT :@: Idx 0
answer62 = lV "f" boolT $ Idx 0 :@> boolT :@: (lT "b" $ Idx 1 :@> TIdx 0)

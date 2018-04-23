import Infer


answer7 = lV "s" (ForAll "a" $ TIdx 0 :-> TIdx 1 :-> TIdx 0) $ lT "a" $ lV "z" (TIdx 0) $ Idx 2 :@> (TIdx 3 :-> TIdx 1) :@: (Idx 2 :@> TIdx 1 :@: Idx 0)

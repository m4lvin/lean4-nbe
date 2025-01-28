/-
data Type = NAT | FUN Type Type

data Term = Var Integer | App Term Term | Lam Type Term
| Zero | Succ Term | Rec Type Term Term Term

mutual begin
data No = Lam Type No | Zero | Succ No | Ne Ne

data Ne = Var Integer | App Ne No | Rec Type No No Ne
mutual end

data D = LamD Type (D -> D) -- semantic function
| ZeroD -- normal 0
| SuccD D -- normal successor
| NeD TERM -- neutral term family

Term families
type TERM = Integer -> Term

reify :: D -> TERM
reify (LamD a f) k
    = Lam a (reify (f (reflect a (freevar (-(k+1))))) (k+1))
reify ZeroD k = Zero
reify (SuccD d) k = Succ (reify d k)
reify (NeD t) k = t k

reflect :: Type -> TERM -> D
reflect (FUN a b) t
    = LamD a (\d -> reflect b (app t (reify d)))
reflect NAT t = NeD t


-/

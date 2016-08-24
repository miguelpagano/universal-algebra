\begin{spec}
Var : Set
Var = String  
  
data Sortsₑ : Sorts where
  ExprN : Sortsₑ

data Funcsₑ : Funcs Sortsₑ where
  valN  : (n : ℕ) → Funcsₑ ([] , ExprN)
  plus  : Funcsₑ ( ExprN ∷ [ ExprN ] , ExprN )
  varN  : (v : Var) → Funcsₑ ([] , ExprN)


Σₑ : Signature
Σₑ = record  { sorts = Sortsₑ
             ; funcs = Funcsₑ
             }
\end{spec}

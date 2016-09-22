\begin{code}
Var : Set
Var = String  
  
data Sortsₑ : Sorts where
  ExprN : Sortsₑ

data Funcsₑ : Funcs Sortsₑ where
  valN  : (n : ℕ) → Funcsₑ ([] , ExprN)
  varN  : (v : Var) → Funcsₑ ([] , ExprN)
  plus  : Funcsₑ ( ExprN ∷ [ ExprN ] , ExprN )

Σₑ : Signature
Σₑ = ⟨ Sortsₑ , Funcsₑ ⟩
\end{code}

module SubDirect where

module SubDirectProduct {ℓ₃ ℓ₄ ℓ₅ ℓ₆ ℓ₇ ℓ₈} {I : Set ℓ₃}
        (A : I → Algebra {ℓ₄} {ℓ₅} Σ)  where
  open import Product
  open IndexedProduct A

  open IsSub
  record isSubDirect (B : Algebra {ℓ₆} {ℓ₇} Σ) : Set (lsuc (ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅ ⊔ ℓ₆ ⊔ ℓ₇ ⊔ ℓ₈)) where
    field
      isSub : IsSub B Πalg ℓ₈
      πSurj : (i : I) → isEpi (π i ↾ subA isSub)

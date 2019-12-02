{-# OPTIONS --without-K --safe #-}
module Examples where
open import Data.Unit
open import Data.Product
open import Data.Fin
open import Data.Vec
open import Pi╱●
import Pi
open import Pi╱D
open import Pi╱DMemSem
open import Extraction

revrev-ext : 𝟙/_ {𝟙/ 𝕋} ↻ ⟷ 𝔹
revrev-ext = Ext∙⟶ (Pi╱●.revrev {Pi.𝔹 # 𝕋})

trace₃ : Vec State' 15
trace₃ = run _ ⟪ revrev-ext ∥ Enum (𝟙/_ {𝟙/_ {𝔹} 𝕋} ↻) [ zero ]⟫

_⊸_ : (A B : ∙𝕌) → ∙𝕌
A ⊸ B = ∙𝟙/ A ∙×ᵤ ❰ B ❱

id⊸ : {A : ∙𝕌} → (A ⊸ A) ∙⟶ ∙𝟙
id⊸ {A} = ∙swap⋆ ∙⊚ ε A

name : {A B : ∙𝕌} → (f : A ∙⟶ B) → ∙𝟙 ∙⟶ (A ⊸ B)
name {A} {B} f = η A ∙⊚ (∙Singᵤ f ∙⊗ ∙id⟷) ∙⊚ ∙swap⋆

coname : {A B : ∙𝕌} → (f : A ∙⟶ B) → (B ⊸ A) ∙⟶ ∙𝟙
coname {A} {B} f = ∙swap⋆ ∙⊚ (∙Singᵤ f ∙⊗ ∙id⟷) ∙⊚ ε B

comp⊸   : (A B C : ∙𝕌) → (A ⊸ B) ∙×ᵤ (B ⊸ C) ∙⟶ (A ⊸ C)
comp⊸ A B C = ∙assocr⋆ ∙⊚
              ∙id⟷ ∙⊗ ∙assocl⋆ ∙⊚
              ∙id⟷ ∙⊗ (ε B ∙⊗ ∙id⟷) ∙⊚
              ∙id⟷ ∙⊗ ∙unite⋆l

app     : (A B : ∙𝕌) → (A ⊸ B) ∙×ᵤ ❰ A ❱ ∙⟶ ❰ B ❱
app A B = ∙swap⋆ ∙⊗ ∙id⟷ ∙⊚
          ∙assocr⋆ ∙⊚ (∙id⟷ ∙⊗ (∙swap⋆ ∙⊚ ε A)) ∙⊚
          ∙unite⋆r

dist×/  : {A B C D : ∙𝕌} →
          (A ⊸ B) ∙×ᵤ (C ⊸ D) ∙⟶ ((A ∙×ᵤ C) ⊸ (B ∙×ᵤ D))
dist×/ {A} {B} {C} {D} = ∙assocr⋆ ∙⊚
                         (∙id⟷ ∙⊗ ∙assocl⋆) ∙⊚
                         ∙id⟷ ∙⊗ (∙swap⋆ ∙⊗ ∙id⟷) ∙⊚
                         (∙id⟷ ∙⊗ ∙assocr⋆) ∙⊚ ∙assocl⋆ ∙⊚
                         c ∙⊗ tensor
  where
  c : (∙𝟙/ A ∙×ᵤ ∙𝟙/ C) ∙⟶ ∙𝟙/ (A ∙×ᵤ C)
  c = ∙uniti⋆l ∙⊚
      (η (A ∙×ᵤ C) ∙⊗ ∙id⟷) ∙⊚
      (∙swap⋆ ∙⊗ ∙id⟷) ∙⊚
      ∙assocr⋆ ∙⊚
      (∙id⟷ ∙⊗ (cotensor ∙⊗ ∙id⟷)) ∙⊚
      (∙id⟷ ∙⊗ (∙swap⋆ ∙⊗ ∙id⟷)) ∙⊚
      (∙id⟷ ∙⊗ ∙assocr⋆) ∙⊚
      (∙id⟷ ∙⊗ (∙id⟷ ∙⊗ ∙assocl⋆)) ∙⊚
      (∙id⟷ ∙⊗ (∙id⟷ ∙⊗ ((ε A ∙⊗ ∙id⟷) ∙⊚ ∙unite⋆l))) ∙⊚
      (∙id⟷ ∙⊗ ε C) ∙⊚
      ∙unite⋆r

trace : {A B C : ∙𝕌} → (f : A ∙×ᵤ C ∙⟶ B ∙×ᵤ C) → A ∙⟶ B
trace {A} {B} {C} f =
  ∙uniti⋆r ∙⊚ (return _ ∙⊗ η C) ∙⊚ ∙assocl⋆ ∙⊚
  (tensor ∙⊗ ∙id⟷) ∙⊚
  (∙Singᵤ f ∙⊗ ∙id⟷) ∙⊚
  (cotensor ∙⊗ ∙id⟷) ∙⊚
  ∙assocr⋆ ∙⊚ (extract _ ∙⊗ ε C) ∙⊚ ∙unite⋆r

traceA : {A₁ A₂ A₃ A₄ : ∙𝕌}
    → (f₁ : A₁ ∙⟶ A₂) → (f₂ : A₂ ∙⟶ A₄)
    → (f₃ : A₃ ∙⟶ A₃) → (f₄ : A₄ ∙⟶ A₁)
    → A₁ ∙⟶ A₁
traceA f₁ f₂ f₃ f₄ = trace f
  where f = (f₁ ∙⊗ (f₂ ∙⊗ (f₃ ∙⊗ f₄))) ∙⊚
            ∙assocl⋆ ∙⊚ ∙swap⋆ ∙⊚ ∙swap⋆ ∙⊗ ∙id⟷ ∙⊚
            ∙assocr⋆ ∙⊚ (∙id⟷ ∙⊗ ∙assocl⋆) ∙⊚
            ∙id⟷ ∙⊗ (∙swap⋆ ∙⊗ ∙id⟷ ∙⊚ ∙assocr⋆)

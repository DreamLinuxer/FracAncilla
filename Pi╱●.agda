{-# OPTIONS --without-K --safe #-}
module Pi╱● where
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Function using (_∘_)
open import Pi

infixr 90 _#_
infixr 70 _∙×ᵤ_
infixr 70 _∙⊗_
infixr 50 _∙⊚_
infix 100 !∙_

Singleton : (A : Set) → (v : A) → Set
Singleton A v = ∃ (λ ● → v ≡ ●)

Recip : (A : Set) → (v : A) → Set
Recip A v = Singleton A v → ⊤

data ∙𝕌 : Set where
  _#_     : (t : 𝕌) → (v : ⟦ t ⟧) → ∙𝕌
  _∙×ᵤ_   : ∙𝕌 → ∙𝕌 → ∙𝕌
  ❰_❱     : ∙𝕌 → ∙𝕌
  ∙𝟙/     : ∙𝕌 → ∙𝕌

∙⟦_⟧ : ∙𝕌 → Σ[ A ∈ Set ] A
∙⟦ t # v ⟧       = ⟦ t ⟧ , v
∙⟦ T₁ ∙×ᵤ T₂ ⟧   = let (t₁ , v₁) = ∙⟦ T₁ ⟧
                       (t₂ , v₂) = ∙⟦ T₂ ⟧
                   in  (t₁ × t₂) , (v₁ , v₂)
∙⟦ ❰ T ❱ ⟧       = let (t , v) = ∙⟦ T ⟧ in Singleton t v , (v , refl)
∙⟦ ∙𝟙/ T ⟧       = let (t , v) = ∙⟦ T ⟧ in Recip t v , λ _ → tt

∙𝟙 : ∙𝕌
∙𝟙 = 𝟙 # tt

data _⧟_ : ∙𝕌 → ∙𝕌 → Set where
  -- lifting from plain Π
  ∙c       :  {t₁ t₂ : 𝕌} {v : ⟦ t₁ ⟧} →
              (c : t₁ ⟷ t₂) → t₁ # v ⧟ t₂ # (eval c v)
  ∙times#  :  {t₁ t₂ : 𝕌} {v₁ : ⟦ t₁ ⟧} {v₂ : ⟦ t₂ ⟧} →
              ((t₁ ×ᵤ t₂) # (v₁ , v₂)) ⧟ ((t₁ # v₁) ∙×ᵤ (t₂ # v₂))
  ∙#times  :  {t₁ t₂ : 𝕌} {v₁ : ⟦ t₁ ⟧} {v₂ : ⟦ t₂ ⟧} →
              ((t₁ # v₁) ∙×ᵤ (t₂ # v₂)) ⧟ ((t₁ ×ᵤ t₂) # (v₁ , v₂))
  ∙id⟷      :  {T : ∙𝕌} → T ⧟ T
  _∙⊚_      :  {T₁ T₂ T₃ : ∙𝕌} → (T₁ ⧟ T₂) → (T₂ ⧟ T₃) → (T₁ ⧟ T₃)
  -- multiplicative structure
  ∙unite⋆l  :  {T : ∙𝕌} → ∙𝟙 ∙×ᵤ T ⧟ T
  ∙uniti⋆l  :  {T : ∙𝕌} → T ⧟ ∙𝟙 ∙×ᵤ T
  ∙unite⋆r  :  {T : ∙𝕌} → T ∙×ᵤ ∙𝟙 ⧟ T
  ∙uniti⋆r  :  {T : ∙𝕌} → T ⧟ T ∙×ᵤ ∙𝟙
  ∙swap⋆    :  {T₁ T₂ : ∙𝕌} → T₁ ∙×ᵤ T₂ ⧟ T₂ ∙×ᵤ T₁
  ∙assocl⋆  :  {T₁ T₂ T₃ : ∙𝕌} →
               T₁ ∙×ᵤ (T₂ ∙×ᵤ T₃) ⧟ (T₁ ∙×ᵤ T₂) ∙×ᵤ T₃
  ∙assocr⋆  :  {T₁ T₂ T₃ : ∙𝕌} →
               (T₁ ∙×ᵤ T₂) ∙×ᵤ T₃ ⧟ T₁ ∙×ᵤ (T₂ ∙×ᵤ T₃)
  _∙⊗_      :  {T₁ T₂ T₃ T₄ : ∙𝕌} → (T₁ ⧟ T₃) → (T₂ ⧟ T₄) →
               (T₁ ∙×ᵤ T₂ ⧟ T₃ ∙×ᵤ T₄)
  -- monad / comonad
  return   : {T : ∙𝕌} → T ⧟ ❰ T ❱
  extract  : {T : ∙𝕌} → ❰ T ❱ ⧟ T
  -- eta/epsilon
  η  :  (T : ∙𝕌) → ∙𝟙 ⧟ ❰ T ❱ ∙×ᵤ ∙𝟙/ T
  ε  :  (T : ∙𝕌) → ❰ T ❱ ∙×ᵤ ∙𝟙/ T ⧟ ∙𝟙

∙Singᵤ : {T₁ T₂ : ∙𝕌} → (T₁ ⧟ T₂) → ❰ T₁ ❱ ⧟ ❰ T₂ ❱
∙Singᵤ {T₁} {T₂} c = extract ∙⊚ c ∙⊚ return

tensor : {T₁ T₂ : ∙𝕌} → ❰ T₁ ❱ ∙×ᵤ ❰ T₂ ❱ ⧟ ❰ T₁ ∙×ᵤ T₂ ❱
tensor {T₁} {T₂} = (extract ∙⊗ extract) ∙⊚ return

cotensor : {T₁ T₂ : ∙𝕌} → ❰ T₁ ∙×ᵤ T₂ ❱ ⧟ ❰ T₁ ❱ ∙×ᵤ ❰ T₂ ❱
cotensor {T₁} {T₂} = extract ∙⊚ (return ∙⊗ return)

join : {T₁ : ∙𝕌} →  ❰ ❰ T₁ ❱ ❱ ⧟ ❰ T₁ ❱
join {T₁} = extract

duplicate : {T₁ : ∙𝕌} → ❰ T₁ ❱ ⧟ ❰ ❰ T₁ ❱ ❱
duplicate {T₁} = return

tensorl : {T₁ T₂ : ∙𝕌} → (❰ T₁ ❱ ∙×ᵤ T₂) ⧟  ❰ (T₁ ∙×ᵤ T₂) ❱
tensorl {T₁} {T₂} = (extract ∙⊗ ∙id⟷) ∙⊚ return

tensorr : {T₁ T₂ : ∙𝕌} → (T₁ ∙×ᵤ ❰ T₂ ❱) ⧟  ❰ (T₁ ∙×ᵤ T₂) ❱
tensorr {T₁} {T₂} = (∙id⟷ ∙⊗ extract) ∙⊚ return

cotensorl : {T₁ T₂ : ∙𝕌} →  ❰ (T₁ ∙×ᵤ T₂) ❱ ⧟ (❰ T₁ ❱ ∙×ᵤ T₂)
cotensorl {T₁} {T₂} = extract ∙⊚ (return ∙⊗ ∙id⟷)

cotensorr : {T₁ T₂ : ∙𝕌} →  ❰ (T₁ ∙×ᵤ T₂) ❱ ⧟ (T₁ ∙×ᵤ ❰ T₂ ❱)
cotensorr {T₁} {T₂} = extract ∙⊚ (∙id⟷ ∙⊗ return)

!∙_ : {A B : ∙𝕌} → A ⧟ B → B ⧟ A
!∙ (∙c {t₁} {t₂} {v} c) = subst (λ x → t₂ # eval c v ⧟ t₁ # x)
                                (ΠisRev c v) (∙c (! c))
!∙ ∙times# = ∙#times
!∙ ∙#times = ∙times#
!∙ ∙id⟷ = ∙id⟷
!∙ (c₁ ∙⊚ c₂) = (!∙ c₂) ∙⊚ (!∙ c₁)
!∙ ∙unite⋆l = ∙uniti⋆l
!∙ ∙uniti⋆l = ∙unite⋆l
!∙ ∙unite⋆r = ∙uniti⋆r
!∙ ∙uniti⋆r = ∙unite⋆r
!∙ ∙swap⋆ = ∙swap⋆
!∙ ∙assocl⋆ = ∙assocr⋆
!∙ ∙assocr⋆ = ∙assocl⋆
!∙ (c₁ ∙⊗ c₂) = (!∙ c₁) ∙⊗ (!∙ c₂)
!∙ return = extract
!∙ extract = return
!∙ η T = ε T
!∙ ε T = η T

∙eval : {T₁ T₂ : ∙𝕌} → (C : T₁ ⧟ T₂)
      → let (t₁ , v₁) = ∙⟦ T₁ ⟧; (t₂ , v₂) = ∙⟦ T₂ ⟧
        in  Σ (t₁ → t₂) (λ f → f v₁ ≡ v₂)
∙eval ∙id⟷ = (λ x → x) , refl
∙eval (∙c c) = eval c , refl
∙eval (C₁ ∙⊚ C₂) with ∙eval C₁ | ∙eval C₂
... | (f , p) | (g , q) = g ∘ f , trans (cong g p) q
∙eval ∙unite⋆l = (λ {(tt , x) → x}) , refl
∙eval ∙uniti⋆l = (λ {x → (tt , x)}) , refl
∙eval ∙unite⋆r = (λ {(x , tt) → x}) , refl
∙eval ∙uniti⋆r = (λ {x → (x , tt)}) , refl
∙eval ∙swap⋆ = (λ {(x , y) → y , x}) , refl
∙eval ∙assocl⋆ = (λ {(x , (y , z)) → ((x , y) , z)}) , refl
∙eval ∙assocr⋆ = (λ {((x , y) , z) → (x , (y , z))}) , refl
∙eval (C₀ ∙⊗ C₁) with ∙eval C₀ | ∙eval C₁
... | (f , p) | (g , q) = (λ {(t₁ , t₂) → f t₁ , g t₂}) , cong₂ _,_ p q
∙eval ∙times# = (λ x → x) , refl
∙eval ∙#times = (λ x → x) , refl
∙eval (return {T}) = (λ _ → proj₂ ∙⟦ T ⟧ , refl) , refl
∙eval extract = (λ {(w , refl) → w}) , refl
∙eval (η T) = (λ tt → (proj₂ ∙⟦ T ⟧ , refl) , λ _ → tt) , refl
∙eval (ε T) = (λ { ((_ , refl) , f) → f (proj₂ ∙⟦ T ⟧ , refl)}) , refl

revrev : {A : ∙𝕌} → ∙𝟙/ (∙𝟙/ A) ⧟ ❰ A ❱
revrev {A} = ∙uniti⋆l ∙⊚
             (η A ∙⊗ ∙id⟷) ∙⊚
             ((∙id⟷ ∙⊗ return) ∙⊗ ∙id⟷) ∙⊚
             ∙assocr⋆ ∙⊚
             ∙id⟷ ∙⊗ ε (∙𝟙/ A) ∙⊚
             ∙unite⋆r

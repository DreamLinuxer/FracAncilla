{-# OPTIONS --without-K --safe #-}
module Pi where
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality

infixr 70 _×ᵤ_
infixr 60 _+ᵤ_
infixr 50 _⊚_
infix 100 !_

data 𝕌 : Set where
  𝟘       : 𝕌
  𝟙       : 𝕌
  _+ᵤ_    : 𝕌 → 𝕌 → 𝕌
  _×ᵤ_    : 𝕌 → 𝕌 → 𝕌

⟦_⟧ : (A : 𝕌) → Set
⟦ 𝟘 ⟧ = ⊥
⟦ 𝟙 ⟧ = ⊤
⟦ t₁ +ᵤ t₂ ⟧ = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ t₁ ×ᵤ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧

data _⟷_ : 𝕌 → 𝕌 → Set where
  unite₊l : {t : 𝕌} → 𝟘 +ᵤ t ⟷ t
  uniti₊l : {t : 𝕌} → t ⟷ 𝟘 +ᵤ t
  unite₊r : {t : 𝕌} → t +ᵤ 𝟘 ⟷ t
  uniti₊r : {t : 𝕌} → t ⟷ t +ᵤ 𝟘
  swap₊   : {t₁ t₂ : 𝕌} → t₁ +ᵤ t₂ ⟷ t₂ +ᵤ t₁
  assocl₊ : {t₁ t₂ t₃ : 𝕌} → t₁ +ᵤ (t₂ +ᵤ t₃) ⟷ (t₁ +ᵤ t₂) +ᵤ t₃
  assocr₊ : {t₁ t₂ t₃ : 𝕌} → (t₁ +ᵤ t₂) +ᵤ t₃ ⟷ t₁ +ᵤ (t₂ +ᵤ t₃)
  unite⋆l : {t : 𝕌} → 𝟙 ×ᵤ t ⟷ t
  uniti⋆l : {t : 𝕌} → t ⟷ 𝟙 ×ᵤ t
  unite⋆r : {t : 𝕌} → t ×ᵤ 𝟙 ⟷ t
  uniti⋆r : {t : 𝕌} → t ⟷ t ×ᵤ 𝟙
  swap⋆   : {t₁ t₂ : 𝕌} → t₁ ×ᵤ t₂ ⟷ t₂ ×ᵤ t₁
  assocl⋆ : {t₁ t₂ t₃ : 𝕌} → t₁ ×ᵤ (t₂ ×ᵤ t₃) ⟷ (t₁ ×ᵤ t₂) ×ᵤ t₃
  assocr⋆ : {t₁ t₂ t₃ : 𝕌} → (t₁ ×ᵤ t₂) ×ᵤ t₃ ⟷ t₁ ×ᵤ (t₂ ×ᵤ t₃)
  absorbr : {t : 𝕌} → 𝟘 ×ᵤ t ⟷ 𝟘
  absorbl : {t : 𝕌} → t ×ᵤ 𝟘 ⟷ 𝟘
  factorzr : {t : 𝕌} → 𝟘 ⟷ t ×ᵤ 𝟘
  factorzl : {t : 𝕌} → 𝟘 ⟷ 𝟘 ×ᵤ t
  dist    : {t₁ t₂ t₃ : 𝕌} → (t₁ +ᵤ t₂) ×ᵤ t₃ ⟷ (t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃)
  factor  : {t₁ t₂ t₃ : 𝕌} → (t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃) ⟷ (t₁ +ᵤ t₂) ×ᵤ t₃
  distl   : {t₁ t₂ t₃ : 𝕌} → t₁ ×ᵤ (t₂ +ᵤ t₃) ⟷ (t₁ ×ᵤ t₂) +ᵤ (t₁ ×ᵤ t₃)
  factorl : {t₁ t₂ t₃ : 𝕌 } → (t₁ ×ᵤ t₂) +ᵤ (t₁ ×ᵤ t₃) ⟷ t₁ ×ᵤ (t₂ +ᵤ t₃)
  id⟷     : {t : 𝕌} → t ⟷ t
  _⊚_     : {t₁ t₂ t₃ : 𝕌} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
  _⊕_     : {t₁ t₂ t₃ t₄ : 𝕌} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (t₁ +ᵤ t₂ ⟷ t₃ +ᵤ t₄)
  _⊗_     : {t₁ t₂ t₃ t₄ : 𝕌} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (t₁ ×ᵤ t₂ ⟷ t₃ ×ᵤ t₄)

eval : {A B : 𝕌} → (A ⟷ B) → ⟦ A ⟧ → ⟦ B ⟧
eval unite₊l (inj₂ v) = v
eval uniti₊l v  = inj₂ v
eval unite₊r (inj₁ v) = v
eval uniti₊r v  = inj₁ v
eval swap₊ (inj₁ v) = inj₂ v
eval swap₊ (inj₂ v) = inj₁ v
eval assocl₊ (inj₁ v) = inj₁ (inj₁ v)
eval assocl₊ (inj₂ (inj₁ v)) = inj₁ (inj₂ v)
eval assocl₊ (inj₂ (inj₂ v)) = inj₂ v
eval assocr₊ (inj₁ (inj₁ v)) = inj₁ v
eval assocr₊ (inj₁ (inj₂ v)) = inj₂ (inj₁ v)
eval assocr₊ (inj₂ v) = inj₂ (inj₂ v)
eval unite⋆l (tt , v) = v
eval uniti⋆l v = (tt , v)
eval unite⋆r (v , tt) = v
eval uniti⋆r v = (v , tt)
eval swap⋆ (v₁ , v₂)          = (v₂ , v₁)
eval assocl⋆ (v₁ , (v₂ , v₃)) = ((v₁ , v₂) , v₃)
eval assocr⋆ ((v₁ , v₂) , v₃) = (v₁ , (v₂ , v₃))
eval absorbl ()
eval absorbr ()
eval factorzl ()
eval factorzr ()
eval dist (inj₁ v₁ , v₃) = inj₁ (v₁ , v₃)
eval dist (inj₂ v₂ , v₃) = inj₂ (v₂ , v₃)
eval factor (inj₁ (v₁ , v₃)) = (inj₁ v₁ , v₃)
eval factor (inj₂ (v₂ , v₃)) = (inj₂ v₂ , v₃)
eval distl (v , inj₁ v₁) = inj₁ (v , v₁)
eval distl (v , inj₂ v₂) = inj₂ (v , v₂)
eval factorl (inj₁ (v , v₁)) = (v , inj₁ v₁)
eval factorl (inj₂ (v , v₂)) = (v , inj₂ v₂)
eval id⟷ v = v
eval (c₁ ⊚ c₂) v = eval c₂ (eval c₁ v)
eval (c₁ ⊕ c₂) (inj₁ v) = inj₁ (eval c₁ v)
eval (c₁ ⊕ c₂) (inj₂ v) = inj₂ (eval c₂ v)
eval (c₁ ⊗ c₂) (v₁ , v₂) = (eval c₁ v₁ , eval c₂ v₂)

!_ : {A B : 𝕌} → A ⟷ B → B ⟷ A
! unite₊l = uniti₊l
! uniti₊l = unite₊l
! unite₊r = uniti₊r
! uniti₊r = unite₊r
! swap₊ = swap₊
! assocl₊ = assocr₊
! assocr₊ = assocl₊
! unite⋆l = uniti⋆l
! uniti⋆l = unite⋆l
! unite⋆r = uniti⋆r
! uniti⋆r = unite⋆r
! swap⋆ = swap⋆
! assocl⋆ = assocr⋆
! assocr⋆ = assocl⋆
! absorbr = factorzl
! absorbl = factorzr
! factorzr = absorbl
! factorzl = absorbr
! dist = factor
! factor = dist
! distl = factorl
! factorl = distl
! id⟷ = id⟷
! (c₁ ⊚ c₂) = (! c₂) ⊚ (! c₁)
! (c₁ ⊕ c₂) = (! c₁) ⊕ (! c₂)
! (c₁ ⊗ c₂) = (! c₁) ⊗ (! c₂)

ΠisRev : ∀ {A B} → (c : A ⟷ B) (a : ⟦ A ⟧) → eval (c ⊚ ! c) a ≡ a
ΠisRev unite₊l (inj₂ y) = refl
ΠisRev uniti₊l a = refl
ΠisRev unite₊r (inj₁ x) = refl
ΠisRev uniti₊r a = refl
ΠisRev swap₊ (inj₁ x) = refl
ΠisRev swap₊ (inj₂ y) = refl
ΠisRev assocl₊ (inj₁ x) = refl
ΠisRev assocl₊ (inj₂ (inj₁ x)) = refl
ΠisRev assocl₊ (inj₂ (inj₂ y)) = refl
ΠisRev assocr₊ (inj₁ (inj₁ x)) = refl
ΠisRev assocr₊ (inj₁ (inj₂ y)) = refl
ΠisRev assocr₊ (inj₂ y) = refl
ΠisRev unite⋆l (tt , y) = refl
ΠisRev uniti⋆l a = refl
ΠisRev unite⋆r (x , tt) = refl
ΠisRev uniti⋆r a = refl
ΠisRev swap⋆ (x , y) = refl
ΠisRev assocl⋆ (x , (y , z)) = refl
ΠisRev assocr⋆ ((x , y) , z) = refl
ΠisRev dist (inj₁ x , z) = refl
ΠisRev dist (inj₂ y , z) = refl
ΠisRev factor (inj₁ (x , z)) = refl
ΠisRev factor (inj₂ (y , z)) = refl
ΠisRev distl (x , inj₁ y) = refl
ΠisRev distl (x , inj₂ z) = refl
ΠisRev factorl (inj₁ (x , y)) = refl
ΠisRev factorl (inj₂ (x , z)) = refl
ΠisRev id⟷ a = refl
ΠisRev (c₁ ⊚ c₂) a rewrite ΠisRev c₂ (eval c₁ a) = ΠisRev c₁ a
ΠisRev (c₁ ⊕ c₂) (inj₁ x) rewrite ΠisRev c₁ x = refl
ΠisRev (c₁ ⊕ c₂) (inj₂ y) rewrite ΠisRev c₂ y = refl
ΠisRev (c₁ ⊗ c₂) (x , y) rewrite ΠisRev c₁ x | ΠisRev c₂ y = refl

pattern 𝔽 = inj₁ tt
pattern 𝕋 = inj₂ tt

𝔹 𝔹² 𝔹³ 𝔹⁴ : 𝕌
𝔹 = 𝟙 +ᵤ 𝟙
𝔹²  = 𝔹 ×ᵤ 𝔹
𝔹³  = 𝔹 ×ᵤ 𝔹²
𝔹⁴  = 𝔹 ×ᵤ 𝔹³

ctrl : {A : 𝕌} → (A ⟷ A) → 𝔹 ×ᵤ A ⟷ 𝔹 ×ᵤ A
ctrl c = dist ⊚ (id⟷ ⊕ (id⟷ ⊗ c)) ⊚ factor

NOT : 𝔹 ⟷ 𝔹
NOT = swap₊

CNOT : 𝔹² ⟷ 𝔹²
CNOT = ctrl NOT

TOFFOLI : 𝔹³ ⟷ 𝔹³
TOFFOLI = ctrl (ctrl NOT)


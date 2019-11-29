{-# OPTIONS --without-K --safe #-}
module Pi╱D_default where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum
open import Data.Product
open import Data.Maybe
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core
open import Relation.Binary
open import Relation.Nullary

infix  99 𝟙/_
infixr 70 _×ᵤ_
infixr 60 _+ᵤ_
infix  40 _⟷_
infixr 50 _⊚_

data ◯ : Set where
  ↻ : ◯

data 𝕌 : Set where
  𝟘     : 𝕌
  𝟙     : 𝕌
  _+ᵤ_  : 𝕌 → 𝕌 → 𝕌
  _×ᵤ_  : 𝕌 → 𝕌 → 𝕌
  𝟙/_   : 𝕌 → 𝕌

⟦_⟧ : 𝕌 → Set
⟦ 𝟘 ⟧ = ⊥
⟦ 𝟙 ⟧ = ⊤
⟦ t₁ +ᵤ t₂ ⟧ = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ t₁ ×ᵤ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧
⟦ 𝟙/ t ⟧ = ◯

_≠𝟘 : 𝕌 → Set
𝟘 ≠𝟘 = ⊥
𝟙 ≠𝟘 = ⊤
(t₁ +ᵤ t₂) ≠𝟘 = (t₁ ≠𝟘) ⊎ (t₂ ≠𝟘)
(t₁ ×ᵤ t₂) ≠𝟘 = (t₁ ≠𝟘) × (t₂ ≠𝟘)
(𝟙/ t) ≠𝟘 = t ≠𝟘

default : {t : 𝕌} → (t≠𝟘 : t ≠𝟘) → ⟦ t ⟧
default {𝟙} t≠𝟘 = tt
default {t₁ +ᵤ t₂} (inj₁ t₁≠𝟘) = inj₁ (default t₁≠𝟘)
default {t₁ +ᵤ t₂} (inj₂ t₂≠𝟘) = inj₂ (default t₂≠𝟘)
default {t₁ ×ᵤ t₂} (t₁≠𝟘 , t₂≠𝟘) = default t₁≠𝟘 , default t₂≠𝟘
default {𝟙/ t} t≠𝟘 = ↻

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
  η : {t : 𝕌} (t≠0 : t ≠𝟘) → 𝟙 ⟷ t ×ᵤ 𝟙/ t
  ε : {t : 𝕌} (t≠0 : t ≠𝟘) → t ×ᵤ 𝟙/ t ⟷ 𝟙

_≟ᵤ_ : {t : 𝕌} → Decidable (_≡_ {A = ⟦ t ⟧})
_≟ᵤ_ {𝟙} tt tt = yes refl
_≟ᵤ_ {t₁ +ᵤ t₂} (inj₁ x) (inj₁ y) with x ≟ᵤ y
... | yes refl = yes refl
... | no  x≠y  = no (λ {refl → x≠y refl})
_≟ᵤ_ {t₁ +ᵤ t₂} (inj₁ x) (inj₂ y) = no (λ ())
_≟ᵤ_ {t₁ +ᵤ t₂} (inj₂ x) (inj₁ y) = no (λ ())
_≟ᵤ_ {t₁ +ᵤ t₂} (inj₂ x) (inj₂ y) with x ≟ᵤ y
... | yes refl = yes refl
... | no  x≠y  = no (λ {refl → x≠y refl})
_≟ᵤ_ {t₁ ×ᵤ t₂} (x₁ , x₂) (y₁ , y₂) with x₁ ≟ᵤ y₁ | x₂ ≟ᵤ y₂
... | yes refl | yes refl = yes refl
... | yes refl | no x₂≠y₂ = no  (x₂≠y₂ ∘ cong proj₂)
... | no x₁≠y₁ | yes refl = no (x₁≠y₁ ∘ cong proj₁)
... | no x₁≠y₁ | no x₂≠y₂ = no (x₁≠y₁ ∘ cong proj₁)
_≟ᵤ_ {𝟙/ t} ↻ ↻ = yes refl

interp : {t₁ t₂ : 𝕌} → (t₁ ⟷ t₂) → ⟦ t₁ ⟧ → Maybe ⟦ t₂ ⟧
interp swap⋆ (v₁ , v₂) = just (v₂ , v₁)
interp unite₊l (inj₁ ())
interp unite₊l (inj₂ v) = just v
interp uniti₊l v = just (inj₂ v)
interp unite₊r (inj₁ v) = just v
interp unite₊r (inj₂ ())
interp uniti₊r v = just (inj₁ v)
interp swap₊ (inj₁ v) = just (inj₂ v)
interp swap₊ (inj₂ v) = just (inj₁ v)
interp assocl₊ (inj₁ v) = just (inj₁ (inj₁ v))
interp assocl₊ (inj₂ (inj₁ v)) = just (inj₁ (inj₂ v))
interp assocl₊ (inj₂ (inj₂ v)) = just (inj₂ v)
interp assocr₊ (inj₁ (inj₁ v)) = just (inj₁ v)
interp assocr₊ (inj₁ (inj₂ v)) = just (inj₂ (inj₁ v))
interp assocr₊ (inj₂ v) = just (inj₂ (inj₂ v))
interp unite⋆l v = just (proj₂ v)
interp uniti⋆l v = just (tt , v)
interp unite⋆r v = just (proj₁ v)
interp uniti⋆r v = just (v , tt)
interp assocl⋆ (v₁ , v₂ , v₃) = just ((v₁ , v₂) , v₃)
interp assocr⋆ ((v₁ , v₂) , v₃) = just (v₁ , v₂ , v₃)
interp absorbr (() , v)
interp absorbl (v , ())
interp factorzr ()
interp factorzl ()
interp dist (inj₁ v₁ , v₃) = just (inj₁ (v₁ , v₃))
interp dist (inj₂ v₂ , v₃) = just (inj₂ (v₂ , v₃))
interp factor (inj₁ (v₁ , v₃)) = just (inj₁ v₁ , v₃)
interp factor (inj₂ (v₂ , v₃)) = just (inj₂ v₂ , v₃)
interp distl (v₁ , inj₁ v₂) = just (inj₁ (v₁ , v₂))
interp distl (v₁ , inj₂ v₃) = just (inj₂ (v₁ , v₃))
interp factorl (inj₁ (v₁ , v₂)) = just (v₁ , inj₁ v₂)
interp factorl (inj₂ (v₁ , v₃)) = just (v₁ , inj₂ v₃)
interp id⟷ v = just v
interp (c₁ ⊕ c₂) (inj₁ v) = interp c₁ v >>= just ∘ inj₁
interp (c₁ ⊕ c₂) (inj₂ v) = interp c₂ v >>= just ∘ inj₂
interp (c₁ ⊗ c₂) (v₁ , v₂) = interp c₁ v₁ >>=
                               (λ v₁' → interp c₂ v₂ >>=
                                  λ v₂' → just (v₁' , v₂'))
interp (c₁ ⊚ c₂) v = interp c₁ v >>= interp c₂
interp (η t≠0) tt = just (default t≠0 , ↻)
interp (ε t≠0) (v' , ○) with v' ≟ᵤ (default t≠0)
... | yes _ = just tt
... | no _ = nothing

𝔹 : 𝕌
𝔹 = 𝟙 +ᵤ 𝟙

pattern 𝔽 = inj₁ tt
pattern 𝕋 = inj₂ tt

CNOT CNOT' : 𝔹 ×ᵤ 𝔹 ⟷ 𝔹 ×ᵤ 𝔹
CNOT = dist ⊚ (id⟷ ⊕ (id⟷ ⊗ swap₊)) ⊚ factor
CNOT' = distl ⊚ (id⟷ ⊕ (swap₊ ⊗ id⟷)) ⊚ factorl

infixr 2  _⟷⟨_⟩_
infix  3  _□

_⟷⟨_⟩_ : (t₁ : 𝕌) {t₂ : 𝕌} {t₃ : 𝕌} →
          (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
_ ⟷⟨ α ⟩ β = α ⊚ β

_□ : (t : 𝕌) → {t : 𝕌} → (t ⟷ t)
_□ t = id⟷

𝔹≠𝟘 : 𝔹 ≠𝟘
𝔹≠𝟘 = inj₁ tt

id' : 𝔹 ⟷ 𝔹
id' = let η' = η 𝔹≠𝟘
          ε' = ε 𝔹≠𝟘
      in 𝔹
      ⟷⟨ uniti⋆r ⟩                        𝔹 ×ᵤ 𝟙
      ⟷⟨ id⟷ ⊗ η' ⟩                       𝔹 ×ᵤ (𝔹 ×ᵤ 𝟙/ 𝔹)
      ⟷⟨ assocl⋆ ⟩                        (𝔹 ×ᵤ 𝔹) ×ᵤ 𝟙/ 𝔹
      ⟷⟨ (CNOT ⊚ CNOT' ⊚ swap⋆) ⊗ id⟷ ⟩   (𝔹 ×ᵤ 𝔹) ×ᵤ 𝟙/ 𝔹
      ⟷⟨ assocr⋆ ⟩                        𝔹 ×ᵤ (𝔹 ×ᵤ 𝟙/ 𝔹)
      ⟷⟨ id⟷ ⊗ ε' ⟩                       𝔹 ×ᵤ 𝟙
      ⟷⟨ unite⋆r ⟩                        𝔹 □

idcheck : (b : ⟦ 𝔹 ⟧) → interp id' b ≡ just b
idcheck 𝔽 = refl
idcheck 𝕋 = refl

rev× : {A B : 𝕌} {A≠0 : A ≠𝟘} {B≠0 : B ≠𝟘} →
       𝟙/ (A ×ᵤ B) ⟷ 𝟙/ A ×ᵤ 𝟙/ B
rev× {A} {B} {A≠0} {B≠0} =
  let η₁ = η A≠0
      η₂ = η B≠0
      ε' = ε (A≠0 , B≠0)
  in  𝟙/ (A ×ᵤ B)
  ⟷⟨ uniti⋆l ⊚ uniti⋆l ⊚ assocl⋆ ⟩
      (𝟙 ×ᵤ 𝟙) ×ᵤ 𝟙/ (A ×ᵤ B)
  ⟷⟨ (η₁ ⊗ η₂) ⊗ id⟷ ⟩
      ((A ×ᵤ 𝟙/ A) ×ᵤ (B ×ᵤ 𝟙/ B)) ×ᵤ 𝟙/ (A ×ᵤ B)
  ⟷⟨ (shuffle ⊗ id⟷) ⊚ assocr⋆ ⟩
      (𝟙/ A ×ᵤ 𝟙/ B) ×ᵤ ((A ×ᵤ B) ×ᵤ 𝟙/ (A ×ᵤ B))
  ⟷⟨ id⟷ ⊗ ε' ⟩
      (𝟙/ A ×ᵤ 𝟙/ B) ×ᵤ 𝟙
  ⟷⟨ unite⋆r ⟩
      𝟙/ A ×ᵤ 𝟙/ B □
  where
    shuffle : {A B C D : 𝕌} → (A ×ᵤ B) ×ᵤ (C ×ᵤ D) ⟷ (B ×ᵤ D) ×ᵤ (A ×ᵤ C)
    shuffle = (swap⋆ ⊗ swap⋆) ⊚ assocr⋆ ⊚ (id⟷ ⊗ (assocl⋆ ⊚ (swap⋆ ⊗ id⟷) ⊚ assocr⋆)) ⊚ assocl⋆

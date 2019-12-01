{-# OPTIONS --without-K --safe #-}
module PiMemSem where
open import Function using (_∘_; _$_)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin hiding (_+_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Vector
open import Pi

∣_∣ : (A : 𝕌) → ℕ
∣ 𝟘 ∣ = 0
∣ 𝟙 ∣ = 1
∣ A₁ +ᵤ A₂ ∣ = ∣ A₁ ∣ + ∣ A₂ ∣
∣ A₁ ×ᵤ A₂ ∣ = ∣ A₁ ∣ * ∣ A₂ ∣

Enum : (A : 𝕌) → Vec ⟦ A ⟧ ∣ A ∣
Enum 𝟘         = []
Enum 𝟙          = tt ∷ []
Enum (A₁ +ᵤ A₂) = map inj₁ (Enum A₁) ++ map inj₂ (Enum A₂)
Enum (A₁ ×ᵤ A₂) = Vec× (Enum A₁) (Enum A₂)

Find : {A : 𝕌} (x : ⟦ A ⟧) → x ∈ Enum A
Find {𝟙} tt = here refl
Find {A₁ +ᵤ A₂} (inj₁ x) = ++⁺ˡ {xs = map inj₁ (Enum A₁)} (∈map inj₁ x (Find x))
Find {A₁ +ᵤ A₂} (inj₂ y) = ++⁺ʳ (map inj₁ (Enum A₁)) (∈map inj₂ y (Find y))
Find {A₁ ×ᵤ A₂} (x , y) = inVec× (Enum A₁) (Enum A₂) x y (Find x) (Find y)

Find' : {A : 𝕌} (x : ⟦ A ⟧) → Fin ∣ A ∣
Find' = index ∘ Find

card= : {t₁ t₂ : 𝕌} (C : t₁ ⟷ t₂) → (∣ t₁ ∣ ≡ ∣ t₂ ∣)
card= unite₊l = refl
card= uniti₊l = refl
card= unite₊r = +-identityʳ _
card= uniti₊r = sym $ +-identityʳ _
card= {t₁ +ᵤ t₂}         swap₊   = +-comm ∣ t₁ ∣ ∣ t₂ ∣
card= {t₁ +ᵤ t₂ +ᵤ t₃}   assocl₊ = sym $ +-assoc ∣ t₁ ∣ _ _
card= {(t₁ +ᵤ t₂) +ᵤ t₃} assocr₊ = +-assoc ∣ t₁ ∣ ∣ t₂ ∣ _
card= {_} {t₂} unite⋆l rewrite +-identityʳ ∣ t₂ ∣ = refl
card= {t₁} {_} uniti⋆l rewrite +-identityʳ ∣ t₁ ∣ = refl
card= {_} {t₂} unite⋆r rewrite *-identityʳ ∣ t₂ ∣ = refl
card= {t₁} {_} uniti⋆r rewrite *-identityʳ ∣ t₁ ∣ = refl
card= {t₁ ×ᵤ t₂} {_}         swap⋆   rewrite *-comm ∣ t₁ ∣ ∣ t₂ ∣ = refl
card= {t₁ ×ᵤ t₂ ×ᵤ t₃} {_}   assocl⋆ rewrite *-assoc ∣ t₁ ∣ ∣ t₂ ∣ (∣ t₃ ∣) = refl
card= {(t₁ ×ᵤ t₂) ×ᵤ t₃} {_} assocr⋆ rewrite *-assoc ∣ t₁ ∣ ∣ t₂ ∣ (∣ t₃ ∣) = refl
card= absorbr = refl
card= {t ×ᵤ 𝟘} {_} absorbl  rewrite *-zeroʳ ∣ t ∣ = refl
card= {_} {t ×ᵤ 𝟘} factorzr rewrite *-zeroʳ ∣ t ∣ = refl
card= factorzl = refl
card= {(t₁ +ᵤ t₂) ×ᵤ t₃} {_} dist    rewrite *-distribʳ-+ ∣ t₃ ∣ ∣ t₁ ∣ (∣ t₂ ∣) = refl
card= {_} {(t₁ +ᵤ t₂) ×ᵤ t₃} factor  rewrite *-distribʳ-+ ∣ t₃ ∣ ∣ t₁ ∣ (∣ t₂ ∣) = refl
card= {t₃ ×ᵤ (t₁ +ᵤ t₂)} {_} distl   rewrite *-distribˡ-+ ∣ t₃ ∣ ∣ t₁ ∣ (∣ t₂ ∣) = refl
card= {_} {t₃ ×ᵤ (t₁ +ᵤ t₂)} factorl rewrite *-distribˡ-+ ∣ t₃ ∣ ∣ t₁ ∣ (∣ t₂ ∣) = refl
card= id⟷ = refl
card= (c₁ ⊚ c₂) = trans (card= c₁) (card= c₂)
card= (c₁ ⊕ c₂) = cong₂ _+_ (card= c₁) (card= c₂)
card= (c₁ ⊗ c₂) = cong₂ _*_ (card= c₁) (card= c₂)

data State (A : 𝕌) : Set where
  ⟪_[_]⟫ : Vec ⟦ A ⟧ ∣ A ∣ → Fin ∣ A ∣ → State A

resolve : {A : 𝕌} → State A → ⟦ A ⟧
resolve ⟪ v [ i ]⟫ = lookup v i

st : {A B : 𝕌} → ⟦ A ⟧ → (c : A ⟷ B) → Σ[ C ∈ 𝕌 ] (C ⟷ B × State C)
st (inj₂ y) (unite₊l {t})                   = _ , id⟷ , ⟪ Enum t [ Find' y ]⟫
st a (uniti₊l {t})                          = _ , id⟷ , ⟪ (Enum (𝟘 +ᵤ t)) [ Find' a ]⟫
st (inj₁ x) (unite₊r {t})                   = _ , id⟷ , ⟪ Enum t [ Find' x ]⟫
st a (uniti₊r {t})                          = _ , id⟷ , ⟪ (Enum (t +ᵤ 𝟘)) [ Find' {t +ᵤ 𝟘} (inj₁ a) ]⟫
st (inj₁ x) (swap₊ {t₁} {t₂})               = _ , id⟷ , ⟪ Enum _ [ Find' {t₂ +ᵤ t₁} (inj₂ x) ]⟫
st (inj₂ y) (swap₊ {t₁} {t₂})               = _ , id⟷ , ⟪ Enum _ [ Find' {t₂ +ᵤ t₁} (inj₁ y) ]⟫
st (inj₁ x) (assocl₊ {t₁} {t₂} {t₃})        = _ , id⟷ , ⟪ Enum _ [ Find' {(t₁ +ᵤ t₂) +ᵤ t₃} (inj₁ (inj₁ x)) ]⟫
st (inj₂ (inj₁ x)) (assocl₊ {t₁} {t₂} {t₃}) = _ , id⟷ , ⟪ Enum _ [ Find' {(t₁ +ᵤ t₂) +ᵤ t₃} (inj₁ (inj₂ x)) ]⟫
st (inj₂ (inj₂ y)) (assocl₊ {t₁} {t₂} {t₃}) = _ , id⟷ , ⟪ Enum _ [ Find' {(t₁ +ᵤ t₂) +ᵤ t₃} (inj₂ y) ]⟫
st (inj₁ (inj₁ x)) (assocr₊ {t₁} {t₂} {t₃}) = _ , id⟷ , ⟪ Enum _ [ Find' {t₁ +ᵤ t₂ +ᵤ t₃} (inj₁ x) ]⟫
st (inj₁ (inj₂ y)) (assocr₊ {t₁} {t₂} {t₃}) = _ , id⟷ , ⟪ Enum _ [ Find' {t₁ +ᵤ t₂ +ᵤ t₃} (inj₂ (inj₁ y)) ]⟫
st (inj₂ y) (assocr₊ {t₁} {t₂} {t₃})        = _ , id⟷ , ⟪ Enum _ [ Find' {t₁ +ᵤ t₂ +ᵤ t₃} (inj₂ (inj₂ y)) ]⟫
st (tt , y) unite⋆l                         = _ , id⟷ , ⟪ Enum _ [ Find' y ]⟫
st a uniti⋆l                                = _ , id⟷ , ⟪ Enum _ [ Find' (tt , a) ]⟫
st (x , tt) unite⋆r                         = _ , id⟷ , ⟪ Enum _ [ Find' x ]⟫
st a uniti⋆r                                = _ , id⟷ , ⟪ Enum _ [ Find' (a , tt) ]⟫
st (x , y) swap⋆                            = _ , id⟷ , ⟪ Enum _ [ Find' (y , x) ]⟫
st (x , y , z) assocl⋆                      = _ , id⟷ , ⟪ Enum _ [ Find' ((x , y) , z) ]⟫
st ((x , y) , z) assocr⋆                    = _ , id⟷ , ⟪ Enum _ [ Find' (x , y , z) ]⟫
st (inj₁ x , y) (dist {t₁} {t₂} {t₃})       = _ , id⟷ , ⟪ Enum _ [ Find' {t₁ ×ᵤ t₃ +ᵤ t₂ ×ᵤ t₃} (inj₁ (x , y)) ]⟫
st (inj₂ x , y) (dist {t₁} {t₂} {t₃})       = _ , id⟷ , ⟪ Enum _ [ Find' {t₁ ×ᵤ t₃ +ᵤ t₂ ×ᵤ t₃} (inj₂ (x , y)) ]⟫
st (inj₁ (x , y)) (factor {t₁} {t₂} {t₃})   = _ , id⟷ , ⟪ Enum _ [ Find' {(t₁ +ᵤ t₂) ×ᵤ t₃} (inj₁ x , y) ]⟫
st (inj₂ (y , z)) (factor {t₁} {t₂} {t₃})   = _ , id⟷ , ⟪ Enum _ [ Find' {(t₁ +ᵤ t₂) ×ᵤ t₃} (inj₂ y , z) ]⟫
st (x , inj₁ y) (distl {t₁} {t₂} {t₃})      = _ , id⟷ , ⟪ Enum _ [ Find' {(t₁ ×ᵤ t₂) +ᵤ (t₁ ×ᵤ t₃)} (inj₁ (x , y)) ]⟫
st (x , inj₂ y) (distl {t₁} {t₂} {t₃})      = _ , id⟷ , ⟪ Enum _ [ Find' {(t₁ ×ᵤ t₂) +ᵤ (t₁ ×ᵤ t₃)} (inj₂ (x , y)) ]⟫
st (inj₁ (x , y)) (factorl {t₁} {t₂} {t₃})  = _ , id⟷ , ⟪ Enum _ [ Find' {t₁ ×ᵤ (t₂ +ᵤ t₃)} (x , inj₁ y) ]⟫
st (inj₂ (x , z)) (factorl {t₁} {t₂} {t₃})  = _ , id⟷ , ⟪ Enum _ [ Find' {t₁ ×ᵤ (t₂ +ᵤ t₃)} (x , inj₂ z) ]⟫
st a id⟷                                    = _ , id⟷ , ⟪ Enum _ [ Find' a ]⟫
st a (id⟷ ⊚ c)                              = _ , c , ⟪ Enum _ [ Find' a ]⟫
st a (c₁ ⊚ c₂)                              = let _ , c , st' = st a c₁ in
                                              _ , c ⊚ c₂ , st'
st (inj₁ x) (_⊕_ {t₁} {t₂} {_} {t₄} id⟷ c₂) = _ , id⟷ , ⟪ Enum _ [ Find' {_ +ᵤ t₄} (inj₁ x) ]⟫
st (inj₁ x) (_⊕_ {t₁} {t₂} c₁ c₂)           = let _ , c , st' = st x c₁ in
                                              _ , c ⊕ c₂ , ⟪ Enum _ [ Find' {_ +ᵤ t₂} (inj₁ $ resolve st') ]⟫
st (inj₂ y) (_⊕_ {t₁} {t₂} {t₃} {_} c₁ id⟷) = _ , id⟷ , ⟪ Enum _ [ Find' {t₃ +ᵤ _} (inj₂ y) ]⟫
st (inj₂ y) (_⊕_ {t₁} c₁ c₂)                = let _ , c , st' = st y c₂ in
                                              _ , c₁ ⊕ c , ⟪ Enum _ [ Find' {t₁ +ᵤ _} (inj₂ $ resolve st') ]⟫
st (x , y) (id⟷ ⊗ id⟷)                      = _ , id⟷ , ⟪ Enum _ [ Find' (x , y) ]⟫
st (x , y) (id⟷ ⊗ c₂)                       = let _ , c , st' = st y c₂ in
                                               _ , id⟷ ⊗ c , ⟪ Enum _ [ Find' (x , resolve st') ]⟫
st (x , y) (c₁ ⊗ c₂)                        = let _ , c , st' = st x c₁ in
                                              _ , c ⊗ c₂ , ⟪ Enum _ [ Find' (resolve st' , y) ]⟫

step : {A B : 𝕌} (c : A ⟷ B) → State A → Σ[ C ∈ 𝕌 ] (C ⟷ B × State C)
step c ⟪ v [ i ]⟫ = st (lookup v i) c

data State' : ℕ → Set where
  ⟪_∥_[_]⟫ : {A B : 𝕌} → A ⟷ B → Vec ⟦ A ⟧ ∣ A ∣ → Fin ∣ A ∣ → State' ∣ A ∣

step' : ∀ {n} → State' n → State' n
step' (⟪_∥_[_]⟫ {A} {B} c v i) with step c ⟪ v [ i ]⟫
... | _ , c' , ⟪ v' [ i' ]⟫ rewrite card= (c ⊚ ! c') = ⟪ c' ∥ v' [ i' ]⟫

run : (sz n : ℕ) → (st : State' sz) → Vec (State' sz) (suc n)
run sz 0 st = [ st ]
run sz (suc n) st with run sz n st
... | sts with last sts
... | ⟪_∥_[_]⟫ {A} {B} cx vx ix rewrite +-comm 1 (suc n) = sts ++ [ step' ⟪ cx ∥ vx [ ix ]⟫ ]

trace₁ : Vec (State' ∣ 𝔹 ×ᵤ 𝔹 ∣) 8
trace₁ = run ∣ 𝔹 ×ᵤ 𝔹 ∣ _ ⟪ CNOT ∥ Enum (𝔹 ×ᵤ 𝔹) [ fromℕ 3 ]⟫

{-# OPTIONS --without-K --safe #-}
module Pi╱DMemSem where
open import Relation.Binary.Core
open import Data.Empty
open import Function using (_∘_; _$_)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin hiding (_+_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Vec
open import Data.Vec.Relation.Unary.Any.Properties
open import Data.Vec.Any using (Any; here; there; index)
open import Data.Vec.Membership.Propositional
open import Data.Vec.Membership.Propositional.Properties
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Pi╱D

infix  80 ∣_∣

∣_∣ : (A : 𝕌) → ℕ
∣ 𝟘 ∣         = 0
∣ 𝟙 ∣         = 1
∣ A₁ +ᵤ A₂ ∣  = ∣ A₁ ∣ + ∣ A₂ ∣
∣ A₁ ×ᵤ A₂ ∣  = ∣ A₁ ∣ * ∣ A₂ ∣
∣ 𝟙/ v ∣      = 1

Enum : (A : 𝕌) → Vec ⟦ A ⟧ ∣ A ∣
Enum 𝟘          = []
Enum 𝟙          = tt ∷ []
Enum (A₁ +ᵤ A₂) = map inj₁ (Enum A₁) ++ map inj₂ (Enum A₂)
Enum (A₁ ×ᵤ A₂) = allPairs (Enum A₁) (Enum A₂)
Enum (𝟙/ A)     = ↻ ∷ []

Find : {A : 𝕌} (x : ⟦ A ⟧) → x ∈ Enum A
Find {𝟙} tt = here refl
Find {A₁ +ᵤ A₂} (inj₁ x) = ++⁺ˡ {xs = map inj₁ (Enum A₁)} (∈-map⁺ inj₁ (Find x))
Find {A₁ +ᵤ A₂} (inj₂ y) = ++⁺ʳ (map inj₁ (Enum A₁)) (∈-map⁺ inj₂ (Find y))
Find {A₁ ×ᵤ A₂} (x , y) = ∈-allPairs⁺ (Find x) (Find y)
Find {𝟙/ t} ↻ = here refl

Find' : {A : 𝕌} (x : ⟦ A ⟧) → Fin ∣ A ∣
Find' = index ∘ Find

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
st tt (η {t} v)                           = _ , id⟷ , ⟪ Enum (t ×ᵤ (𝟙/ v)) [ Find' {t ×ᵤ (𝟙/ v)} (v , ↻) ]⟫
st (x , ○) (ε {t} v) with v ≟ᵤ x
st (x , ○) (ε {t} v) | yes _ = _ , id⟷ , ⟪ Enum _ [ Find' tt ]⟫
st (x , ○) (ε {t} v) | no  _ = _ , (ε {t} v) , ⟪ Enum (t ×ᵤ (𝟙/ v)) [ Find' {t ×ᵤ (𝟙/ v)} (x , ○) ]⟫
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

data State' : Set where
  ⟪_∥_[_]⟫ : {A B : 𝕌} → A ⟷ B → Vec ⟦ A ⟧ ∣ A ∣ → Fin ∣ A ∣ → State'

step' : State' → State'
step' ⟪ c ∥ v [ i ]⟫ with step c ⟪ v [ i ]⟫
step' ⟪ c ∥ v [ i ]⟫ | _ , c' , ⟪ v' [ i' ]⟫ = ⟪ c' ∥ v' [ i' ]⟫

run : (n : ℕ) → State' → Vec State' (suc n)
run 0 st = [ st ]
run (suc n) st with run n st
... | sts with last sts
... | ⟪ cx ∥ vx [ ix ]⟫ rewrite +-comm 1 (suc n) = sts ++ [ step' ⟪ cx ∥ vx [ ix ]⟫ ]

trace₂ : Vec State' 34
trace₂ = run _ ⟪ id' ∥ Enum 𝔹 [ fromℕ 1 ]⟫

{-# OPTIONS --without-K --safe #-}
module Vector where
open import Data.Fin
open import Data.Nat
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Vec public
open import Data.Vec.Relation.Unary.Any.Properties public
open import Data.Vec.Any using (Any; here; there; index) public
open import Relation.Binary.PropositionalEquality

_∈_ : ∀ {ℓ} {A : Set ℓ} {n} → (a : A) → Vec A n → Set _
a ∈ A = Any (a ≡_) A

Vec× : ∀ {n m} {A B : Set} → Vec A n → Vec B m → Vec (A × B) (n * m)
Vec× va vb = concat (map (λ a₁ → map (a₁ ,_) vb) va)

∈map : ∀ {ℓ₁ ℓ₂} {n} {A : Set ℓ₁} {B : Set ℓ₂} {v : Vec A n} → (f : A → B) → (a : A)
     → a ∈ v → f a ∈ map f v
∈map f a (here refl) = here refl
∈map f a (there a∈v) = there (∈map f a a∈v)

inVec× : ∀ {n m} {A B : Set} → (va : Vec A n) → (vb : Vec B m)
       → (a : A) (b : B)
       → a ∈ va → b ∈ vb
       → (a , b) ∈ Vec× va vb
inVec× (a ∷ va) vb .a b (here refl) b∈vb = ++⁺ˡ {xs = map (a ,_) vb} (∈map _ _ b∈vb)
inVec× (x ∷ va) vb a b (there a∈va) b∈vb = ++⁺ʳ (map (x ,_) vb) (inVec× va vb a b a∈va b∈vb)


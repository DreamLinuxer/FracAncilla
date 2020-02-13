{-# OPTIONS --without-K --rewriting #-}
module Toffoli where
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Pi hiding (_⟷_)
open import Pi╱●
open import Pi╱D hiding (⟦_⟧ ; 𝔹 ; 𝔹³)
open import Agda.Builtin.Equality.Rewrite
open import Extraction

infixr 20 _&_
infixr 20 _^_

_&_ : ⟦ 𝔹 ⟧ → ⟦ 𝔹 ⟧ → ⟦ 𝔹 ⟧
𝔽 & 𝔽 = 𝔽
𝔽 & 𝕋 = 𝔽
𝕋 & 𝔽 = 𝔽
𝕋 & 𝕋 = 𝕋

_^_ : ⟦ 𝔹 ⟧ → ⟦ 𝔹 ⟧ → ⟦ 𝔹 ⟧
𝔽 ^ 𝔽 = 𝔽
𝔽 ^ 𝕋 = 𝕋
𝕋 ^ 𝔽 = 𝕋
𝕋 ^ 𝕋 = 𝔽

lid^ : ∀ b → 𝔽 ^ b ≡ b
lid^ 𝔽 = refl
lid^ 𝕋 = refl
{-# REWRITE lid^ #-}

rid^ : ∀ b → b ^ 𝔽 ≡ b
rid^ 𝔽 = refl
rid^ 𝕋 = refl
{-# REWRITE rid^ #-}

inv^ : ∀ b → b ^ b ≡ 𝔽
inv^ 𝔽 = refl
inv^ 𝕋 = refl
{-# REWRITE inv^ #-}

∙times#³ : ∀ {t₁ t₂ t₃ v₁ v₂ v₃}
         → ((t₁ ×ᵤ (t₂ ×ᵤ t₃)) # (v₁ , v₂ , v₃)) ⧟ ((t₁ # v₁) ∙×ᵤ (t₂ # v₂) ∙×ᵤ (t₃ # v₃))
∙times#³ = ∙times# ∙⊚ ∙id⟷ ∙⊗ ∙times#

∙#times³ : ∀ {t₁ t₂ t₃ v₁ v₂ v₃}
         → ((t₁ # v₁) ∙×ᵤ (t₂ # v₂) ∙×ᵤ (t₃ # v₃)) ⧟ ((t₁ ×ᵤ (t₂ ×ᵤ t₃)) # (v₁ , v₂ , v₃))
∙#times³ = ∙id⟷ ∙⊗ ∙#times ∙⊚ ∙#times

∙TOFFOLI : ∀ {a b c} → (𝔹 # a ∙×ᵤ 𝔹 # b ∙×ᵤ 𝔹 # c) ⧟ (𝔹 # a ∙×ᵤ 𝔹 # b ∙×ᵤ 𝔹 # ((a & b) ^ c))
∙TOFFOLI = ∙#times³ ∙⊚ TOFFOLI' ∙⊚ ∙times#³
  where
    TOFFOLI' : ∀ {a b c} → (𝔹³ # (a , b , c)) ⧟ (𝔹³ # (a , b , ((a & b) ^ c)))
    TOFFOLI' {𝔽} {𝔽} {c} = ∙c TOFFOLI
    TOFFOLI' {𝔽} {𝕋} {c} = ∙c TOFFOLI
    TOFFOLI' {𝕋} {𝔽} {c} = ∙c TOFFOLI
    TOFFOLI' {𝕋} {𝕋} {𝔽} = ∙c TOFFOLI
    TOFFOLI' {𝕋} {𝕋} {𝕋} = ∙c TOFFOLI

∙TOFFOLI₄ : ∀ {a b c d} → (𝔹 # a ∙×ᵤ 𝔹 # b ∙×ᵤ 𝔹 # c ∙×ᵤ 𝔹 # d) ⧟ (𝔹 # a ∙×ᵤ 𝔹 # b ∙×ᵤ 𝔹 # c ∙×ᵤ 𝔹 # (((a & b) & c) ^ d))
∙TOFFOLI₄ = ∙assocl⋆ ∙⊚ ((∙uniti⋆r ∙⊚ (∙id⟷ ∙⊗ (η (𝔹 # 𝔽) ∙⊚ (extract ∙⊗ ∙id⟷)))) ∙⊗ ∙id⟷) ∙⊚
            ((∙assocl⋆ ∙⊚ ((∙assocr⋆ ∙⊚ ∙TOFFOLI) ∙⊗ ∙id⟷) ∙⊚ shuffle) ∙⊗ ∙id⟷) ∙⊚
            ∙assocr⋆ ∙⊚ (∙id⟷ ∙⊗ ∙TOFFOLI) ∙⊚ ∙assocl⋆ ∙⊚
            ((shuffle ∙⊚ ((∙TOFFOLI ∙⊚ ∙assocl⋆) ∙⊗ ∙id⟷) ∙⊚ ∙assocr⋆) ∙⊗ ∙id⟷) ∙⊚
            (((∙id⟷ ∙⊗ ((return ∙⊗ ∙id⟷) ∙⊚ ε (𝔹 # 𝔽))) ∙⊚ ∙unite⋆r) ∙⊗ ∙id⟷) ∙⊚ ∙assocr⋆
  where
    shuffle : ∀ {A B C D} → (A ∙×ᵤ B ∙×ᵤ C) ∙×ᵤ D ⧟ (A ∙×ᵤ B ∙×ᵤ D) ∙×ᵤ C
    shuffle = ∙assocr⋆ ∙⊚ (∙id⟷ ∙⊗ (∙assocr⋆ ∙⊚ (∙id⟷ ∙⊗ ∙swap⋆))) ∙⊚ (∙id⟷ ∙⊗ ∙assocl⋆) ∙⊚ ∙assocl⋆

TOFFOLI₄ : 𝔹⁴ ⟷ 𝔹⁴
TOFFOLI₄ = Ext⧟ (∙TOFFOLI₄ {𝔽} {𝔽} {𝔽} {𝔽})

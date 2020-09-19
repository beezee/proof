module Lawvere.Limits where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Product using (∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)

record Diagram {M N O : Set} : Set where
  field
    dom : N → M
    cod : N → M
    arrs : ∀ (n : N) → dom n → cod n
open Diagram

data Limit {A : Set} (M N O : Set) {Ob : M → Set} : Set where
  limit : (d : Diagram {M} {N} {O} Ob) →
          (∀ (a : A) → ∀ (n : N) → ∃[ io ](arrs d n (proj₁ io) ≡ proj₂ io ))
          → Limit M N O

cov-action : {M N I O : Set} {Ob : M → (I → O)} → Diagram Ob → Diagram (M → O)
cov-action diagram = ?

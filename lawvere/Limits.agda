module Lawvere.Limits where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Product using (∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)

data Diagram (M N : Set) (dom cod : M → N) (Ob : N → Set): Set where
  diagram : (∀ (m : M) → Ob (dom m) → Ob (cod m)) → Diagram M N dom cod Ob

arrs : {M N : Set} {dom cod : M → N} {Ob : N → Set} → Diagram M N dom cod Ob → ∀ (m : M) → Ob (dom m) → Ob (cod m)
arrs (diagram x) = x

open Diagram

data Limit {A : Set} {M : Set} {N : Set} {dom cod : M → N} {Ob : N → Set} : Set where
  limit : (d : Diagram M N dom cod Ob) →
          (∀ (a : A) → ∀ (m : M) → ∃[ io ](arrs d m (proj₁ io) ≡ proj₂ io ))
          → Limit

data Inj {A : Set} {M : Set} {N : Set} {dom cod : M → N} {Ob : N → Set}
         (d : Diagram M N dom cod Ob) (m : M) : Set where
  inj : (inl : Ob (dom m) → A) → (inr : Ob (cod m) → A) →
        (∀ (o : Ob (dom m)) → inl o ≡ inr (arrs d m o)) →
        Inj d m

data Colimit {A : Set} {M : Set} {N : Set} {dom cod : M → N} {Ob : N → Set} : Set where
  colimit : (d : Diagram M N dom cod Ob) → (∀ (m : M) → Inj {A} d m) → Colimit

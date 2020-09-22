module Lawvere.SetsForMath where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Product using (∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)

data Uniq {T E A : Set} (i : E → A) (x : T → A) (x′ : T → E) : Set where
  uniq : (x ≡ i ∘ x′) → (∀ (z : T → E) → (x ≡ i ∘ z) → x′ ≡ z) → Uniq i x x′

data ProdUniq {A B C X : Set} (f : X → A) (g : X → B) (π₁ : C → A) (π₂ : C → B) (x : X → C) : Set where
  prod-uniq : Uniq π₁ f x → Uniq π₂ g x → ProdUniq f g π₁ π₂ x

data Prod (A B C : Set) : Set₁ where
  prod : (π₁ : C → A) → (π₂ : C → B) → (∀ (X : Set) → (f : X → A) → (g : X → B) → ∃[ x ](ProdUniq f g π₁ π₂ x)) → Prod A B C

data Equalizer (T E A B : Set) (i : E → A) (f g : A → B) : Set where
  intro : f ∘ i ≡ g ∘ i → (∀ (x : T → A) → ∃[ x′ ]( Uniq i x x′ )) → Equalizer T E A B i f g

data _∈_ {T E A : Set} (x : T → A) (i : E → A) : Set where
  through : ∃[ x′ ](x ≡ i ∘ x′) → x ∈ i

infix 4 _∈_

∈→≡ : ∀ {T E A B} {f g : A → B}
  → (x : T → A)
  → (i : E → A)
  → Equalizer T E A B i f g
  → x ∈ i
  -----------------------------------
  → f ∘ x ≡ g ∘ x
∈→≡ x i (intro ev eql) (through ⟨ x′ , refl ⟩) rewrite cong (λ fix → λ x → fix (x′ x)) ev = refl

≡→∈ : ∀ {T E A B} {f g : A → B}
  → (x : T → A)
  → (i : E → A)
  → Equalizer T E A B i f g
  → f ∘ x ≡ g ∘ x
  -----------------------------------
  → x ∈ i
≡→∈ x i (intro ev eql) ev₁ with (eql x )
... | ⟨ x′ , (uniq refl _) ⟩ = through ⟨ x′ , refl ⟩

data Pullback (P A B C : Set) : Set₁ where
  pullback : (f : A → C) → (g : B → C) → (π₁ : P → A) → (π₂ : P → B) → (g ∘ π₂ ≡ f ∘ π₁)
                → (∀ (X : Set) → (f′ : X → A) → (g′ : X → B) → ∃[ x ]( ProdUniq f′ g′ π₁ π₂ x ))
                → Pullback P A B C

data UniqArr {X A : Set} (f : X → A) : Set where
  uniq-arr : (∀ (g : X → A) → g ≡ f) → UniqArr f

data Terminal (A : Set) : Set₁ where
  terminal : (∀ (X : Set) → (f : X → A) → UniqArr f) → Terminal A

pb-×-terminal→product : {P A B C : Set}
  → Pullback P A B C
  → Terminal C
    -------------------------
  → Prod A B P
pb-×-terminal→product (pullback f g π₁ π₂ x x₁) (terminal x₂) =
  prod π₁ π₂ (λ X f₁ g₁ → x₁ X f₁ g₁)

data UniqPO (P A B X : Set) (inj₁ : A → P) (inj₂ : B → P) (x : P → X) (f : A → X) (g : B → X) : Set where
  uniq-po : (x ∘ inj₁ ≡ f) → (x ∘ inj₂ ≡ g) → UniqPO P A B X inj₁ inj₂ x f g

data Pushout (P A B C : Set) (f : C → A) (g : C → B) : Set₁ where
  pushout : (inj₁ : A → P) → (inj₂ : B → P) → (inj₂ ∘ g ≡ inj₁ ∘ f)
                → (∀ (X : Set) → (f′ : A → X) → (g′ : B → X) → ∃[ x ]( UniqPO P A B X inj₁ inj₂ x f′ g′ ))
                → Pushout P A B C f g

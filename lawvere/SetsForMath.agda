module Lawvere.SetsForMath where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Data.Product using (_×_; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)

infix 0 _≃_
record _≃_ (A B : Set₁) : Set₁ where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (a : A) → f a ≡ g a)
      ----------------------
    → f ≡ g

postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀ (x : A) → B x}
    → ∀(x : A) → f x ≡ g x
      ---------------------
    → f ≡ g

data Uniq {T E A : Set} (i : E → A) (x : T → A) (x′ : T → E) : Set where
  uniq : (x ≡ i ∘ x′) → (∀ (z : T → E) → (x ≡ i ∘ z) → x′ ≡ z) → Uniq i x x′

data Prod (A B C : Set) (π₁ : C → A) (π₂ : C → B) : Set₁ where
  prod : (∀ (X : Set) → (f : X → A) → (g : X → B) → ∃[ x ](Uniq π₁ f x × Uniq π₂ g x)) → Prod A B C π₁ π₂

irrelevant : ∀ {a} {A : Set a} {x y : A} (p q : x ≡ y) → p ≡ q
irrelevant refl refl = refl

p-uniq : {A B C : Set} → {π₁ : C → A} → {π₂ : C → B}
  → (X : Set)
  → (f : X → A)
  → (g : X → B)
  → (u₁ : ∃[ x ](Uniq π₁ f x × Uniq π₂ g x))
  → (u₂ : ∃[ x ](Uniq π₁ f x × Uniq π₂ g x))
    ----------------------------------------
  → u₁ ≡ u₂
p-uniq {A} {B} {C} {π₁} {π₂} X f g ⟨ fst , ⟨ uniq x x₁ , uniq x₆ x₇ ⟩ ⟩ ⟨ fst₁ , ⟨ uniq x₂ x₃ , uniq x₄ x₅ ⟩ ⟩ with x₁ fst₁ x₂
... | refl with irrelevant x x₂ | irrelevant x₆ x₄
... | refl | refl with ∀-extensionality {X → C} {λ z → (g ≡ π₂ ∘ z → fst ≡ z)} {x₅} {x₇} fst
... | z with z (extensionality λ a → irrelevant (x₅ fst a) (x₇ fst a) )
... | refl with ∀-extensionality {X → C} {λ z → (f ≡ π₁ ∘ z → fst ≡ z)} {x₁} {x₃} fst
... | z₁ with z₁ (extensionality λ a → irrelevant (x₁ fst a) (x₃ fst a) )
... | refl = refl

postulate
  prod-uniq-extensionality : ∀ {A B C : Set} → {π₁ : C → A} → {π₂ : C → B}
    → (x y : ∀ (X : Set) → (f : X → A) → (g : X → B) → ∃[ x ](Uniq π₁ f x × Uniq π₂ g x))
    → (∀ (X : Set) → (f : X → A) → (g : X → B) → (x X f g) ≡ y X f g)
      ----------------------
    → x ≡ y

prod-uniq : {A B C : Set} → {π₁ : C → A} → {π₂ : C → B} → (p₁ : Prod A B C π₁ π₂) → (p₂ : Prod A B C π₁ π₂) → p₁ ≡ p₂
prod-uniq {A} {B} {C} {π₁} {π₂} (prod p₁) (prod p₂) with prod-uniq-extensionality p₁ p₂ λ X f g → p-uniq X f g (p₁ X f g) (p₂ X f g)
... | refl = refl



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

data Pullback (P A B C : Set) (π₁ : P → A) (π₂ : P → B) : Set₁ where
  pullback : (Prod A B P π₁ π₂) → (f : A → C) → (g : B → C) → (g ∘ π₂ ≡ f ∘ π₁)
                → Pullback P A B C π₁ π₂

data UniqArr {X A : Set} (f : X → A) : Set where
  uniq-arr : (∀ (g : X → A) → g ≡ f) → UniqArr f

data Terminal (A : Set) : Set₁ where
  terminal : (∀ (X : Set) → ∃[ f ](UniqArr {X} {A} f)) → Terminal A

terminal→pb→product : {P A B C : Set}
  → Terminal C
  → (π₁ : P → A)
  → (π₂ : P → B)
  → Pullback P A B C π₁ π₂
    -------------------------
  → Prod A B P π₁ π₂
terminal→pb→product _ _ _ (pullback p f g x) = p

terminal→product→pb : {P A B C : Set}
  → Terminal C
  → (π₁ : P → A)
  → (π₂ : P → B)
  → Prod A B P π₁ π₂
    ---------------------------------
  → Pullback P A B C π₁ π₂
terminal→product→pb {P} {A} {B} {C} (terminal ta) π₁ π₂ (prod x) with ta A | ta B | ta P
terminal→product→pb {P} {A} {B} {C} (terminal ta) π₁ π₂ (prod x) | ⟨ f , uniq-arr uniq-f ⟩ | ⟨ g , uniq-arr uniq-g ⟩ | ⟨ p , uniq-arr uniq-p ⟩
  with uniq-p (g ∘ π₂) | uniq-p (f ∘ π₁)
...   | refl | z = pullback (prod x) f g (sym z)

terminal→pb≃product : {P A B C : Set}
  → Terminal C
  → (π₁ : P → A)
  → (π₂ : P → B)
    ---------------------------------
  → Pullback P A B C π₁ π₂ ≃ Prod A B P π₁ π₂
terminal→pb≃product {P} {A} {B} {C} (terminal ta) π₁ π₂ = record {
  to = terminal→pb→product (terminal ta) π₁ π₂ ;
  from = terminal→product→pb (terminal ta) π₁ π₂ ;
  from∘to = fromto ;
  to∘from = tofrom }
  where

  fromto : (pb : Pullback P A B C π₁ π₂) → terminal→product→pb (terminal ta) π₁ π₂ (terminal→pb→product (terminal ta) π₁ π₂ pb) ≡ pb
  fromto (pullback p f g x) with terminal→product→pb (terminal ta) π₁ π₂ p
  fromto (pullback p f g x) | pullback p₁ f₁ g₁ x₃ with ta B | ta A
  fromto (pullback p f g x) | pullback p₁ f₁ g₁ x₃ | ⟨ b , uniq-arr ub ⟩ | ⟨ a , uniq-arr ua ⟩ with ub g₁ | ua f₁ | ub g | ua f
  ... | refl | refl | refl | refl with irrelevant x x₃
  ... | refl with prod-uniq p₁ p
  ... | refl = refl

  tofrom : (prod : Prod A B P π₁ π₂) → terminal→pb→product (terminal ta) π₁ π₂ (terminal→product→pb (terminal ta) π₁ π₂ prod) ≡ prod
  tofrom p with prod-uniq p (terminal→pb→product (terminal ta) π₁ π₂ (terminal→product→pb (terminal ta) π₁ π₂ p))
  ... | z = sym z

data UniqPO (P A B X : Set) (inj₁ : A → P) (inj₂ : B → P) (x : P → X) (f : A → X) (g : B → X) : Set where
  uniq-po : (x ∘ inj₁ ≡ f) → (x ∘ inj₂ ≡ g) → UniqPO P A B X inj₁ inj₂ x f g

data Pushout (P A B C : Set) (f : C → A) (g : C → B) : Set₁ where
  pushout : (inj₁ : A → P) → (inj₂ : B → P) → (inj₂ ∘ g ≡ inj₁ ∘ f)
                → (∀ (X : Set) → (f′ : A → X) → (g′ : B → X) → ∃[ x ]( UniqPO P A B X inj₁ inj₂ x f′ g′ ))
                → Pushout P A B C f g

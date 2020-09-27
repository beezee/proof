module Lawvere.SetsForMath where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
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

data UniqProd {T E A : Set} (i : E → A) (x : T → A) (x′ : T → E) : Set where
  uniq-prod : (x ≡ i ∘ x′) → (∀ (z : T → E) → (x ≡ i ∘ z) → x′ ≡ z) → UniqProd i x x′

data Prod (A B C : Set) (π₁ : C → A) (π₂ : C → B) : Set₁ where
  prod : (∀ (X : Set) → (f : X → A) → (g : X → B) → ∃[ x ](UniqProd π₁ f x × UniqProd π₂ g x)) → Prod A B C π₁ π₂

data UniqCoprod {T E A : Set} (i : E → A) (x : T → A) (x′ : T → E) : Set where
  uniq-coprod : (x ≡ i ∘ x′) → (∀ (z : E → A) → (x ≡ z ∘ x′) → i ≡ z) → UniqCoprod i x x′

data Coprod (A B C : Set) (inj₁ : A → C) (inj₂ : B → C) : Set₁ where
  coprod : (∀ (X : Set) → (f : A → X) → (g : B → X) → ∃[ x ](UniqCoprod x f inj₁  × UniqCoprod x g inj₂)) → Coprod A B C inj₁ inj₂

irrelevant : ∀ {a} {A : Set a} {x y : A} (p q : x ≡ y) → p ≡ q
irrelevant refl refl = refl

p-uniq : {A B C : Set} → {π₁ : C → A} → {π₂ : C → B}
  → (X : Set)
  → (f : X → A)
  → (g : X → B)
  → (u₁ : ∃[ x ](UniqProd π₁ f x × UniqProd π₂ g x))
  → (u₂ : ∃[ x ](UniqProd π₁ f x × UniqProd π₂ g x))
    ----------------------------------------
  → u₁ ≡ u₂
p-uniq {A} {B} {C} {π₁} {π₂} X f g ⟨ fst , ⟨ uniq-prod x x₁ , uniq-prod x₆ x₇ ⟩ ⟩ ⟨ fst₁ , ⟨ uniq-prod x₂ x₃ , uniq-prod x₄ x₅ ⟩ ⟩ with x₁ fst₁ x₂
... | refl with irrelevant x x₂ | irrelevant x₆ x₄
... | refl | refl with ∀-extensionality {X → C} {λ z → (g ≡ π₂ ∘ z → fst ≡ z)} {x₅} {x₇} fst
... | z with z (extensionality λ a → irrelevant (x₅ fst a) (x₇ fst a) )
... | refl with ∀-extensionality {X → C} {λ z → (f ≡ π₁ ∘ z → fst ≡ z)} {x₁} {x₃} fst
... | z₁ with z₁ (extensionality λ a → irrelevant (x₁ fst a) (x₃ fst a) )
... | refl = refl

postulate
  prod-uniq-extensionality : ∀ {A B C : Set} → {π₁ : C → A} → {π₂ : C → B}
    → (x y : ∀ (X : Set) → (f : X → A) → (g : X → B) → ∃[ x ](UniqProd π₁ f x × UniqProd π₂ g x))
    → (∀ (X : Set) → (f : X → A) → (g : X → B) → (x X f g) ≡ y X f g)
      ----------------------
    → x ≡ y

prod-uniq : {A B C : Set} → {π₁ : C → A} → {π₂ : C → B} → (p₁ : Prod A B C π₁ π₂) → (p₂ : Prod A B C π₁ π₂) → p₁ ≡ p₂
prod-uniq {A} {B} {C} {π₁} {π₂} (prod p₁) (prod p₂) with prod-uniq-extensionality p₁ p₂ λ X f g → p-uniq X f g (p₁ X f g) (p₂ X f g)
... | refl = refl

cp-uniq : {A B C : Set} → {inj₁ : A → C} → {inj₂ : B → C}
  → (X : Set)
  → (f : A → X)
  → (g : B → X)
  → (u₁ : ∃[ x ](UniqCoprod x f inj₁ × UniqCoprod x g inj₂))
  → (u₂ : ∃[ x ](UniqCoprod x f inj₁ × UniqCoprod x g inj₂))
    -------------------------------------------
  → u₁ ≡ u₂
cp-uniq {A} {B} {C} {inj₁} {inj₂} X f g ⟨ fst , ⟨ uniq-coprod x x₁ , uniq-coprod x₆ x₇ ⟩ ⟩ ⟨ fst₁ , ⟨ uniq-coprod x₂ x₃ , uniq-coprod x₄ x₅ ⟩ ⟩
  with x₁ fst₁ x₂
... | refl with irrelevant x x₂ | irrelevant x₆ x₄
... | refl | refl with ∀-extensionality {C → X} {λ z → (g ≡ z ∘ inj₂ → fst ≡ z)} {x₅} {x₇} fst
... | z with z (extensionality λ a → irrelevant (x₅ fst a) (x₇ fst a) )
... | refl with ∀-extensionality {C → X} {λ z → (f ≡ z ∘ inj₁ → fst ≡ z)} {x₁} {x₃} fst
... | z₁ with z₁ (extensionality λ a → irrelevant (x₁ fst a) (x₃ fst a) )
... | refl = refl

postulate
  coprod-uniq-extensionality : ∀ {A B C : Set} → {inj₁ : A → C} → {inj₂ : B → C}
    → (x y : ∀ (X : Set) → (f : A → X) → (g : B → X) → ∃[ x ](UniqCoprod x f inj₁ × UniqCoprod x g inj₂))
    → (∀ (X : Set) → (f : A → X) → (g : B → X) → (x X f g) ≡ y X f g)
      ----------------------
    → x ≡ y

coprod-uniq : {A B C : Set} → {inj₁ : A → C} → {inj₂ : B → C} → (cp₁ : Coprod A B C inj₁ inj₂) → (cp₂ : Coprod A B C inj₁ inj₂) → cp₁ ≡ cp₂
coprod-uniq {A} {B} {C} {inj₁} {inj₂} (coprod cp₁) (coprod cp₂)
  with coprod-uniq-extensionality cp₁ cp₂ λ X f g → cp-uniq X f g (cp₁ X f g) (cp₂ X f g)
... | refl = refl

data Equalizer (T E A B : Set) (i : E → A) (f g : A → B) : Set where
  intro : f ∘ i ≡ g ∘ i → (∀ (x : T → A) → ∃[ x′ ]( UniqProd i x x′ )) → Equalizer T E A B i f g

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
... | ⟨ x′ , (uniq-prod refl _) ⟩ = through ⟨ x′ , refl ⟩

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
  tofrom p = sym (prod-uniq p (terminal→pb→product (terminal ta) π₁ π₂ (terminal→product→pb (terminal ta) π₁ π₂ p)))

data Initial (A : Set) : Set₁ where
  initial : (∀ (X : Set) → ∃[ f ](UniqArr {A} {X} f)) → Initial A

data Pushout (P A B C : Set) (inj₁ : A → C) (inj₂ : B → C) : Set₁ where
  pushout : (Coprod A B C inj₁ inj₂) → (f : P → A) → (g : P → B) → (inj₂ ∘ g ≡ inj₁ ∘ f)
                → Pushout P A B C inj₁ inj₂

initial→pushout→coprod : {P A B C : Set}
  → Initial P
  → (inj₁ : A → C)
  → (inj₂ : B → C)
  → Pushout P A B C inj₁ inj₂
    -------------------------
  → Coprod A B C inj₁ inj₂
initial→pushout→coprod _ _ _ (pushout p f g x) = p

initial→coprod→pushout : {P A B C : Set}
  → Initial P
  → (inj₁ : A → C)
  → (inj₂ : B → C)
  → Coprod A B C inj₁ inj₂
    ---------------------------------
  → Pushout P A B C inj₁ inj₂
initial→coprod→pushout {P} {A} {B} {C} (initial ia) inj₁ inj₂ cp with ia A | ia B | ia C
... | ⟨ f , f-uniq ⟩ | ⟨ g , g-uniq ⟩ | ⟨ c , uniq-arr c-uniq ⟩ with c-uniq (inj₁ ∘ f)
... | refl with c-uniq (inj₂ ∘ g)
... | x = pushout cp f g x

initial→pushout≃coprod : {P A B C : Set}
  → Initial P
  → (inj₁ : A → C)
  → (inj₂ : B → C)
    ---------------------------------
  → Pushout P A B C inj₁ inj₂ ≃ Coprod A B C inj₁ inj₂
initial→pushout≃coprod {P} {A} {B} {C} (initial ia) inj₁ inj₂ = record {
  to = initial→pushout→coprod (initial ia) inj₁ inj₂ ;
  from = initial→coprod→pushout (initial ia) inj₁ inj₂ ;
  from∘to = fromto ;
  to∘from = tofrom }
  where

  fromto : (po : Pushout P A B C inj₁ inj₂)
    → initial→coprod→pushout (initial ia) inj₁ inj₂ (initial→pushout→coprod (initial ia) inj₁ inj₂ po) ≡ po
  fromto (pushout (coprod cp) f g ev) with initial→coprod→pushout (initial ia) inj₁ inj₂ (coprod cp)
  ... | pushout (coprod cp₂) f₁ g₁ ev₁ with coprod-uniq (coprod cp) (coprod cp₂)
  ... | refl with ia A | ia B
  ... | ⟨ a , uniq-arr uniq-a ⟩ | ⟨ b , uniq-arr uniq-b ⟩ with uniq-a f₁ | uniq-b g₁
  ... | refl | refl with uniq-a f | uniq-b g
  ... | refl | refl with irrelevant ev ev₁
  ... | refl = refl

  tofrom : (cp : Coprod A B C inj₁ inj₂)
    → initial→pushout→coprod (initial ia) inj₁ inj₂ (initial→coprod→pushout (initial ia) inj₁ inj₂ cp) ≡ cp
  tofrom cp = coprod-uniq (initial→pushout→coprod (initial ia) inj₁ inj₂ (initial→coprod→pushout (initial ia) inj₁ inj₂ cp)) cp

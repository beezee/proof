module AddMulSemiring where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (refl; _≡_; sym; trans; cong)
open Eq.≡-Reasoning

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

recℕ : ∀ {C : Set} → C → (ℕ → C → C) → ℕ → C
recℕ z s zero = z
recℕ z s (succ n) = s n (recℕ z s n)

add : ℕ → ℕ → ℕ
add = recℕ {ℕ → ℕ} (λ x → x) (λ n g m → succ (g m))

mul : ℕ → ℕ → ℕ
mul = recℕ {ℕ → ℕ} (λ x → zero) (λ n g m → add m (g m))

2+1 : add (succ (succ zero)) (succ zero) ≡ succ (add (succ zero) (succ zero))
2+1 = refl

indℕ : ∀ (C : ℕ → Set) → C zero → (∀ (n : ℕ) → C n → C (succ n)) → (∀ (n : ℕ) → C n)
indℕ C c₀ cs zero = c₀
indℕ C c₀ cs (succ n) = cs n (indℕ C c₀ cs n)

+-suc : ∀ (m n : ℕ) → add (succ m) n ≡ succ (add m n)
+-suc m n = refl

addIdSymInd : ∀(n : ℕ) → (add n zero) ≡ (add zero n) → (add (succ n) zero) ≡ add zero (succ n)
addIdSymInd (n) x = begin
      add (succ n) zero
    ≡⟨⟩
      succ (add n zero)
    ≡⟨ cong succ x ⟩
      succ (add zero n)
    ≡⟨⟩
      succ n
    ≡⟨⟩
      add zero (succ n)
    ∎

addIdSym : ∀ (n : ℕ) → add n zero ≡ add zero n
addIdSym = indℕ (λ n → add n zero ≡ add zero n) refl addIdSymInd

incSymZero : ∀ (n : ℕ) → add (succ zero) n ≡ add zero (succ n)
incSymZero n = begin
      add (succ zero) n
    ≡⟨⟩
      succ (add zero n)
    ≡⟨⟩
      succ n
    ≡⟨⟩
      add zero (succ n)
    ∎

incSymInd : ∀ (m n : ℕ) → add (succ n) m ≡ add n (succ m) → add (succ (succ n)) m ≡ add (succ n) (succ m)
incSymInd m n x = begin
      add (succ (succ n)) m
    ≡⟨⟩
      succ (add (succ n) m)
    ≡⟨ cong succ x ⟩
      succ (add n (succ m))
    ≡⟨⟩
      add (succ n) (succ m)
    ∎

incSym : ∀ (m n : ℕ) → add (succ n) m ≡ add n (succ m)
incSym m = indℕ (λ n → add (succ n) m ≡ add n (succ m)) (incSymZero m) (incSymInd m)

addSymInd : ∀(m n : ℕ) → add n m ≡ add m n → add (succ n) m ≡ add m (succ n)
addSymInd m n x = begin
      add (succ n) m
    ≡⟨⟩
      succ (add n m)
    ≡⟨ cong succ x ⟩
      succ (add m n)
    ≡⟨⟩
      add (succ m) n
    ≡⟨ incSym n m ⟩
      add m (succ n)
    ∎

addSym : ∀ (m n : ℕ) → add n m ≡ add m n
addSym m = indℕ (λ n → add n m ≡ add m n) (sym (addIdSym m)) (addSymInd m)

assocAddInd : ∀ (n x y : ℕ) → add n (add x y) ≡ add (add n x) y → add (succ n) (add x y) ≡ add (add (succ n) x) y
assocAddInd n x y eq = begin
      add (succ n) (add x y)
    ≡⟨⟩
      succ (add n (add x y))
    ≡⟨ cong succ eq ⟩
      succ (add (add n x) y)
    ≡⟨⟩
      add (succ (add n x)) y
    ≡⟨⟩
      add (add (succ n) x) y
    ∎

assocAdd : ∀ (x y n : ℕ) → add n (add x y) ≡ add (add n x) y
assocAdd x y = indℕ (λ n → add n (add x y) ≡ add (add n x) y) refl λ n → assocAddInd n x y

mulIdLZero : mul (succ zero) zero ≡ zero
mulIdLZero = refl

mulIdLInd : ∀ (n : ℕ) → mul (succ zero) n ≡ n → mul (succ zero) (succ n) ≡ succ n
mulIdLInd n x = begin
      mul (succ zero) (succ n)
    ≡⟨⟩
      add (succ n) (mul zero n)
    ≡⟨⟩
      succ (add n (mul zero n))
    ≡⟨⟩
      succ (mul (succ zero) n)
    ≡⟨ cong succ x ⟩
      succ n
    ∎

mulIdL : ∀ (n : ℕ) → mul (succ zero) n ≡ n
mulIdL = indℕ (λ n → mul (succ zero) n ≡ n) mulIdLZero mulIdLInd

mulAddZero : ∀ (x y : ℕ) → add (mul zero x) (mul y x) ≡ mul (add zero y) x
mulAddZero x y = begin
      add (mul zero x) (mul y x)
    ≡⟨⟩
      add zero (mul y x)
    ≡⟨⟩
      mul y x
    ≡⟨⟩
      mul (add zero y) x
    ∎

mulAddInd : ∀ (x y n : ℕ) → add (mul n y) (mul x y) ≡ mul (add n x) y → add (mul (succ n) y) (mul x y) ≡ mul (add (succ n) x) y
mulAddInd x y n eq = begin
      add (mul (succ n) y) (mul x y)
    ≡⟨⟩
      add (add y (mul n y)) (mul x y)
    ≡⟨ sym (assocAdd (mul n y) (mul x y) y) ⟩
      add y (add (mul n y) (mul x y))
    ≡⟨ cong (λ x → add y x) eq ⟩
      add y (mul (add n x) y)
    ≡⟨⟩
      mul (succ (add n x)) y
    ≡⟨⟩
      mul (add (succ n) x) y
    ∎

mulAdd : ∀ (x y n : ℕ) → add (mul n y) (mul x y) ≡ mul (add n x) y
mulAdd x y = indℕ (λ n → add (mul n y) (mul x y) ≡ mul (add n x) y) (mulAddZero y x) (mulAddInd x y)

mulAssocZero : ∀ (x y : ℕ) → mul zero (mul x y) ≡ mul (mul zero x) y
mulAssocZero x y = refl

mulAssocInd : ∀ (x y n : ℕ) → mul n (mul x y) ≡ mul (mul n x) y → mul (succ n) (mul x y) ≡ mul (mul (succ n) x) y
mulAssocInd x y n eq = begin
      mul (succ n) (mul x y)
    ≡⟨⟩
      add (mul x y) (mul n (mul x y))
    ≡⟨ cong (λ z → add (mul x y) z) eq ⟩
      add (mul x y) (mul (mul n x) y)
    ≡⟨ mulAdd (mul n x) y x ⟩
      mul (add x (mul n x)) y
    ≡⟨⟩
      mul (mul (succ n) x) y
    ∎

mulAssoc : ∀ (x y n : ℕ) → mul n (mul x y) ≡ mul (mul n x) y
mulAssoc x y = indℕ (λ n → mul n (mul x y) ≡ mul (mul n x) y) (mulAssocZero x y) (mulAssocInd x y) 

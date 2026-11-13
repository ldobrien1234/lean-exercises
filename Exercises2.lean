import Mathlib

/-
Exercises from https://leanprover-community.github.io/mathematics_in_lean/C02_Basics.html
section 2
-/


-- Calculating
example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a b c]
  rw [h]
  rw [<-mul_assoc a e f]

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp]
  rw [hyp']
  rw [mul_comm]
  ring

--structured way of writing calculations, and seeing simplifications
example (a b : ℝ) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]


example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  calc
    (a + b) * (a - b) = a * a + b * a - a * b - b * b := by
      rw[mul_sub, add_mul, add_mul, <-sub_sub]
    _ = a * a + (a * b - a * b ) - b * b := by
      rw [<-add_sub (a * a) (b * a) (a * b), mul_comm b a]
    _ = a^2 + (a * b - a * b) - b^2 := by
      rw [<-pow_two a, <-pow_two b]
    _ = a^2 - b^2 := by
      rw [sub_self (a * b), add_zero]


-- Proofs in algebraic structures ------------------------

namespace MyRing

variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw[add_comm, zero_add]

theorem add_neg_cancel (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

#check MyRing.add_zero
#check add_zero
#check add_left_cancel


theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  rw [<-add_neg_cancel a] at h
  exact (add_left_cancel h).symm


theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  sorry

theorem neg_zero : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_neg (a : R) : - -a = a := by
  sorry

end MyRing


-- Theorems and Lemmas -------------------------

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans
  · apply h₀
  · apply h₁


-- More uses of the tactic apply -------------------


#check min_le_left
#check min_le_right
#check le_min
#check max_le


example (a b : ℝ) : min a b = min b a := by
  apply le_antisymm
  · --  min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · -- min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left


example (a b : ℝ) : max a b = max b a := by
  apply le_antisymm
  · -- max a b ≤ max b a
    apply max_le
    · apply le_max_right
    apply le_max_left
  · -- max b a ≤ max a b
    apply max_le
    · apply le_max_right
    apply le_max_left


example (a b c : ℝ) : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · -- min (min a b) c ≤ min a (min b c)
    apply le_min
    · -- min (min a b) c ≤ a
      have h0: min (min a b) c ≤ min a b := by apply min_le_left
      have h1: min a b ≤ a := by apply min_le_left
      apply le_trans h0
      exact h1
    · -- min (min a b) c ≤ min b c
      have s0: min (min a b) c ≤ b := by
        have s01: min (min a b) c ≤ min a b := by apply min_le_left
        have s02: min a b ≤ b := by apply min_le_right
        apply le_trans s01
        exact s02
      have s1: min (min a b) c ≤ c := by apply min_le_right
      exact le_min s0 s1
  · -- min a (min b c) ≤ min (min a b) c
    apply le_min
    · -- min a (min b c) ≤ min a b
      apply le_min (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    · -- min a (min b c) ≤ c
      apply le_trans (min_le_right _ _) (min_le_right _ _)


theorem aux (a b c : ℝ) : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  · -- min a b + c ≤ a + c
    apply add_le_add_left
    apply min_le_left
  · -- min a b + c ≤ b + c
    apply add_le_add_left
    apply min_le_right


#check add_neg_cancel_right
#check sub_le_iff_le_add


example (a b c : ℝ) : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · apply aux
  · -- min (a + c) (b + c) ≤ min a b + c
    nth_rw 2 [<-add_neg_cancel_right a c]
    nth_rw 2 [<-add_neg_cancel_right b c]
    rw [<-sub_le_iff_le_add]
    rw [sub_eq_add_neg]
    exact aux (a + c) (b + c) (-c)


#check (abs_add_le : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)
#check sub_add_cancel

example (a b : ℝ) : |a| - |b| ≤ |a - b| := by
  rw [sub_le_iff_le_add]
  nth_rw 1 [<-sub_add_cancel a b]
  exact abs_add_le (a-b) b





-- 2.5: Proving facts about algebraic structures -----------------

variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)

#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  · apply le_inf
    · exact inf_le_right
    · exact inf_le_left
  · apply le_inf
    · exact inf_le_right
    · exact inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · apply le_inf
    · have h1 : x ⊓ y ⊓ z ≤ x ⊓ y := by apply inf_le_left
      have h2 : x ⊓ y ≤ x := by apply inf_le_left
      apply le_trans h1 h2
    · apply le_inf
      · have t1 : x ⊓ y ⊓ z ≤ x ⊓ y := by apply inf_le_left
        have t2: x ⊓ y ≤ y := by apply inf_le_right
        apply le_trans t1 t2
      · exact inf_le_right
  · apply le_inf
    · apply le_inf
      · exact inf_le_left
      · have s1 : x ⊓ (y ⊓ z) ≤ y ⊓ z := by apply inf_le_right
        have s2 : y ⊓ z ≤ y := by apply inf_le_left
        apply le_trans s1 s2
    · have q1 : x ⊓ (y ⊓ z) ≤ y ⊓ z := by apply inf_le_right
      have q2 : y ⊓ z ≤ z := by apply inf_le_right
      apply le_trans q1 q2

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  · apply sup_le
    · apply le_sup_right
    · apply le_sup_left
  · apply sup_le
    · apply le_sup_right
    · apply le_sup_left

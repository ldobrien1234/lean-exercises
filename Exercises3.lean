/-
Exercises from https://leanprover-community.github.io/mathematics_in_lean/C02_Basics.html
section 3
-/

import Mathlib

theorem my_lemma : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry

section


variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma a b δ
#check my_lemma a b δ h₀ h₁
#check my_lemma a b δ h₀ h₁ ha hb
#check lt_trans

end

#check mul_le_mul
#check rfl
#check le_antisymm
#check mul_lt_mul_of_pos_right
#check le_of_lt
#check one_mul_eq_id


theorem my_lemma4 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  calc
    |x * y| = |x| * |y| := abs_mul x y
    _ ≤ |x| * ε := mul_le_mul (le_refl |x|) (le_of_lt ylt) (abs_nonneg y) (abs_nonneg x)
    _ < 1 * ε := mul_lt_mul_of_pos_right (lt_of_lt_of_le xlt ele1) (epos)
    _ = ε := one_mul ε


def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x


example (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  apply add_le_add
  apply hfa
  apply hgb


example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  apply add_le_add
  · apply hfa
  · apply hgb



example (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 := by
  intro x
  dsimp
  apply mul_nonneg
  · apply nnf
  · apply nng


example (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x ↦ f x * g x) (a * b) := by
    intro x
    dsimp
    apply mul_le_mul (hfa x) (hgb x) (nng x) (nna)

-- Need to specify f and g because Monotone takes many types of arguments (polymorphic)
-- In contrast, FnLb and FnUb only take functions, so they don't need to be specified
example (f g : ℝ → ℝ) (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x :=
  fun _a _b aleb ↦ add_le_add (mf aleb) (mg aleb)

#check mul_le_mul_of_nonneg_left

example (f : ℝ → ℝ) {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x := by
  intro a b aleb --intro variables and hypothesis
  dsimp
  exact mul_le_mul_of_nonneg_left (mf aleb) nnc

example (f g : ℝ → ℝ) (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) :=
  fun _a _b aleb ↦ mf (mg aleb)


variable {α : Type*} (r s t : Set α)

example : s ⊆ s := by
  intro x xs
  exact xs

theorem Subset.refl : s ⊆ s := fun _x xs ↦ xs

theorem Subset.trans : r ⊆ s → s ⊆ t → r ⊆ t := by
  intro rsubs ssubt x xr
  exact ssubt (rsubs xr )


variable {α : Type*} [PartialOrder α]
variable (s : Set α) (a b : α)

def SetUb (s : Set α) (a : α) :=
  ∀ x, x ∈ s → x ≤ a

example (h : SetUb s a) (h' : a ≤ b) : SetUb s b :=
  fun x xs ↦ le_trans (h x xs) h'


-- Makes things inside function (like a package) available without the prefix
-- e.g. we can write Injective rather than Funciton.Injective
open Function

example (c : ℝ) : Injective fun x ↦ x + c := by
  intro x₁ x₂ h'
  exact (add_left_inj c).mp h'

#check mul_right_inj

example {c : ℝ} (h : c ≠ 0) : Injective fun x ↦ c * x := by
  intro x1 x2 h'
  exact (mul_right_inj' h).mp h'


-- Section 3.2: The existential quantifier ∃ ------------------------
-- Use the "use" tactic

#check norm_num


--proving existential statements-------------------------------------


example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  use 5 / 2
  norm_num


example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  have h1 : 2 < (5 : ℝ) / 2 := by norm_num
  have h2 : (5 : ℝ) / 2 < 3 := by norm_num
  use 5 / 2, h1, h2



--using proofs about existence-------------------------------------
-- Recall the below definitions from a previous declaration
-- def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  -- ∀ x, f x ≤ a

-- def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  -- ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

theorem fnUb_add {f g : ℝ → ℝ} {a b : ℝ} (hfa : FnUb f a) (hgb : FnUb g b) :
    FnUb (fun x ↦ f x + g x) (a + b) :=
  fun x ↦ add_le_add (hfa x) (hgb x)


theorem fnLb_add {f g : ℝ → ℝ} {a b : ℝ} (hfa : FnLb f a) (hgb : FnLb g b) :
    FnLb (fun x ↦ f x + g x) (a + b) :=
  fun x ↦ add_le_add (hfa x) (hgb x)


variable {f g : ℝ → ℝ}


-- Use rcases to "unwrap" existential quantifiers
example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  rcases ubf with ⟨a, ubfa⟩
  rcases ubg with ⟨b, ubgb⟩
  use a + b
  apply fnUb_add ubfa ubgb

example (lbf : FnHasLb f) (lbg : FnHasLb g) : FnHasLb fun x ↦ f x + g x := by
  rcases lbf with ⟨a, lbfa⟩
  rcases lbg with ⟨b, lbgb⟩
  use a + b
  apply fnLb_add lbfa lbgb

#check mul_le_mul_of_nonneg_left

example {c : ℝ} (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb fun x ↦ c * f x := by
  rcases ubf with ⟨a, lbfa⟩ --rcases for "recursive cases"
  use c * a
  intro x
  exact mul_le_mul_of_nonneg_left (lbfa x) h


example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x := by
  rintro ⟨a, ubfa⟩ ⟨b, ubgb⟩ --rintro for "recursive intro"
  exact ⟨a + b, fnUb_add ubfa ubgb⟩

example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x :=
  fun ⟨a, ubfa⟩ ⟨b, ubgb⟩ ↦ ⟨a + b, fnUb_add ubfa ubgb⟩


--Another way to unpack information in a hypothesis
--The hypothesis has a specific "pattern" that is unpacked (pattern matching in computer science)
example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  obtain ⟨a, ubfa⟩ := ubf
  obtain ⟨b, ubgb⟩ := ubg
  exact ⟨a + b, fnUb_add ubfa ubgb⟩


variable {α : Type*} [CommRing α]

def SumOfSquares (x : α) :=
  ∃ a b, x = a ^ 2 + b ^ 2

theorem sumOfSquares_mul {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
    SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, xeq⟩
  rcases sosy with ⟨c, d, yeq⟩
  rw [xeq, yeq]
  use a * c - b * d, a * d + b * c
  ring


theorem sumOfSquares_mul' {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
    SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, rfl⟩
  rcases sosy with ⟨c, d, rfl⟩
  use a * c - b * d, a * d + b * c
  ring


example {a b c : ℤ} (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c := by
  rcases divab with ⟨d, beq⟩
  rcases divbc with ⟨e, ceq⟩
  rw [ceq, beq]
  use d * e; ring

-- a | b has a hidden existential quantifier
example {a b c : ℤ} (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
  rcases divab with ⟨d1, eq_mul1⟩
  rcases divac with ⟨d2, eq_mul2⟩
  use d1 + d2
  rw [eq_mul1,eq_mul2]
  ring


-- Surjectivity requires universal and existential quantifiers
-- ∀y ∃x : f x = y
example {c : ℝ} : Surjective fun x ↦ x + c := by
  intro y
  use y - c
  dsimp; ring

#check mul_inv_cancel
#check one_mul_eq_id

example {c : ℝ} (h : c ≠ 0) : Surjective fun x ↦ c * x := by
  intro y
  use  (1/c) * y
  dsimp;
  rw [<-mul_assoc, one_div, mul_inv_cancel₀ h, one_mul]

-- Like with rings, we can do automatic simplifications on fields
example (x y : ℝ) (h : x - y ≠ 0) : (x ^ 2 - y ^ 2) / (x - y) = x + y := by
  field_simp [h]
  ring

example {f : ℝ → ℝ} (h : Surjective f) : ∃ x, f x ^ 2 = 4 := by
  rcases h 2 with ⟨x, hx⟩ --Says take y=2 and treats h as a function
  use x
  rw [hx]
  norm_num

variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

example (surjg : Surjective g) (surjf : Surjective f) : Surjective fun x ↦ g (f x) := by
  intro y
  rcases surjg y with ⟨b, h1⟩
  rcases surjf b with ⟨a, h2⟩
  use a
  dsimp
  rw [h2,h1]



-- Section 3.3 : Negation --------------------------------------------
variable (a b : ℝ)
variable (f : ℝ → ℝ)


example (h : a < b) : ¬b < a := by
  intro h' --(assume b < a since the statement to prove is b < a -> False )
  have : a < a := lt_trans h h'
  apply lt_irrefl a this

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith


example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  intro fhaslb
  rcases fhaslb with ⟨a, alef⟩
  rcases h a with ⟨x, flea⟩
  have h0 : a < a := lt_of_le_of_lt (alef x) flea
  apply lt_irrefl a
  exact h0

#check lt_add_one
#check lt_of_lt_of_le

example : ¬FnHasUb fun x ↦ x := by
  intro fhasub
  rcases fhasub with ⟨a, flea⟩
  have h0 : a + 1 ≤ a := flea (a + 1)
  have h1: a < a := lt_of_lt_of_le (lt_add_one a) h0
  apply lt_irrefl a
  exact h1

#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

example (h : Monotone f) (h' : f a < f b) : a < b := by
  apply lt_of_not_ge
  contrapose h'
  apply not_lt_of_ge
  exact h h'

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  contrapose h'
  apply not_lt_of_ge
  exact h' h

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ) -- x maps to 0 (in ℝ)
  have monof : Monotone f := by
    intro a b aleb
    dsimp [f]
    exact le_refl (0 : ℝ)
  have h' : f 1 ≤ f 0 := le_refl _
  have h0 : (1 : ℝ) ≤ 0 := by apply h monof h'
  linarith

#check lt_self_iff_false

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro zlex
  have h0 : x < x := h x zlex
  exact (lt_self_iff_false x).mp h0


variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro x px
  apply h
  use x

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  intro ex_x_px
  rcases ex_x_px with ⟨x, px⟩
  apply h
  exact px

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  contrapose! h
  exact h

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro all_x_px
  rcases h with ⟨x, not_px⟩
  apply not_px
  exact all_x_px x


-- Proof by contradiction
-- by_contra tactic allows us to prove Q by assuming not Q and proving False
example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩


example (h : ¬¬Q) : Q := by
  by_contra h0
  apply h
  exact h0

example (h : Q) : ¬¬Q := by
  intro not_q
  apply not_q
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  sorry

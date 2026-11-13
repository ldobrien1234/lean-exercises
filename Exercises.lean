import Mathlib

/-!
# First Lean + Mathlib exercises

Replace each `sorry` with a proof. Hints are in comments if you get stuck.
General tip: when you don't know a lemma's name, try `exact?` and Lean will
search Mathlib for you.
-/

/-! ## 1. Logic (tactics: intro, exact, constructor, cases/obtain, left, right) -/

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
   constructor
   exact hp
   exact hq

example (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  constructor
  · exact h.right
  · exact h.left

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  rcases h with hp | hq
  right; exact hp
  left; exact hq

example (p q r : Prop) (hpq : p → q) (hqr : q → r) : p → r := by
  intro h
  apply hqr
  apply hpq
  exact h

example (p : Prop) : ¬¬¬p → ¬p := by
  intro h hp
  apply h
  intro h1
  exact h1 hp

example (α : Type) (P Q : α → Prop) (h : ∀ x, P x ∧ Q x) : ∀ x, P x := by
  intro x
  specialize h x
  exact h.left

example (α : Type) (P : α → Prop) (a : α) (h : P a) : ∃ x, P x := by
  use a

/-! ## 2. Algebra (tactics: ring, linarith, nlinarith, positivity) -/

example (a b c : ℕ) : a * (b + c) = a * b + a * c := by
  ring

example (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

example (x : ℝ) (h : 2 * x + 3 = 7) : x = 2 := by
  linarith

example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  positivity

example (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-! ## 3. Divisibility and parity -/

example : Even (10 : ℕ) := by
  use 5

example (a b c : ℕ) (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c := by
  obtain ⟨k2,hk2⟩ := h2
  obtain ⟨k1,hk1⟩ := h1
  use k1*k2
  rw [hk2,hk1]
  ring

example (n : ℕ) (h : Odd n) : Odd (n ^ 2) := by
  sorry

example (n : ℕ) : Even (n * (n + 1)) := by
  sorry -- hint: `exact?`

/-! ## 4. Sets (tactics: intro, ext, simp, constructor) -/

example (α : Type) (s t : Set α) : s ∩ t ⊆ s := by
  sorry -- hint: `intro x hx`; `hx` is a proof of `x ∈ s ∧ x ∈ t`

example (α : Type) (s t : Set α) : s ∩ t = t ∩ s := by
  sorry -- hint: `ext x`, then prove an `↔`

example (α : Type) (s t u : Set α) : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) := by
  sorry -- try it by hand first, then see what `ext x; simp; tauto` does

/-! ## 5. Functions -/

example (f g : ℕ → ℕ) (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (g ∘ f) := by
  sorry -- hint: `intro a b h`, then `apply hf`

/-! ## 6. Challenge: induction with sums -/

-- The sum of the first n odd numbers is n².
example (n : ℕ) : ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := by
  sorry -- hint: `induction n with | zero => ... | succ n ih => ...`
        -- and the lemma `Finset.sum_range_succ`

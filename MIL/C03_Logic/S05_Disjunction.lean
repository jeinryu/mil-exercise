import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
  · have := abs_nonneg x
    linarith

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · have := abs_nonneg x
    linarith
  · rw [abs_of_neg h]


theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with h | h
  · rw [abs_of_nonneg h]
    exact add_le_add (le_abs_self x) (le_abs_self y)
  · rw [abs_of_neg h, neg_add]
    exact add_le_add (neg_le_abs_self x) (neg_le_abs_self y)


theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    constructor
    intro h; left; exact h
    intro h'; rcases h' with h₁ | h₂
    exact h₁
    linarith
  · rw [abs_of_neg h]
    constructor
    intro h; right; exact h
    intro h'; rcases h' with h₁ | h₂
    linarith
    exact h₂



theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  · intro h
    have h₁ := le_abs_self x
    have h₂ := neg_le_abs_self x
    constructor <;> linarith
  · rintro ⟨h₁, h₂⟩
    rcases le_or_gt 0 x with h | h
    rw [abs_of_nonneg h]; exact h₂
    rw [abs_of_neg h]; linarith

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, ⟨y, ⟨h₁, h₂⟩⟩⟩ <;> linarith [pow_two_nonneg x, pow_two_nonneg y]

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : (x + 1) * (x - 1) = 0 := by linarith
  rcases eq_zero_or_eq_zero_of_mul_eq_zero this with h' | h'
  right; linarith
  left; linarith

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have : (x + y) * (x - y) = 0 := by linarith
  rcases eq_zero_or_eq_zero_of_mul_eq_zero this with h' | h'
  right; linarith
  left; linarith

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : (x + 1) * (x - 1) = 0 := by ring_nf; rw [h, neg_add_cancel]
  rcases eq_zero_or_eq_zero_of_mul_eq_zero this with h' | h'
  right; exact add_eq_zero_iff_eq_neg.mp h'
  left; exact sub_eq_zero.mp h'


example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have : (x + y) * (x - y) = 0 := by ring_nf; rw [h, sub_eq_zero]
  rcases eq_zero_or_eq_zero_of_mul_eq_zero this with h' | h'
  right; exact add_eq_zero_iff_eq_neg.mp h'
  left; exact sub_eq_zero.mp h'

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  · intro h
    by_cases h' : P
    · right; exact h h'
    · left; exact h'
  · intro h₁ h₂
    rcases h₁ with h' | h'
    contradiction; exact h'

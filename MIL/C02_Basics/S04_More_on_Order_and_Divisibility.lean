import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  apply le_antisymm
  repeat
    apply max_le
    apply le_max_right
    apply le_max_left

example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · show min (min a b) c ≤ min a (min b c)
    have h : min (min a b) c ≤ min a b := min_le_left (min a b) c
    apply le_min
    · show min (min a b) c ≤ a
      exact le_trans h (min_le_left a b)
    · show min (min a b) c ≤ min b c
      apply le_min
      · exact le_trans h (min_le_right a b)
      · exact min_le_right (min a b) c
  · show min a (min b c) ≤ min (min a b) c
    have h : min a (min b c) ≤ min b c := min_le_right a (min b c)
    apply le_min
    · show min a (min b c) ≤ min a b
      apply le_min
      · exact min_le_left a (min b c)
      · exact le_trans h (min_le_left b c)
    · show min a (min b c) ≤ c
      apply le_trans h (min_le_right b c)


theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  · apply add_le_add_right
    apply min_le_left
  · apply add_le_add_right
    apply min_le_right

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · exact aux a b c
  · show min (a + c) (b + c) ≤ min a b + c
    have h := aux (a + c) (b + c) (-c)
    rw [add_neg_cancel_right, add_neg_cancel_right] at h
    linarith

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  have h := abs_add (a - b) b
  rw [sub_add_cancel] at h
  linarith
end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  have h₁ : x ∣ y * (x * z) := by
    apply dvd_mul_of_dvd_right
    apply dvd_mul_right
  rw [add_assoc]
  apply dvd_add h₁
  have h₂ : x ∣ x ^ 2 := by apply dvd_mul_left
  apply dvd_add h₂
  apply dvd_pow h (by norm_num)
end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  apply _root_.dvd_antisymm
  · show m.gcd n ∣ n.gcd m
    apply dvd_gcd
    exact gcd_dvd_right m n
    exact gcd_dvd_left m n
  · show n.gcd m ∣ m.gcd n
    apply dvd_gcd
    exact gcd_dvd_right n m
    exact gcd_dvd_left n m

end

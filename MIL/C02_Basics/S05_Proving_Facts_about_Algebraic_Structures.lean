import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
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

end

section
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
  repeat
    apply le_inf
    exact inf_le_right
    exact inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · show x ⊓ y ⊓ z ≤ x ⊓ (y ⊓ z)
    apply le_inf
    · show x ⊓ y ⊓ z ≤ x
      trans x ⊓ y
      · exact inf_le_left -- x ⊓ y ⊓ z ≤ x ⊓ y
      · exact inf_le_left -- x ⊓ y ≤ x
    · show x ⊓ y ⊓ z ≤ y ⊓ z
      apply le_inf
      · show x ⊓ y ⊓ z ≤ y
        trans x ⊓ y
        exact inf_le_left
        exact inf_le_right
      · exact inf_le_right -- x ⊓ y ⊓ z ≤ z
  · show x ⊓ (y ⊓ z) ≤ x ⊓ y ⊓ z
    apply le_inf
    · show x ⊓ (y ⊓ z) ≤ x ⊓ y
      apply le_inf
      exact inf_le_left -- x ⊓ (y ⊓ z) ≤ x
      show x ⊓ (y ⊓ z) ≤ y
      trans y ⊓ z
      exact inf_le_right
      exact inf_le_left
    · show x ⊓ (y ⊓ z) ≤ z
      trans y ⊓ z
      exact inf_le_right
      exact inf_le_right

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  repeat
    apply sup_le
    exact le_sup_right
    exact le_sup_left


example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  · show x ⊔ y ⊔ z ≤ x ⊔ (y ⊔ z)
    apply sup_le
    · show x ⊔ y ≤ x ⊔ (y ⊔ z)
      apply sup_le
      exact le_sup_left -- x ≤ x ⊔ (y ⊔ z)
      -- y ≤ x ⊔ (y ⊔ z)
      trans y ⊔ z
      exact le_sup_left; exact le_sup_right
    · show z ≤ x ⊔ (y ⊔ z)
      trans y ⊔ z
      exact le_sup_right; exact le_sup_right
  · show x ⊔ (y ⊔ z) ≤ x ⊔ y ⊔ z
    apply sup_le
    · show x ≤ x ⊔ y ⊔ z
      trans x ⊔ y
      exact le_sup_left; exact le_sup_left
    · show y ⊔ z ≤ x ⊔ y ⊔ z
      apply sup_le
      trans x ⊔ y
      exact le_sup_right; exact le_sup_left
      exact le_sup_right


theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · exact inf_le_left -- x ⊓ (x ⊔ y) ≤ x
  · show x ≤ x ⊓ (x ⊔ y)
    apply le_inf
    exact le_refl x -- x ≤ x
    exact le_sup_left -- x ≤ x ⊔ y



theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  · show x ⊔ x ⊓ y ≤ x
    apply sup_le
    exact le_refl x -- x ≤ x
    exact inf_le_left -- x ⊓ y ≤ x
  · exact le_sup_left -- x ≤ x ⊔ x ⊓ y

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw [h, inf_comm (a ⊔ b) a, absorb1]
  rw [inf_comm (a ⊔ b) c, h]
  rw [← sup_assoc, inf_comm c a, absorb2, inf_comm c b]

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  rw [h, sup_comm (a ⊓ b) a, absorb2]
  rw [sup_comm (a ⊓ b) c, h]
  rw [← inf_assoc, sup_comm c a, absorb1, sup_comm c b]

end

section
variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

lemma le_sub (h : a ≤ b) : 0 ≤ b - a := by
  have h₁ := sub_le_sub_right h a
  rw [sub_self] at h₁
  exact h₁

lemma sub_le (h: 0 ≤ b - a) : a ≤ b := by
  have h₁ := add_le_add_right h a
  rw [zero_add, sub_add_cancel] at h₁
  exact h₁

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have h₁ := le_sub a b h
  have h₂ := mul_nonneg h₁ h'
  apply sub_le
  rw [sub_mul] at h₂
  exact h₂

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  have h := dist_triangle x y x
  rw [dist_self, dist_comm y x] at h
  linarith

end

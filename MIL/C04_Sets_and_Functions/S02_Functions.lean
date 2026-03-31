import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro h x xs
    show f x ∈ v
    have : f x ∈ f '' s := by use x
    exact h this
  · rintro h x ⟨a, ha, rfl⟩
    have := h ha
    exact this


example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  rintro x ⟨_, ha, hax⟩
  rw [←(h hax)]
  exact ha

example : f '' (f ⁻¹' u) ⊆ u := by
  rintro x ⟨_, ha, hax⟩
  rw [← hax]
  exact ha

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro y hy
  rcases h y with ⟨x, rfl⟩
  use x
  constructor
  exact hy; rfl

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  rintro y ⟨x, hx, rfl⟩
  use x
  exact ⟨h hx, rfl⟩

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x hx
  exact h hx

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  constructor

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro y ⟨x, hx, rfl⟩
  constructor
  use x; exact ⟨hx.1, rfl⟩
  use x; exact ⟨hx.2, rfl⟩

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro y ⟨⟨a, ha, ha'⟩, ⟨b, hb, h'⟩⟩
  have : f a = f b := by
    trans y
    exact ha'
    exact h'.symm
  have : a = b := by exact h this
  rw [← this] at hb
  use a
  exact ⟨⟨ha, hb⟩, ha'⟩

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rintro _ ⟨⟨x, hx, rfl⟩, h₂⟩
  use x
  constructor
  · constructor
    · exact hx
    intro ht
    simp at h₂
    have := h₂ x ht
    contradiction
  rfl

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  intro x ⟨h₁, h₂⟩
  constructor
  · exact h₁
  · intro hv
    exact h₂ hv


example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext y
  constructor
  · intro ⟨⟨x, hs, hx⟩, h₂⟩
    rw [← hx] at h₂
    use x
    exact ⟨⟨hs, h₂⟩, hx⟩
  · intro ⟨x, ⟨_, h₂⟩, hy⟩
    constructor
    use x
    rw [← hy]
    exact h₂


example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  intro y ⟨x, ⟨_, h₂⟩, hx⟩
  rw [← hx]
  constructor
  use x
  exact h₂

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  intro x ⟨_, h₂⟩
  constructor
  use x; exact h₂

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (_ | h)
  · left; use x
  · right; exact h


variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y
  constructor
  · simp
    intro x i _ hx
    use i, x
  · simp
    intro i x _ hx
    use x
    constructor
    use i; exact hx


example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  simp
  intro i y hy
  show f y ∈ f '' A i
  use y
  simp at hy
  exact ⟨hy i, rfl⟩


example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro y hy
  simp at hy
  rcases hy i with ⟨x, hx⟩
  use x
  constructor
  · simp; intro i'
    rcases hy i' with ⟨x', hx'⟩
    have : f x = f x' := by
      trans y
      exact hx.2
      exact hx'.2.symm
    rw [injf this]
    exact hx'.1
  · exact hx.2

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  constructor <;> simp


example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  constructor <;> simp

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x xpos y ypos h
  rw [sqrt_eq_iff_mul_self_eq] at h
  rw [h, ← sqrt_mul, sqrt_mul_self]
  exact ypos
  exact ypos
  exact xpos
  exact sqrt_nonneg y


example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x xpos y ypos h
  dsimp at h
  rw [← sqrt_sq xpos, h, sqrt_sq]
  exact ypos

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext y; constructor
  · rintro ⟨x, xpos, rfl⟩
    simp
  · intro ypos
    use y ^ 2
    exact ⟨sq_nonneg y, sqrt_sq ypos⟩


example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    dsimp; exact sq_nonneg x
  · intro ypos
    use sqrt y; dsimp
    exact sq_sqrt ypos

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  · intro hinj x
    apply hinj
    apply inverse_spec
    use x
  · intro hlinj
    simp [LeftInverse] at hlinj
    intro x x' h
    rw [← hlinj x, ← hlinj x', h]


example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  · intro hsurj y
    apply inverse_spec
    rcases hsurj y with ⟨x, _⟩
    use x
  · intro h y
    have := h y
    use inverse f y

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := by simp [S]; exact h₁
  have h₃ : j ∉ S := by rw [h] at h₁; exact h₁
  contradiction

-- COMMENTS: TODO: improve this
end

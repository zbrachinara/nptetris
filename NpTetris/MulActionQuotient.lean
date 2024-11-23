import Mathlib.Algebra.Group.Defs
import Mathlib.GroupTheory.GroupAction.Basic

private def orbit_setoid (β α) [Group β] [MulAction β α] : Setoid α where
r a b := ∃ t : β, t • a = b
iseqv := by
  constructor
  · intro x; exists 1; simp
  · rintro x y ⟨t, txy⟩
    exists t⁻¹
    apply smul_left_cancel t
    rw [<- mul_smul, mul_inv_cancel, one_smul, txy]
  · intro x y z ⟨t₁, xy⟩ ⟨t₂, yz⟩
    exists t₂ * t₁
    rw [mul_smul, xy, yz]

/-- For some reason, the counterpart in mathlib, `MulAction.orbitRel.Quotient`, relies on the axiom
  of choice. This one does not. -/
def orbit_quotient (β α) [Group β] [MulAction β α] := Quotient (orbit_setoid β α)

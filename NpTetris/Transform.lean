import Mathlib

/-- Translates addition into "multiplication" -/

abbrev Position := Multiplicative (ℤ × ℤ)
abbrev Rotation := Multiplicative (ZMod 4)

example :
  (Multiplicative.ofAdd ⟨2,3⟩) * (Multiplicative.ofAdd ⟨4,5⟩)
  = (Multiplicative.ofAdd ⟨6,8⟩ : Position)
:= by
  rw [<- ofAdd_add]
  simp

private def four_rot : GaussianInt := {re := 0, im := 1}
private theorem elim_four_rot : four_rot ^ 4 = 1 := rfl

/-- Rotations on gaussian integers by 90 degrees -/
def aut_rot_gaussian (rotation : Rotation) : AddAut GaussianInt where
toFun p := (four_rot ^ rotation.toAdd.val) * p
invFun p := (four_rot ^ (4 - rotation.toAdd.val)) * p
left_inv _ := by
  dsimp
  rw [<- mul_assoc, <- pow_add, Nat.sub_add_cancel, elim_four_rot]
  simp only [Int.reduceNeg, one_mul]
  exact ZMod.val_le rotation.toAdd
right_inv _ := by
  dsimp
  rw [<- mul_assoc, <- pow_add, <- Nat.add_sub_assoc, add_comm, Nat.add_sub_cancel, elim_four_rot]
  simp
  exact ZMod.val_le rotation.toAdd
map_add' x y := by ring

/-- Relating gaussian integers to our own custom positions -/
def iso_gaussian_position : GaussianInt ≃+ (ℤ × ℤ) where
toFun := by intro ⟨x, y⟩; exact ⟨x, y⟩
invFun := by intro ⟨x, y⟩; exact ⟨x, y⟩
left_inv h := rfl
right_inv k := rfl
map_add' a b := rfl

/-- Now we can use the guassian integers as a bridge to define automorphisms on position -/
def aut_rot_additive (rotation : Rotation) : AddAut (ℤ × ℤ):=
  ((iso_gaussian_position.symm).trans (aut_rot_gaussian rotation)).trans iso_gaussian_position

/-- And finally, translate to "multiplication" to prepare for semidirect product. -/
def aut_rot (rotation : Rotation) : MulAut Position where
toFun x := x |> Multiplicative.toAdd |> (aut_rot_additive rotation).toFun |> Multiplicative.ofAdd
invFun x := x |> Multiplicative.toAdd |> (aut_rot_additive rotation).invFun |> Multiplicative.ofAdd
left_inv x := by simp
right_inv x := by simp
map_mul' x y := by simp

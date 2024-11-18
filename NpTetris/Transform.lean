import Mathlib

/-!
This basically defines a (very limited) module
-/

structure Position where
  x : ℤ
  y : ℤ

namespace Position

instance : Mul Position where
  mul | ⟨x₁, y₁⟩, ⟨x₂, y₂⟩ => ⟨x₁ + x₂, y₁ + y₂⟩
instance : Inv Position where
  inv x := ⟨-x.x, -x.y⟩
instance : One Position where
  one := ⟨0, 0⟩

#check Prod.mk.inj_iff
/-- Taken from [Prod.mk.inj_iff] -/
theorem mk.inj_iff {a₁ a₂ b₁ b₂ : ℤ} : (⟨a₁, b₁⟩: Position) = ⟨a₂, b₂⟩ ↔ a₁ = a₂ ∧ b₁ = b₂ :=
  Iff.of_eq (mk.injEq _ _ _ _)

@[simp]
theorem mul_def (x₁ y₁ x₂ y₂ : ℤ) : (⟨x₁, y₁⟩ : Position) * ⟨x₂, y₂⟩ = ⟨x₁ + x₂, y₁ + y₂⟩ := by
  apply Position.mk.inj_iff.mpr
  simp
@[simp]
theorem one_def : (1 : Position) = ⟨0,0⟩ := rfl
@[simp]
theorem inv_def (x y : ℤ) : (⟨x, y⟩ : Position)⁻¹ = ⟨-x, -y⟩ := rfl

instance : Group Position := by
  apply Group.ofRightAxioms
  · rintro ⟨a, d⟩ ⟨b, e⟩ ⟨c, f⟩
    simp
    apply And.intro <;> apply add_assoc
  · intro ⟨x, y⟩; simp
  · intro ⟨x, y⟩; simp

instance : CommGroup Position where
  mul_comm := by
    rintro ⟨a,c⟩ ⟨b,d⟩
    simp
    apply And.intro <;> apply add_comm

instance : AddCommGroup Position := Additive.addCommGroup

theorem add_mul_equiv (a b : Position) : a + b = a * b := rfl

end Position

structure Rotation where
  state : (ZMod 4)

namespace Rotation

instance : Mul Rotation where
  mul x y := ⟨x.state + y.state⟩
instance : Inv Rotation where
  inv x := ⟨-x.state⟩
instance : One Rotation where
  one := ⟨0⟩

@[local simp]
theorem mul_def (a b : ZMod 4) : (⟨a⟩ : Rotation) * ⟨b⟩ = ⟨a + b⟩ := rfl
@[local simp]
theorem one_def : (1 : Rotation) = ⟨0⟩ := rfl
@[local simp]
theorem inv_def (x : ZMod 4) : (⟨x⟩ : Rotation)⁻¹ = ⟨-x⟩ := rfl

instance : Group Rotation := by
  apply Group.ofRightAxioms
  · rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    simp; apply add_assoc
  · intro ⟨a⟩; simp
  · intro ⟨x⟩; simp

instance : CommGroup Rotation where
  mul_comm := by
    rintro ⟨x⟩ ⟨y⟩
    simp
    apply add_comm

end Rotation

/-- Translated addition into "multiplication" -/
example : (⟨2,3⟩: Position) * (⟨4,5⟩ : Position) = ⟨6,8⟩ := by
  simp

def four_rot : GaussianInt := {re := 0, im := 1}

theorem elim_four_rot : four_rot ^ 4 = 1 := rfl

/-- Rotations on gaussian integers by 90 degrees -/
def aut_rot_gaussian (rotation : Rotation) : AddAut GaussianInt where
toFun p := (four_rot ^ rotation.state.val) * p
invFun p := (four_rot ^ (4 - rotation.state.val)) * p
left_inv _ := by
  dsimp
  rw [<- mul_assoc, <- pow_add, Nat.sub_add_cancel, elim_four_rot]
  simp only [Int.reduceNeg, one_mul]
  exact ZMod.val_le rotation.state
right_inv _ := by
  dsimp
  rw [<- mul_assoc, <- pow_add, <- Nat.add_sub_assoc, add_comm, Nat.add_sub_cancel, elim_four_rot]
  simp
  exact ZMod.val_le rotation.state
map_add' x y := by ring

/-- Relating gaussian integers to our own custom positions -/
def iso_gaussian_position : GaussianInt ≃+ Position where
toFun := by intro ⟨x, y⟩; exact ⟨x, y⟩
invFun := by intro ⟨x, y⟩; exact ⟨x, y⟩
left_inv h := rfl
right_inv k := rfl
map_add' a b := by simp [Position.add_mul_equiv]

/-- Now we can use the guassian integers as a bridge to define automorphisms on position -/
def aut_rot_additive (rotation : Rotation) : AddAut Position :=
  ((iso_gaussian_position.symm).trans (aut_rot_gaussian rotation)).trans iso_gaussian_position

/-- And finally, translate to "multiplication" to prepare for semidirect product. -/
def aut_rot (rotation : Rotation) : MulAut Position := by sorry

def aut_id : MulAut Position := 1
def aut_r1 : MulAut Position where
toFun p := ⟨-p.y, p.x⟩
invFun p := ⟨p.y, -p.x⟩
left_inv _ := by simp
right_inv _ := by simp
map_mul' p q := by
  simp
  apply And.intro <;> rw[Position.mul_def]
  simp
  rw [add_comm]
def aut_r3 := aut_r1⁻¹
def aut_r2 : MulAut Position where
toFun p := ⟨-p.x, -p.y⟩
invFun p := ⟨-p.x, -p.y⟩
left_inv _ := by simp
right_inv _ := by simp
map_mul' p q := by
  simp
  apply And.intro <;> (rw [Position.mul_def]; simp; rw [add_comm])

def rotation_Z2 : MonoidHom Rotation (MulAut Position) where
toFun rot := match rot.state with
| 0 => aut_id
| 1 => aut_r1
| 2 => aut_r2
| 3 => aut_r3
map_one' := rfl
map_mul' r1 r2 := by
  sorry

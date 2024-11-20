import Mathlib

/-- Translates addition into "multiplication" -/

abbrev Position := Multiplicative (ℤ × ℤ)
abbrev Rotation := Multiplicative (ZMod 4)

example :
  (Multiplicative.ofAdd ⟨2,3⟩) * (Multiplicative.ofAdd ⟨4,5⟩)
  = (Multiplicative.ofAdd ⟨6,8⟩ : Position)
:= by
  rw [<- ofAdd_add]
  simp only [Prod.mk_add_mk, Int.reduceAdd]

def four_rot : GaussianInt := {re := 0, im := 1}
@[local simp]
private theorem elim_four_rot : four_rot ^ 4 = 1 := rfl

/-- Rotations on gaussian integers by 90 degrees -/
def aut_rot_gaussian (rotation : Rotation) : AddAut GaussianInt where
toFun p := (four_rot ^ rotation.toAdd.val) * p
invFun p := (four_rot ^ (4 - rotation.toAdd.val)) * p
left_inv _ := by
  dsimp only
  rw [<- mul_assoc, <- pow_add, Nat.sub_add_cancel]
  simp only [elim_four_rot, one_mul]
  exact ZMod.val_le rotation.toAdd
right_inv _ := by
  -- Almost the same proof, but some numbers are switched around
  dsimp only
  rw [<- mul_assoc, <- pow_add, <- Nat.add_sub_assoc, add_comm, Nat.add_sub_cancel]
  simp only [elim_four_rot, one_mul]
  exact ZMod.val_le rotation.toAdd
map_add' _ _ := by ring

/-- Relating gaussian integers to our own custom positions -/
def iso_gaussian_position : GaussianInt ≃+ (ℤ × ℤ) where
toFun := by intro ⟨x, y⟩; exact ⟨x, y⟩
invFun := by intro ⟨x, y⟩; exact ⟨x, y⟩
left_inv _ := rfl
right_inv _ := rfl
map_add' _ _ := rfl

/-- Now we can use the Gaussian integers as a bridge to define automorphisms on position -/
def aut_rot_additive (rotation : Rotation) : AddAut (ℤ × ℤ):=
  ((iso_gaussian_position.symm).trans (aut_rot_gaussian rotation)).trans iso_gaussian_position

/-- And finally, translate to "multiplication" to prepare for semidirect product. -/
def aut_rot (rotation : Rotation) : MulAut Position where
toFun x := x |> Multiplicative.toAdd |> (aut_rot_additive rotation).toFun |> Multiplicative.ofAdd
invFun x := x |> Multiplicative.toAdd |> (aut_rot_additive rotation).invFun |> Multiplicative.ofAdd
left_inv _ := by simp
right_inv _ := by simp
map_mul' _ _ := by simp

theorem four_rot_equiv_z4 (x y : ZMod 4) :
  four_rot ^ (x + y).val = four_rot ^ x.val * four_rot ^ y.val
:= by
  let k := x.val + y.val
  rcases Nat.lt_or_ge k 4 with lt | ge
  · rw [ZMod.val_add_of_lt, pow_add]
    exact lt
  · rw [<- pow_add, ZMod.val_add_val_of_le ge, pow_add, elim_four_rot, mul_one]

theorem aut_rot_linear (r₁ r₂ : Rotation) (p : Position) :
  aut_rot (r₁ * r₂) p = aut_rot r₁ (aut_rot r₂ p)
:= by
  simp [aut_rot, aut_rot_additive, aut_rot_gaussian]
  rw [<- mul_assoc, four_rot_equiv_z4]

def rotation_hom : Rotation →* (MulAut Position) where
toFun := aut_rot
map_mul' x y := by
  ext s
  simp [aut_rot, aut_rot_additive, aut_rot_gaussian]
  rw [<- mul_assoc]
  congr
  apply four_rot_equiv_z4
map_one' := by
  ext s
  simp [aut_rot, aut_rot_additive, aut_rot_gaussian]

theorem neg_rotation (r : Rotation) (p : Position) :
  (rotation_hom r p)⁻¹ = rotation_hom r (p⁻¹)
:= by simp [rotation_hom]
theorem rotation_distrib (r : Rotation) (p₁ p₂ : Position) :
  (rotation_hom r) (p₁ * p₂) = (rotation_hom r p₁) * (rotation_hom r p₂)
:= by simp [rotation_hom]

abbrev Transform := Position ⋊[rotation_hom] Rotation
instance : SMul Transform Position where
smul := by
  rintro ⟨translate, rotate⟩ pos
  exact rotation_hom rotate pos * translate

theorem Transform.smul_def (t : Transform) (p : Position) :
  t • p = rotation_hom t.right p * t.left
:= rfl
theorem Transform.one_def :
  (1 : Transform) = ⟨Multiplicative.ofAdd 0, Multiplicative.ofAdd 0⟩
:= rfl

instance: MulAction Transform Position where
one_smul _ := by
  rw [Transform.one_def, Transform.smul_def]
  simp
mul_smul x y p := by
  simp [Transform.smul_def, rotation_hom]
  rw [aut_rot_linear, mul_comm x.left, mul_assoc]

@[simp]
theorem Transform.invert (t : Transform) (p : Position) :
  (t • p)⁻¹ = (⟨t.left⁻¹, t.right⟩ : Transform)  • (p⁻¹)
:= by
  repeat rw [Transform.smul_def]
  simp
  rw [mul_comm]

theorem norm_four_rot (r : ZMod 4): Zsqrtd.norm (four_rot ^ r.val) = 1 := by
  have ⟨p, q⟩ := r
  induction p
  case zero => rfl
  case succ n ih =>
    have ih := ih (Nat.lt_of_succ_lt q)
    have (k: Nat) (q : k < 4) : @ZMod.val 4 (⟨k, q⟩: ZMod 4) = k := by exact rfl
    rw [this] at ih
    rw [this, pow_add, Zsqrtd.norm_mul, ih, one_mul, pow_one]
    rfl

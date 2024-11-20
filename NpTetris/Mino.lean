import NpTetris.Transform

def one_off' : Set (ℤ × ℤ) := {(p, q) : (ℤ × ℤ) | p^2 + q^2 = 1 }
def one_off : Set Position := { Multiplicative.ofAdd x | x ∈ one_off'}

private theorem norm_is_id_lemma (r : Rotation):
  (four_rot ^ (Multiplicative.toAdd r).val).im ^ 2 +
  (four_rot ^ (Multiplicative.toAdd r).val).re ^ 2 = 1
:= by
  have := norm_four_rot r
  have id : r.val = (Multiplicative.toAdd r).val := by exact rfl
  rw [Zsqrtd.norm_def, neg_one_mul, Int.neg_mul, Int.sub_neg] at this
  repeat rw [<- pow_two] at this
  rw [id, add_comm] at this
  exact this
/-- Rotation keeps one-off transformations -/
theorem rotation_preserves_one_off (p : Position) (r : Rotation) :
  p ∈ one_off → rotation_hom r p ∈ one_off
:= by
  simp [one_off, one_off']
  intro x y cond pxy
  rw [<- pxy]
  simp [rotation_hom, aut_rot, aut_rot_additive, aut_rot_gaussian, iso_gaussian_position]
  ring_nf
  conv =>
    lhs; rw [add_assoc, add_assoc];
    rhs; rw [<- add_assoc, add_comm, <- add_assoc, add_comm];
    lhs; rw [mul_comm]
  rw [<- add_assoc]
  repeat rw [<- add_mul]
  rw [add_comm (_ ^ _)]
  rw [norm_is_id_lemma]
  simp
  assumption

inductive Connected : Finset Position → Prop where
| triv set : set.card <= 1 → Connected set
| cons point (set' : Finset Position) :
    (∃ point' ∈ set', point⁻¹ * point' ∈ one_off) → Connected (insert point set')

@[ext]
structure Points (size : ℕ) where
  points: Finset Position
  connected: Connected points
  sized : points.card = size

@[simp]
def transform_map (t : Transform) : Position ↪ Position where
toFun := (t • ·)
inj' := MulAction.injective t

/-- Transforming a set of points preserves connectedness -/
instance (size : ℕ) : SMul Transform (Points size) where
smul := by
  rintro t ⟨points, conn, sized⟩
  apply Points.mk
  case mk.points => exact points.map (transform_map t)
  case mk.sized => simp only [Finset.card_map]; assumption -- trivial
  case mk.connected =>
    induction conn
    case triv set card =>
      apply Connected.triv
      rw [Finset.card_map]
      assumption
    case cons pt points witness =>
      rw [Finset.map_insert]
      apply Connected.cons
      have ⟨witness, wit_mem, wit_cond⟩ := witness
      exists (transform_map t) witness
      apply And.intro
      · rw [Finset.mem_map]
        exists witness
      · have ⟨t_left, t_right⟩ := t
        simp
        repeat rw [Transform.smul_def]
        simp
        conv => rhs; rw [mul_assoc]; rhs ; rw [mul_comm, mul_assoc]
        rw [mul_inv_cancel, mul_one]
        rw [neg_rotation, <- rotation_distrib]
        apply rotation_preserves_one_off
        assumption

@[simp]
theorem Transform.smul_points_def {n : ℕ} (t : Transform) (p : Points n) :
  (t • p).points = p.points.map (transform_map t)
:= rfl

/-- The rest of the group action axioms easily follow -/
instance (size : ℕ) : MulAction Transform (Points size) where
one_smul _ := by ext; simp
mul_smul a b p := by
  ext k
  simp only [Transform.smul_points_def, transform_map, Finset.mem_map,
             Function.Embedding.coeFn_mk]
  constructor <;> simp only [forall_exists_index, and_imp]
  · intro p p_points p_mul
    exists b • p
    constructor
    exists p
    rw [<- mul_smul]
    assumption
  · intro p1 p2 p2_points p2_to_p1 p1_to_k
    exists p2
    constructor
    assumption
    rw [mul_smul, p2_to_p1, p1_to_k]

def Shape (n : ℕ) := MulAction.orbitRel.Quotient Transform (Points n)

/-- TODO define rotation and translation operations, may also need a center of rotation -/
structure Mino (n : ℕ) where
  shape : Shape n
  position : Position
  rotation : Rotation

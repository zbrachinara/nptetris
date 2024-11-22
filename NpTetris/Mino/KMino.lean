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
  rw [add_comm (_ ^ _), norm_is_id_lemma, one_mul, one_mul]
  assumption

inductive Connected : Finset Position → Prop where
| triv set : set.card <= 1 → Connected set
| cons point (set' : Finset Position) :
    (∃ point' ∈ set', point⁻¹ * point' ∈ one_off) → Connected (insert point set')

@[simp]
def transform_map (t : Transform) : Position ↪ Position where
toFun := (t • ·)
inj' := MulAction.injective t

/-- The core of what k-tris is. The mino is a connected set of points in Z^2, which can be
  manipulated by translation or rotation. The number of points also remains the same between
  transformations, so this easy fact comes pre-encoded into the type. -/
@[ext]
structure KMino (k : ℕ+) where
  points: Finset Position
  connected: Connected points
  boundable : points.card = k

/-- Transforming a set of points preserves connectedness -/
instance (bound) : SMul Transform (KMino bound) where
smul := by
  rintro t ⟨points, conn, sized⟩
  apply KMino.mk
  case mk.points => exact points.map (transform_map t)
  case mk.boundable => rw [Finset.card_map]; assumption -- trivial
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
theorem Transform.smul_points_def {b} (t : Transform) (p : KMino b) :
  (t • p).points = p.points.map (transform_map t)
:= rfl

/-- The rest of the group action axioms easily follow -/
instance {b} : MulAction Transform (KMino b) where
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

/-- A mino which cares not for its place in the world. No matter what rotation and translation are
  applied to a mino, its shape must be preserved. This type serves as a convenience to encode this
  fact -- if two minos have the same shape, they are equal in `Shape`. -/
def Shape (bound) := MulAction.orbitRel.Quotient Transform (KMino bound)

namespace KMino

variable {k}

/-- The maximum y-coordinate of the positions of a mino. -/
def max_height (m : KMino k) : ℤ := by
  apply Finset.max'
  case s =>
    apply m.points.image
    intro pos
    exact pos.snd
  rw [Finset.image_nonempty]
  apply Finset.card_pos.mp
  rw [m.boundable]
  exact PNat.pos k

/-- Produces the shape of the given mino -/
def shape (m : KMino k) : Shape k := Quotient.mk _ m

/-- A relation between two minos that says that one can be maneuvered into the other. -/
structure ManeuverStep (k₁ k₂ : KMino k) : Prop where
shapes_id : k₁.shape = k₂.shape
touching : ∃ p₁ ∈ k₁.points, ∃ p₂ ∈ k₂.points, p₁ = p₂ ∨ p₁⁻¹ * p₂ ∈ one_off

abbrev Path := List (KMino k)

inductive Maneuver : @Path k → Prop where
| base p q: ManeuverStep p q → Maneuver [p, q]
| cons l mino nonempty :
    Maneuver l → ManeuverStep mino (l.head nonempty) → Maneuver (mino :: l)

theorem Maneuver.length_nz {list} (path : @Maneuver k list) : list ≠ [] := by
  cases path <;> apply List.cons_ne_nil

def Maneuver.head {list} (path : @Maneuver k list) : KMino k := by
  apply list.head
  apply Maneuver.length_nz
  assumption
def Maneuver.last {list} (path : @Maneuver k list) : KMino k := by
  apply list.getLast
  apply Maneuver.length_nz
  assumption

end KMino

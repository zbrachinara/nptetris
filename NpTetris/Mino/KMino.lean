import Mathlib.Data.Multiset.Fintype

import NpTetris.Transform
import NpTetris.MulActionQuotient

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
| triv p : Connected {p}
| cons point point' (set' : Finset Position) :
    point' ∈ set' → point⁻¹ * point' ∈ one_off → Connected (insert point set')

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
    case triv p =>
      apply Connected.triv
    case cons pt witness points wit_set wit_cond =>
      rw [Finset.map_insert]
      apply Connected.cons _ (transform_map t witness)
      · exact (Finset.mem_map' (transform_map t)).mpr wit_set
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
def KShape (bound) := orbit_quotient Transform (KMino bound)

namespace KMino

variable {k}

theorem nonempty (m : KMino k) : Nonempty m.points := by
  have ⟨points, connected, card⟩ := m
  dsimp only
  cases connected
  case triv p => exists p; rw [Finset.mem_singleton]
  case cons pt _ _ _ _ =>
    exists pt
    simp only [Finset.mem_insert, true_or]

def Position.y' (t: Position) : WithBot ℤ := some t.2

/-- The maximum y-coordinate of the positions of a mino. -/
def max_height (m : KMino k) : ℤ := by
  apply WithBot.unbot
  case x =>
    apply Multiset.sup
    apply Multiset.map
    case s => exact m.points.val
    exact Position.y'
  -- Proof that max_height is not unvalued
  intro has_bottom
  have pos : ¬∃ x, Position.y' x = ⊥ := by
    push_neg
    intro position pnone
    unfold Position.y' at pnone
    cases pnone
  have neg : ∃ x, Position.y' x = ⊥ := by
    have ⟨p, _⟩ := m.nonempty
    exists p
    apply bot_unique
    rw [<- has_bottom]
    apply Multiset.le_sup
    apply Multiset.mem_map_of_mem
    apply Finset.mem_def.mp
    assumption
  exact pos neg

/-- Produces the shape of the given mino -/
def shape (m : KMino k) : KShape k := Quotient.mk _ m

end KMino

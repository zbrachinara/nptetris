import NpTetris.Mino.Quarantine
import NpTetris.Transform
import NpTetris.MulActionQuotient

def norm_one_offsets : Finset Position := by
  apply Finset.map
  case α => exact (ℤ × ℤ)
  case s => exact {(0, 1), (1, 0), (0, -1), (-1, 0)}
  apply Equiv.toEmbedding
  exact Multiplicative.ofAdd
lemma norm_one.prop {x y : ℤ}: (x, y) ∈ norm_one_offsets ↔ x^2 + y^2 = 1 := by
  constructor
  · unfold norm_one_offsets
    simp
    rintro (h | h | h | h) <;> cases h <;> rfl
  · intro xy_norm
    have := int_square xy_norm
    apply Finset.mem_map.mpr
    exists (x, y)
    constructor <;> try rfl
    casesm* _ ∨ _
    case _ x_zro =>
      have : x^2 = 0 := by subst x; simp
      have : y^2 = 1 := by rw [this, zero_add] at xy_norm; exact xy_norm
      cases int_square_one.mp this
      repeat (subst x; subst y; simp)
    all_goals {
      have : x ^ 2 = 1 := by subst x; ring
      have : y ^ 2 = 0 := by rw [this] at xy_norm; exact (Int.add_left_inj 1).mp xy_norm
      have : y = 0 := int_square_zro.mp this
      subst x; subst y; simp
    }

private lemma norm_is_id (r : Rotation):
  (four_rot ^ (Multiplicative.toAdd r).val).im ^ 2 +
  (four_rot ^ (Multiplicative.toAdd r).val).re ^ 2 = 1
:= by
  have := norm_four_rot r
  have id : r.val = (Multiplicative.toAdd r).val := by exact rfl
  rw [Zsqrtd.norm_def, neg_one_mul, Int.neg_mul, Int.sub_neg] at this
  repeat rw [<- pow_two] at this
  rw [id, add_comm] at this
  exact this
/-- Rotation preserves one-off transformations -/
theorem rotation_preserves_norm_one (p : Position) (r : Rotation) :
  p ∈ norm_one_offsets → rotation_hom r p ∈ norm_one_offsets
:= by
  have ⟨x, y⟩ := p
  intro cond
  simp [rotation_hom, aut_rot, aut_rot_additive, aut_rot_gaussian, iso_gaussian_position]
  apply norm_one.prop.mpr
  ring_nf
  conv => -- TODO ugly proof, redo with calc
    lhs; rw [add_assoc, add_assoc];
    rhs; rw [<- add_assoc, add_comm, <- add_assoc, add_comm];
    lhs; rw [mul_comm]
  rw [<- add_assoc]
  repeat rw [<- add_mul]
  rw [add_comm (_ ^ _), norm_is_id, one_mul, one_mul]
  apply norm_one.prop.mp
  assumption

inductive Connected : Finset Position → Prop where
| triv p : Connected {p}
| cons point point' (set' : Finset Position) :
    point' ∈ set' → point⁻¹ * point' ∈ norm_one_offsets → Connected (insert point set')

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
deriving DecidableEq

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
        apply rotation_preserves_norm_one
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

def Position.y' (t: Position) : WithBot ℤ := some t.2
def Position.y'' (t : Position) : WithTop ℤ := some t.2

namespace KMino

variable {k} (m : KMino k)

theorem nonempty : Nonempty m.points := by
  have ⟨points, connected, card⟩ := m
  dsimp only
  cases connected
  case triv p => exists p; rw [Finset.mem_singleton]
  case cons pt _ _ _ _ =>
    exists pt
    simp only [Finset.mem_insert, true_or]

/-- The maximum y-coordinate of the positions of a mino. -/
def max_height : ℤ := by
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

def min_height : ℤ := by
  apply WithTop.untop
  case x =>
    apply Multiset.inf
    apply Multiset.map
    case s => exact m.points.val
    exact Position.y''
  intro has_top
  have pos : ¬∃ x, Position.y'' x = ⊤ := by
    push_neg
    intro position pnone
    unfold Position.y'' at pnone
    cases pnone
  have neg : ∃ x, Position.y'' x = ⊤ := by
    have ⟨p, _⟩ := m.nonempty
    exists p
    apply top_unique
    rw [<- has_top]
    apply Multiset.inf_le
    apply Multiset.mem_map_of_mem
    apply Finset.mem_def.mp
    assumption
  exact pos neg

instance explicit_withtop_int_preorder : Preorder (WithTop ℤ) where
le_refl := by exact fun a ↦ Preorder.le_refl a
le_trans := by exact fun a b c a_1 a_2 ↦ Preorder.le_trans a b c a_1 a_2
lt_iff_le_not_le := by exact fun a b ↦ lt_iff_le_not_le

lemma height_min_le_max : m.min_height ≤ m.max_height := by
  unfold min_height
  unfold max_height
  unfold WithTop.untop
  unfold WithBot.unbot
  split ; case _ x' _ x _ x_inf _ =>
  split ; case _ y' _ y _ y_sup _ =>
  by_cases h : x ≤ y ; assumption
  push_neg at h
  exfalso
--@LT.lt (WithTop ℤ) Preorder.toLT
  -- have : (some y)  < (some x) := by exact h
  -- let x'' : WithTop ℤ := (Multiset.map Position.y' m.points.val).inf
  -- let y'' : WithTop ℤ := some y
  -- have def_x'' : x'' = (Multiset.map Position.y' m.points.val).inf := by exact rfl
  -- have def_y'' : y'' = some y := by exact rfl
  -- rw [<- def_y''] at this
  -- rw [<- x_inf, <- def_x''] at this
  -- have : y'' ≤ (Multiset.map Position.y'' m.points.val).inf := by
  --   apply le_of_lt
  --   exact this
  sorry

def height := m.max_height - m.min_height -- TODO make into nat

/-- Produces the shape of the given mino -/
def shape (m : KMino k) : KShape k := Quotient.mk _ m

end KMino

namespace KShape

def minos {k} (shape : KShape k) : Set (KMino k) := {s | ⟦s⟧ = shape}

end KShape

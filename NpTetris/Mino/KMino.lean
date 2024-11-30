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


private lemma gaussian_int_aux {x : GaussianInt} : x.re ^2 - -x.im^2 = x.re^2 - -1 * x.im^2 := by
  refine (Int.sub_left_inj (x.re ^ 2)).mpr ?a
  exact Int.neg_eq_neg_one_mul (x.im ^ 2)

/-- Rotation preserves one-off transformations -/
theorem rotation_preserves_norm_one (p : Position) (r : Rotation) :
  p ∈ norm_one_offsets → rotation_hom r p ∈ norm_one_offsets
:= by
  have ⟨x, y⟩ := p
  intro cond
  simp only [rotation_hom]
  dsimp
  simp only [aut_rot, aut_rot_additive, aut_rot_gaussian, iso_gaussian_position]
  dsimp
  apply norm_one.prop.mpr
  generalize r'_def : (four_rot ^ (Multiplicative.toAdd r).val) = r'
  generalize p'_def : (Multiplicative.toAdd (x, y)) = p'
  repeat rw [add_sq]
  ring_nf
  conv => -- TODO ugly proof, redo with calc
    lhs; rw [add_assoc, add_assoc];
    rhs; rw [<- add_assoc, add_comm, <- add_assoc, add_comm];
    lhs; rw [Int.mul_comm]
  rw [<- add_assoc]
  repeat rw [<- add_mul]
  rw [ Int.add_comm (r'.im ^ _), <- Int.sub_neg _ (_ ^ _), gaussian_int_aux]
  repeat rw [pow_two]
  rw [<- Int.mul_assoc (-1), <-Zsqrtd.norm_def]
  have this' := norm_four_rot r
  have : (Multiplicative.toAdd r).val = r.val := by exact rfl
  rw [<-this] at this'
  rw [<-r'_def, this']
  ring_nf
  apply norm_one.prop.mp
  rw [<- p'_def]
  simpa

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
instance Mino.instSMul (bound) : SMul Transform (KMino bound) where
smul := by
  rintro t ⟨points, conn, sized⟩
  constructor
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

def botmap {α} (l : Multiset α) : Multiset (WithBot α) := l.map (WithBot.some ·)
def topmap {α} (l : Multiset α) : Multiset (WithTop α) := l.map (WithBot.some ·)


theorem eq_bot_top (a : Multiset ℤ) : botmap a = topmap a := rfl

def Position.y (t: Position) : ℤ := t.2
-- def Position.y'' (t : Position) : ℤ := t.2
def ymap (l : Multiset Position) : Multiset ℤ := l.map Position.y

def yfiber'{s : Multiset Position} : {x // x ∈ s} → {x // x ∈ ymap s} :=
λ ⟨a, b⟩ ↦ ⟨a.y, by unfold ymap; apply Multiset.mem_map_of_mem; exact b⟩
def ymap' (s : Multiset Position) (t : Multiset {x // x ∈ s}) : Multiset {x // x ∈ ymap s}
:= t.map (yfiber')

namespace KMino

variable {k} (m : KMino k)

theorem nonempty : Nonempty m.points := by
  have ⟨points, connected, sized⟩ := m
  dsimp only
  cases connected
  case triv p => exists p; rw [Finset.mem_singleton]
  case cons pt _ _ _ _ =>
    exists pt
    simp only [Finset.mem_insert, true_or]

theorem nonempty' : Nonempty m.points.attach := by
  have ⟨points, connected, sized⟩ := m
  dsimp only
  cases connected
  case triv p =>
    exists ⟨p, ?a1⟩
    exact Finset.mem_singleton.mpr rfl
    exact Finset.mem_attach {p} ⟨p, Finset.mem_singleton.mpr rfl⟩
  case cons pt _ _ _ _ =>
    exists ⟨pt, ?a2⟩
    apply Finset.mem_insert_self pt
    apply Finset.mem_attach

-- TODO cleanup/generalize, should be applicable to all maps to DecidableEq types

/-- The maximum y-coordinate of the positions of a mino. -/
def max_height' : {x : ℤ // x ∈ ymap m.points.val} := by
  apply WithBot.unbot
  case x =>
    apply Multiset.sup
    apply botmap
    apply ymap'
    exact m.points.val.attach
  -- Proof that max_height is not unvalued
  dsimp
  intro has_bottom
  have pos : ¬∃ x, (@yfiber' m.points.val x |> WithBot.some) = ⊥ := by
    push_neg
    intro position pnone
    unfold yfiber' at pnone
    cases pnone
  have neg : ∃ x, (@yfiber' m.points.val x |> WithBot.some) = ⊥ := by
    have ⟨p, _⟩ := m.nonempty'
    exists p
    apply bot_unique
    rw [<- has_bottom]
    apply Multiset.le_sup
    apply Multiset.mem_map_of_mem
    apply Multiset.mem_map_of_mem
    assumption
  exact pos neg

def min_height' : {x : ℤ // x ∈ ymap m.points.val} := by
  apply WithTop.untop
  case x =>
    apply Multiset.inf
    apply topmap
    apply ymap'
    exact m.points.val.attach
  intro has_top
  have pos : ¬∃ x, (@yfiber' m.points.val x |> WithTop.some) = ⊤ := by
    push_neg
    intro position pnone
    unfold yfiber' at pnone
    cases pnone
  have neg : ∃ x, (@yfiber' m.points.val x |> WithTop.some) = ⊤ := by
    have ⟨p, _⟩ := m.nonempty'
    exists p
    apply top_unique
    rw [<- has_top]
    apply Multiset.inf_le
    apply Multiset.mem_map_of_mem
    apply Multiset.mem_map_of_mem
    assumption
  exact pos neg

def max_height := m.max_height'.val
def min_height := m.min_height'.val

lemma height_min_le_max : m.min_height' ≤ m.max_height' := by
  simp only [min_height', max_height', WithTop.untop, WithBot.unbot]
  split ; case _ _ _ x _ _ _ =>
  split ; case _ _ _ y _ y_sup _ =>
  by_cases h : x ≤ y ; assumption
  exfalso
  push_neg at h
  let ⟨yv, yp⟩ := y
  let ⟨xv, xp⟩ := x
  have : ⟨xv, xp⟩ ∈ ymap' m.points.val m.points.val.attach := by
    unfold ymap'
    unfold yfiber'
    apply Multiset.mem_map.mpr
    let ⟨a, b, c⟩:= Multiset.mem_map.mp xp
    exists ⟨a, b⟩
    constructor
    exact Multiset.mem_attach m.points.val ⟨a, b⟩
    rw [Subtype.mk.injEq]
    assumption
  have : (WithBot.some ⟨xv, xp⟩: WithTop _) ∈ botmap (ymap' m.points.val m.points.val.attach) := by
    unfold botmap
    apply Multiset.mem_map_of_mem
    assumption
  have xy := Multiset.le_sup this
  rw [y_sup] at xy
  have xy: (⟨xv, xp⟩ : {x // x ∈ ymap m.points.val}) ≤ ⟨yv, yp⟩ := by
    apply WithBot.coe_le_coe.mp
    apply xy
  have yx : yv < xv := by exact h
  apply Lean.Omega.Int.le_lt_asymm
  exact xy; assumption

lemma height_le_of_proj : m.min_height ≤ m.max_height := by
  unfold min_height
  unfold max_height
  apply Subtype.GCongr.coe_le_coe
  exact height_min_le_max m

def height := m.max_height - m.min_height |> Int.toNat

/-- Produces the shape of the given mino -/
def shape : KShape k := ⟦m⟧

end KMino

def Shape.minos {k} (shape : KShape k) : Set (KMino k) := {s | ⟦s⟧ = shape}

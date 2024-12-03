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
| cons point point' (set' : Finset Position) : Connected set' →
    point' ∈ set' → point⁻¹ * point' ∈ norm_one_offsets → Connected (insert point set')

theorem Connected.nonempty s (conn : Connected s) : 0 < s.card := by
  induction conn with
  | triv _ => exact Nat.zero_lt_succ [].length
  | cons x _ set _ _ _ ih => calc
    _ < _ := ih
    _ ≤ _ := by apply Finset.card_le_card; apply Finset.subset_insert

/-- Although not defined this way, `Connected` can be functionally treated as if each construction
  introduces a brand new point, rather than a potentially existing one. -/
def Connected.induction_nonoverlapping
  (motive : (a : Finset Position) → Connected a → Prop)
  (triv : ∀ p, motive {p} (Connected.triv p))
  (cons : ∀ p p' set' conn,
    (p'_set : p' ∈ set') →
    (one_off : p⁻¹ * p' ∈ norm_one_offsets) →
    motive set' conn →
    p ∉ set' → -- the special sauce
    motive (insert p set') (by apply Connected.cons; repeat assumption)) :
  ∀ {s} conn, motive s conn := by intros s conn; induction conn with
| triv => apply triv
| cons point _ set conn' _ _ ih =>
  by_cases pmem : point ∈ set
  · have : insert point set = set := by exact Finset.insert_eq_of_mem pmem
    simp_rw [this]
    assumption
  · apply cons
    repeat assumption

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
    induction conn using Connected.induction_nonoverlapping generalizing bound
    case triv p => apply Connected.triv
    case cons pt witness points conn wit_set wit_cond ind pt_mem =>
      rw [Finset.map_insert]
      apply Connected.cons _ (transform_map t witness)
      · let bound' : ℕ+ := by
          refine ⟨bound.val - 1, ?g⟩
          rw [<- sized, Finset.card_insert_of_not_mem, Nat.add_one_sub_one]
          exact Connected.nonempty points conn
          assumption
        apply ind bound'
        unfold bound'
        change _ = bound.val - 1
        rw [<- sized, Finset.card_insert_of_not_mem, Nat.add_one_sub_one]
        assumption
      · exact (Finset.mem_map' (transform_map t)).mpr wit_set
      · have ⟨t_left, t_right⟩ := t
        simp
        repeat rw [Transform.smul_def]
        simp
        conv => rhs; rw [mul_assoc]; rhs ; rw [mul_comm, mul_assoc]
        rw [mul_inv_cancel, mul_one]
        rw [neg_rotation, <- rotation_distrib]
        apply rotation_preserves_norm_one
        exact wit_cond

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

def Position.y (t : Position) : ℤ := t.2
-- def Position.y' (t: Position) : WithBot ℤ := some t.2
-- def Position.y'' (t : Position) : WithTop ℤ := some t.2

namespace KMino

variable {k} (m : KMino k)

theorem nonempty : Nonempty m.points := by
  have ⟨points, connected, sized⟩ := m
  dsimp only
  cases connected
  case triv p => exists p; rw [Finset.mem_singleton]
  case cons pt _ _ _ _ _ =>
    exists pt
    simp only [Finset.mem_insert, true_or]

def ys : Multiset ℤ := m.points.val.map Position.y

-- TODO should generalize these two definitions
/-- The maximum y-coordinate of the positions of a mino. -/
def max_height : ℤ := by
  apply WithBot.unbot
  case x =>
    apply Multiset.sup
    exact m.ys.map (WithBot.some ·)
  -- Proof that max_height is not unvalued
  intro has_bottom
  have pos : ¬∃ x, WithBot.some (Position.y x) = ⊥ := by
    push_neg
    intro position pnone
    unfold Position.y at pnone
    cases pnone
  have neg : ∃ x, WithBot.some (Position.y x) = ⊥ := by
    have ⟨p, _⟩ := m.nonempty
    exists p
    apply bot_unique
    rw [<- has_bottom]
    apply Multiset.le_sup
    repeat apply Multiset.mem_map_of_mem
    assumption
  exact pos neg

def min_height : ℤ := by
  apply WithTop.untop
  case x =>
    apply Multiset.inf
    exact m.ys.map (WithTop.some · )
  intro has_top
  have pos : ¬∃ x, WithTop.some (Position.y x) = ⊤ := by
    push_neg
    intro position pnone
    unfold Position.y at pnone
    cases pnone
  have neg : ∃ x, WithTop.some (Position.y x) = ⊤ := by
    have ⟨p, _⟩ := m.nonempty
    exists p
    apply top_unique
    rw [<- has_top]
    apply Multiset.inf_le
    repeat apply Multiset.mem_map_of_mem
    assumption
  exact pos neg

theorem min_height_unpack :
  ∃ x, (Multiset.map (WithTop.some ·) m.ys).inf = WithTop.some x ∧ m.min_height = x
:= by
  exists m.min_height
  constructor
  unfold min_height; unfold WithTop.untop; split
  assumption
  rfl
theorem max_height_unpack :
  ∃ x, (Multiset.map (WithBot.some ·) m.ys).sup = WithBot.some x ∧ m.max_height = x
:= by
  exists m.max_height
  constructor
  unfold max_height; unfold WithBot.unbot; split
  assumption
  rfl

lemma min_height_mem : m.min_height ∈ m.ys := by
  have ⟨points, connected, card⟩ := m
  unfold min_height
  unfold WithTop.untop
  unfold ys
  dsimp only
  split ; case _ _ _ x _ inf he =>
  apply Multiset.mem_map.mpr
  induction connected using Connected.induction_nonoverlapping generalizing k with
  | triv p =>
    simp only [Finset.singleton_val, Multiset.mem_singleton, exists_eq_left]
    simp only [Finset.singleton_val, Multiset.map_singleton, Multiset.inf_singleton] at inf
    unfold WithTop.some at inf
    exact Option.some_inj.mp inf
  | cons p _ set conn' _ _ ind h =>
    let k' : ℕ+ := by
      refine ⟨k.val - 1, ?g⟩
      rw [<- card, Finset.card_insert_of_not_mem, Nat.add_one_sub_one]
      apply Connected.nonempty
      repeat assumption
    have : set.card = k' := by
      -- TODO basically same proof as in SMul, use new induction principle to avoid repetition
      unfold k'
      change _ = k.val - 1
      rw [<- card, Finset.card_insert_of_not_mem, Nat.add_one_sub_one]
      assumption
    rw [Finset.insert_val, Multiset.ndinsert_of_not_mem, Multiset.map_cons, Multiset.map_cons,
    Multiset.inf_cons] at inf
    by_cases h' : WithTop.some p.y ≤ some x
    · have := calc
        _ ≤ _ := h'
        _ = _ := symm inf
        _ ≤ _ := by apply inf_le_right
      have := inf_eq_left.mpr this
      rw [inf] at this
      exists p
      constructor
      apply Finset.mem_def.mp
      exact Finset.mem_insert_self p set
      apply WithTop.coe_inj.mp
      rw [<- this]
      rfl
    have h' := lt_of_not_le h'
    suffices h : ∃ a ∈ set.val, a.y = x by
      have ⟨a, a_mem, ayx⟩ := h
      exists a
      constructor
      apply Finset.mem_val.mpr
      exact Finset.mem_insert_of_mem a_mem
      assumption
    apply ind ⟨set, conn', this⟩
    have := calc
      _ = _ := inf
      _ < _ := h'
    have := inf_lt_left.mp this
    have := lt_of_not_le this |> le_of_lt
    have := inf_eq_right.mpr this
    rw [inf] at this
    rw [<- this]
    apply proof_irrel_heq
    repeat assumption

lemma height_min_le_max : m.min_height ≤ m.max_height := by
  have ⟨x, x_inf, xdef⟩ := m.min_height_unpack; subst x
  have ⟨y, y_sup, ydef⟩ := m.max_height_unpack; subst y
  apply WithBot.coe_le_coe.mp
  rw [<- y_sup]
  apply Multiset.le_sup
  apply Multiset.mem_map_of_mem
  exact min_height_mem m

def height := m.max_height - m.min_height |> Int.toNat

@[simp]
lemma height_pos : m.height = m.max_height - m.min_height := by
  unfold height
  simp only [sub_add_cancel, Int.ofNat_toNat]
  apply Int.max_eq_left
  exact Int.sub_nonneg_of_le m.height_min_le_max

theorem height_le_k : m.height ≤ k := by
  apply Int.ofNat_le.mp
  rw [height_pos]
  have ⟨x, x_inf, _⟩ := m.min_height_unpack; subst x
  have ⟨y, y_sup, _⟩ := m.max_height_unpack; subst y
  have ⟨points, conn, card⟩ := m
  induction conn using Connected.induction_nonoverlapping generalizing k with
  | triv => sorry
  | cons => sorry
#print axioms height_le_k

/-- Produces the shape of the given mino -/
def shape : KShape k := ⟦m⟧

end KMino

def Shape.minos {k} (shape : KShape k) : Set (KMino k) := {s | ⟦s⟧ = shape}

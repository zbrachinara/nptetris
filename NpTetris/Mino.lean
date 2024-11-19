import NpTetris.Transform

def one_off' : Set (ℤ × ℤ) := {(1, 0), (0, 1), (-1, 0), (0, -1)}
def one_off : Set Position := { Multiplicative.ofAdd x | x ∈ one_off'}

inductive Connected : Finset Position → Prop where
| triv set : set.card <= 1 → Connected set
| cons point (set' : Finset Position) :
    (∃ point' ∈ set', point⁻¹ * point' ∈ one_off) → Connected (insert point set')

structure Points (size : ℕ) where
  points: Finset Position
  connected: Connected points

/-- Transforming a set of points preserves connectedness -/
instance (size : ℕ): MulAction Transform (Points size) where
smul := sorry
one_smul := sorry
mul_smul := sorry

instance transform_independent (n: _) : Setoid (Points n) where
  r a b := ∃ t : Transform, t • a = b
  iseqv := by
    apply Equivalence.mk
    case refl => sorry
    case symm => sorry
    case trans => sorry

def Shape (n : ℕ) := Quotient (transform_independent n)

structure Mino (n : ℕ) where
  shape : Shape n
  position : Position
  rotation : Rotation

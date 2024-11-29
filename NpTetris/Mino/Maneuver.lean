import NpTetris.Mino.KMino

namespace KMino

variable {k}

/-- A relation between two minos that says that one can be maneuvered into the other. -/
structure ManeuverStep (k₁ k₂ : KMino k) : Prop where
shapes_id : k₁.shape = k₂.shape
touching : ∃ p₁ ∈ k₁.points, ∃ p₂ ∈ k₂.points, p₁ = p₂ ∨ p₁⁻¹ * p₂ ∈ norm_one_offsets

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

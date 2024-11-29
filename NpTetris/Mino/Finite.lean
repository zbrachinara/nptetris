import NpTetris.Mino.KMino
import NpTetris.Mino.LekMino

/-- Takes the mino to the set of minos which can be formed by filling a connected cell -/
def explode {k} : KMino k → List (KMino (k + 1)) := by
  intro ⟨points, connected, boundable⟩
  sorry

def zero_anchored {k} : List (KMino k) := by
  have ⟨k, knz⟩ := k
  induction k using Nat.twoStepInduction
  case zero => exact {} -- will never be encountered, give it a trivial value
  case one =>
    refine [ ?g ]
    constructor
    case points => exact {(0, 0)}
    case connected => apply Connected.triv
    case boundable => simp
  case more n _ prev =>
    have : 0 < n + 1 := by exact Nat.zero_lt_succ n
    have := prev this

    sorry

instance {k} : Finite (KShape k) := by
  apply Set.finite_univ_iff.mp
  
  sorry

instance {k} : Fintype (LeKShape k) := sorry

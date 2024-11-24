import NpTetris.Board
import NpTetris.Proofs.S3_2_TwoColumn.NDPA

def two_column_solutions rows k := {queue | ∃ finish, @LeKTris k 2 rows queue {} finish }

def machine (rows k : ℕ+) : NDPA sorry sorry sorry := sorry
def machine.solutions (rows k : ℕ+) := { s | (machine rows k).accepts s }

/-- Solutions to queues in a two-column LeKTris game are represented by accepted strings in a
  non-deterministic pushdown automaton -/
theorem two_column_is_polynomial rows k :
  Nonempty (machine.solutions rows k ≃ two_column_solutions rows k)
:= by
  sorry

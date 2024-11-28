import NpTetris.Board
import NpTetris.Proofs.S3_2_TwoColumn.NDPA
import NpTetris.Proofs.S3_2_TwoColumn.SolutionNDPA

def two_column_solutions rows k := {queue | ∃ finish, @LeKTris k 2 rows queue {} finish }

def machine_solutions (rows k : ℕ+) := { s | (Solution.machine rows k).accepts s }

/-- Solutions to queues in a two-column LeKTris game are represented by accepted strings in a
  non-deterministic pushdown automaton -/
theorem two_column_is_polynomial rows k :
  Nonempty (machine_solutions rows k ≃ two_column_solutions rows k)
:= by
  sorry

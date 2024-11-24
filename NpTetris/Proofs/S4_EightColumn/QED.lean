import NpTetris.Board
import NpTetris.Proofs.S4_EightColumn.ThreePartition

def tetris_solutions columns rows board := {queue | @KTris 4 columns rows queue board {} }

def partition_problem (rows columns : ℕ+) : ThreePartitionProblem sorry sorry sorry := sorry

/-- Solutions to queues in a 4-tris game with eight or more columns are represented by valid
  3-partitions. -/
theorem eight_column_is_np_hard rows columns : ∃ board,
  Nonempty ((partition_problem rows columns).solutions ≃ tetris_solutions rows columns board)
:= by
  sorry

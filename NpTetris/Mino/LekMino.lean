import NpTetris.Mino.KMino

/-- A type which encompasses all k-minos ≤k -/
structure LeKMino (k : ℕ+) where
  t : ℕ+
  val : KMino t
  isLe : t ≤ k

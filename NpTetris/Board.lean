import NpTetris.Mino

/-- A rectangular playing field with width `n` (`n` columns) and height `m` (`m` rows). Coordinates
  increase from left to right and from bottom to top. -/
abbrev Board (n m : ℕ) := Finset (Fin n × Fin m)

namespace Board

variable {n m : ℕ+}

def position_map : Fin n × Fin m ↪ Position where
toFun := by rintro ⟨p,q⟩; exact ⟨p,q⟩
inj' := by
  intro a b fab
  ext <;> apply Int.ofNat_inj.mp
  · exact congrArg Prod.fst fab
  · exact congrArg Prod.snd fab

def points (board : Board n m) : Finset Position := board.map position_map

inductive lockable {k} (board : Board m n) (mino : KMino k) where
| on_floor p : p ∈ mino.points → p.2 = 0 → lockable board mino
| supported p : p ∈ board.points → p * Multiplicative.ofAdd (0, 1) ∈ mino.points → lockable board mino
-- TODO better notation for position

/-- If these conditions are satisfied, then a mino with this shape can maneuver through the path and
  lock onto the board to step it to the final state -/
structure lock {k} {path : @KMino.Path k} {maneuver : KMino.Maneuver path}
  (shape : KShape k) (initial final : Board n m)
where
/-- No point on the path intersects `initial` -/
no_intersections m : m ∈ path → m.points ∩ initial.points = ∅
/-- No point on the path leaves the board -/
bounded p mino : mino ∈ path → p ∈ mino.points → ∃ fxy : Fin n × Fin m, position_map fxy = p
/-- The shape of the mino described in the maneuver is the one supplied. -/
shape_correct : maneuver.head.shape = shape
/-- The path begins at the top of the board -/
spawn_at_top : maneuver.head.max_height = m
/-- The locking position of the path completes the board -/
diff_correct : maneuver.last.points ∪ initial.points = final.points
/-- The locking position is actually a locking position -/
lockable : initial.lockable maneuver.last

/-- A board can step from initial to final if the final board is a line clear on row `r` -/
structure clear (r) (initial final : Board n m) where
lower_id : ∀ c r', r' < r → (c, r') ∈ initial → (c, r') ∈ final
/-- The rows `r` and above of `initial` should be the same as the -/
upper_shifted : ∀ c r', r' > r → (c, r') ∈ initial → (c, r' - 1) ∈ final
/-- Row `r` in the initial board should be full. -/
r_full : ∀ c, (c, r) ∈ initial
/-- The top of the final board should be empty. -/
top_empty : ∀ c, (c, -1) ∉ final

end Board

/-- A game of k-tris parameterized by its queue, initial state, and final state -/
inductive KTris {k} {n m : ℕ+} : List (KShape k) → Board n m → Board n m → Prop where
/-- An empty queue does nothing -/
| triv board : KTris [] board board
/-- Even without a piece, the board can step if it has a full row -/
| clear queue initial row final : initial.clear row final → KTris queue initial final
/-- If there is a piece in the queue, then it can lock down. -/
| lock shape steps b₁ b₂ b₃ : KTris steps b₁ b₂ → b₂.lock shape b₃ → KTris (shape :: steps) b₁ b₃

/-- A game of ≤k-tris parameterized by its queue, initial state, and final state. Unlike k-tris,
  pieces can be of any size less than `k`, and not just of size `k` itself. -/
inductive LeKTris {k} {n m : ℕ+} : List (LeKShape k) → Board n m → Board n m → Prop where
/-- An empty queue does nothing -/
| triv board : LeKTris [] board board
/-- Even without a piece, the board can step if it has a full row -/
| clear queue initial row final : initial.clear row final → LeKTris queue initial final
/-- If there is a piece in the queue, then it can lock down. This is defined by finding the related
  k-mino, and using that to find out what the final state of the board can be. -/
| lock (lekshape : LeKShape k) kshape steps b₁ b₂ b₃ :
  LeKTris steps b₁ b₂ →
  lekshape.shape_eq kshape →
  b₂.lock kshape b₃ →
  LeKTris (lekshape :: steps) b₁ b₃

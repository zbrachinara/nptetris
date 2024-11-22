import NpTetris.Mino

/-- A rectangular playing field with width `n` (`n` columns) and height `m` (`m` rows). Coordinates
  increase from left to right and from bottom to top. -/
abbrev Board (n m : ℕ) := Finset (Fin n × Fin m)

namespace Board

variable {n m : ℕ}

def position_map : Fin n × Fin m ↪ Position where
toFun := by rintro ⟨p,q⟩; exact ⟨p,q⟩
inj' := by
  intro a b fab
  ext <;> apply Int.ofNat_inj.mp
  · exact congrArg Prod.fst fab
  · exact congrArg Prod.snd fab

def points (board : Board n m) : Finset Position := board.map position_map

/-- The difference between the initial and final board. These are the positions of the board which
  are filled in the final board, but empty in the initial board. Concretely, this is a set
  difference. -/
instance : HSub (Board n m) (Board n m) (Finset Position) where
hSub final initial := (final \ initial).points

/-- If these conditions are satisfied, then a mino with the given shape can step the board from the
  initial state to the final state. -/
structure step {k} {path : @KMino.Path k} {maneuver : KMino.Maneuver path}
  (shape : Shape k) (initial final : Board n m)
where
/-- The difference between the two boards is exactly where the path ends -/
diff_correct : maneuver.last.points = final - initial
/-- The shape of the mino described in the maneuver is exactly the one being considered. -/
shape_correct : maneuver.head.shape = shape
/-- The path begins at the top of the board -/
spawn_at_top : maneuver.last.max_height = m
/-- No point on the path intersects `initial` -/
no_intersections (m : @KMino k) : m ∈ path → m.points ∩ initial.points = ∅

end Board

/-- A game of k-tris parameterized by its queue, initial state, and final state -/
inductive KTris {n m k} : List (Shape k) → Board n m → Board n m → Prop where
| triv board : KTris [] board board
| step shape steps b₁ b₂ b₃ : KTris steps b₁ b₂ → b₂.step shape b₃ → KTris (shape :: steps) b₁ b₃

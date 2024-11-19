import NpTetris.Transform
import NpTetris.Collection


def Vec.map {α β n} (f : α → β) (v : Vec α n) : Vec β n := by
  have ⟨l, H_length⟩ := v
  refine ⟨l.map f, ?g⟩
  rw [List.length_map]
  exact H_length

theorem Vec.map_id {α n} (v : Vec α n) : v.map (fun x ↦ x) = v := by
  unfold map
  simp
  exact rfl

def Points size := Vec Position size

instance {n: _} : Setoid (Points n) where
  r a b := ∃ t : Transform, (a.map (fun p => t • p)).congruent b
  iseqv := by
    apply Equivalence.mk
    case refl =>
      intro x
      exists 1
      simp
      rw [Vec.map_id]
      sorry
    case symm => sorry
    case trans => sorry

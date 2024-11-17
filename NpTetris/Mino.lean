-- import Mathlib.Tactic
-- import Mathlib.Algebra.Group.Defs
-- import Mathlib.Algebra.Group.Fin.Basic
-- import Mathlib.Algebra.Group.Hom.Defs
-- import Mathlib.Algebra.Group.TypeTags
-- import Mathlib.GroupTheory.SemidirectProduct
import Mathlib
import Batteries.Data.List.Lemmas

def Vec α n := { ls : List α // ls.length = n }
def Vec.nil {α} : Vec α 0 := ⟨[], by simp⟩
def Vec.cons {α n} (a : α) (v : Vec α n) : Vec α (n + 1) := ⟨a :: v.val, by simp[v.prop]⟩
infixr: 68 " :: " => Vec.cons

def Vec.destruct_cons {α n} (v : Vec α (n + 1)) : α × (Vec α n) := by
  have nonempty: v.val ≠ [] := by apply List.ne_nil_of_length_pos; simp[v.prop]
  have head := v.val.head nonempty

  let tail := v.val.tail
  have : tail.length = n := by
    apply Nat.add_right_cancel
    rw [List.length_tail_add_one] <;> simp[v.prop]

  exact ⟨head, ⟨tail, this⟩⟩

def Vec.tail {α n} (v : Vec α (n + 1)) : Vec α n := ⟨v.val.tail, by simp[v.prop]⟩
def Vec.ins {α n} (a : α) (v : Vec α n) (position : Fin n) : Vec α (n + 1) :=
match position with
| ⟨0, _⟩ => a :: v
| ⟨Nat.succ pos, p⟩ => by
  induction n with
  | zero => have ⟨_, _⟩ := position; linarith
  | succ x _ =>
    have ⟨head, tail⟩ := Vec.destruct_cons v
    refine head :: Vec.ins a tail ⟨pos, ?g⟩
    apply Nat.lt_of_add_lt_add_right
    apply p

/-- Equality that does not care about order of elements -/
inductive Vec.Congruent {α} : {n: Nat} → (p1 : Vec α n) → (p2 : Vec α n) → Prop where
| triv p1 p2 : @Congruent α 0 p1 p2
| cons a ix p1 p2 : Congruent p1 p2 → Congruent (a :: p1) (p2.ins a ix)


/-- Defines an action on ℤ × ℤ in the usual way -/
structure Transform where
  position : ℤ × ℤ
  rotation : Fin 4
def Transform.mul (t₁ t₂ : Transform) : Transform :=
  let ⟨x₂, y₂⟩ := t₂.position
  let pos₂' : ℤ × ℤ := match t₁.rotation with
  | 0 => ⟨x₂, y₂⟩
  | 1 => ⟨-y₂, x₂⟩
  | 2 => ⟨-x₂, -y₂⟩
  | 3 => ⟨y₂, -x₂⟩
  ⟨t₁.position + pos₂', t₁.rotation + t₂.rotation⟩
instance : Mul Transform where
mul := Transform.mul
-- mul t₁ t₂ := by
--   have ⟨x₂, y₂⟩ := t₂.position
--   have pos₂' : Coord := match t₁.rotation with
--   | 0 => ⟨x₂, y₂⟩
--   | 1 => ⟨-y₂, x₂⟩
--   | 2 => ⟨-x₂, -y₂⟩
--   | 3 => ⟨y₂, -x₂⟩
--   exact ⟨t₁.position + pos₂', t₁.rotation + t₂.rotation⟩

instance : AddGroup (Fin 4) := by infer_instance


/--
This is basically (ℤ × ℤ) ⋊ ℤ₄. I couldn't figure out semidirect products for additive groups, so I
will define it manually.

Maybe someday TODO show an isomorphism between this and that.
-/
instance : Group Transform where
mul_assoc := by
  rintro ⟨p₁, r₁⟩ ⟨p₂, r₂⟩ ⟨p₃, r₃⟩

  sorry
one := ⟨0, 0⟩
one_mul := by
  rintro ⟨p, r⟩


  sorry
mul_one := sorry
inv := sorry
inv_mul_cancel := sorry


def Points size := Vec (ℤ × ℤ) size

instance (n: _) : Setoid (Points n) where
  r a b := sorry
  iseqv := sorry

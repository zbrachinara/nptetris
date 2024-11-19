import Mathlib
import Batteries.Data.List.Lemmas

def Vec α n := { ls : List α // ls.length = n }

namespace Vec
def nil {α} : Vec α 0 := ⟨[], by simp⟩
def cons {α n} (a : α) (v : Vec α n) : Vec α (n + 1) := ⟨a :: v.val, by simp[v.prop]⟩
infixr: 68 " :: " => cons

def ind_together {α} {n : Nat} {M : (n : ℕ) → Vec α n → Sort*}
  (m_nil : M 0 nil)
  (m_cons : ∀ (n : ℕ) (a : α) (v : Vec α n), M n v → M (n + 1) (a :: v)) :
  ∀ (v : Vec α n), M n v
:= by
  intro v
  induction n
  case zero =>
    have ⟨p, q⟩ := v
    induction p
    case nil => apply m_nil
    case cons head tail _ =>
      have : (head :: tail).length > 0 := by exact Nat.zero_lt_succ tail.length
      linarith
  case succ n' provider_v' =>
    have ⟨p, q⟩ := v
    induction p
    case nil =>
      have : ([] : List α).length = 0 := rfl
      linarith
    case cons head tail _ =>
      let tailv : Vec α n' := ⟨tail, Nat.succ_inj'.mp q⟩
      have prev := provider_v' tailv
      exact m_cons n' head tailv prev

def destruct_cons {α n} (v : Vec α (n + 1)) : α × (Vec α n) := by
  have nonempty: v.val ≠ [] := by apply List.ne_nil_of_length_pos; simp[v.prop]
  have head := v.val.head nonempty

  let tail := v.val.tail
  have : tail.length = n := by
    apply Nat.add_right_cancel
    rw [List.length_tail_add_one] <;> simp[v.prop]

  exact ⟨head, ⟨tail, this⟩⟩

def tail {α n} (v : Vec α (n + 1)) : Vec α n := ⟨v.val.tail, by simp[v.prop]⟩
def ins {α n} (a : α) (v : Vec α n) (position : Fin (n + 1)) : Vec α (n + 1) :=
match position with
| ⟨0, _⟩ => a :: v
| ⟨Nat.succ pos, p⟩ => by
  induction n with
  | zero => have ⟨_, _⟩ := position; linarith
  | succ x _ =>
    have ⟨head, tail⟩ := destruct_cons v
    refine head :: ins a tail ⟨pos, ?g⟩
    apply Nat.lt_of_add_lt_add_right
    apply p

theorem ins_at_zero {α n} (a : α) (v : Vec α n) : a :: v = v.ins a 0 := by
  unfold ins
  congr

/-- Equality that does not care about order of elements -/
inductive congruent {α} : {n: Nat} → (p1 : Vec α n) → (p2 : Vec α n) → Prop where
| triv n p1 p2 : n = 0 → @congruent α n p1 p2
| cons a ix p1 p2 : congruent p1 p2 → congruent (a :: p1) (p2.ins a ix)

instance {α} {n : _} : Setoid (Vec α n) where
r p q := p.congruent q
iseqv := by
  apply Equivalence.mk
  case refl =>
    intro x
    induction x using ind_together
    case m_nil =>
      apply congruent.triv
      rfl
    case m_cons n' h t rec_congruence =>
      conv =>
        rhs
        rw [ins_at_zero]
      apply congruent.cons
      exact rec_congruence
  case symm => sorry
  case trans => sorry

end Vec
import Mathlib.Data.Fin.Fin2

import NpTetris.Proofs.S3_2_TwoColumn.NDPA
import NpTetris.Mino

namespace Solution

/--
This type acts as the stack language of the equivalent NDPA to a two-column $≤k$-tris game. They are
one-to-one with the state of a $k$-tris "stack", the shape that the filled cells on a board form. To
see this, let `Left` represent rows where the left column is filled, `Right` represent the same for
the right column.

For any $k$-tris stack, there must be a contiguous range of rows starting from the bottom and going
up to a maximum height where all the rows are either filled on the left and right column, and all
other rows are empty. If, for example, there was an empty row separating two such contiguous ranges,
this would imply that there is a placement which was anchored on nothing. But this is impossible by
the definition of $≤k$-tris, so such a situation cannot happen. A full row is irrelevant because it
can be eliminated with a line clear.
-/
inductive FilledColumn where
| Left
| Right
deriving DecidableEq

instance : Fintype FilledColumn where
elems := { FilledColumn.Left, FilledColumn.Right }
complete p := by cases p <;> simp

inductive State (rows k : ℕ+) where
/--
In this state, the machine is in the process of resolving the state of the board after locking a
piece. Here are the parts of this state:
- The number of rows currently filled. Once this grows so large that the next piece cannot be
  spawned, the machine transitions to the failure state (`none`).
- The row-wise residue of the piece, from the bottom (the side closer to the bottom of the board) to
  the top. While a piece's residue needs not be connected, rows which are full must still be
  represented, because they will act like a "rim" which stops the piece from clearing any more
  lines. As an example, think about an s/z piece in 2-column 4-tris.

  This residue is used to decide whether a row can be cleared. If the next residue is the opposite
  of the next stack symbol (that is, if the left and right column interlock to fill a row), then the
  residue is popped and the process repeats again. If the next residue is not the opposite of the
  next stack symbol, then the residue is pushed onto the stack. Note that rows of residue which are
  entirely filled are `none`.
- There are at most `k` rows of residue to consider, corresponding to the smallest bounding box
  containing all spawnable $≤k$-minos. This puts a finite bound on the number of states, which is
  required to show that an algorithm for acceptability is polynomial.
-/
| resolving (filled : Fin rows) (residue : List (Option FilledColumn)) (rlen: residue.length ≤ k)
/--
In this state, the board is ready to receive the next piece in the queue. The number of rows is
recorded so that the machine can decide to terminate.
-/
| ready (filled : Fin rows)
deriving DecidableEq

def List.rec_univ {α} [Fintype α] [DecidableEq α] (k: ℕ) : Finset (List α) := by
  induction k
  case zero => exact {[]}
  case succ k s =>
    refine s ∪ ?new
    apply Finset.map
    case s => exact (@Finset.univ α _).product s
    constructor
    case toFun =>
      intro ⟨a,xs⟩
      refine a :: xs
    intro p q
    rw [List.cons.injEq]
    rintro ⟨a,b⟩
    ext
    assumption
    rw [b]

theorem List.rec_univ_finite {α k} [Fintype α] [DecidableEq α]:
  ∀ x : List α, x ∈ List.rec_univ k → x.length ≤ k
:= by
  unfold rec_univ
  unfold Nat.recAux
  induction k
  · intro x k
    apply Nat.le_of_eq
    apply List.length_eq_zero.mpr
    apply Finset.eq_of_mem_singleton
    assumption
  case _ n ind =>
  intro ls k
  simp only [Nat.rec] at k
  cases Finset.mem_union.mp k
  case inr k =>
    have ⟨_, ⟨ls_length, ls_a_x⟩⟩ := Finset.mem_map.mp k
    have ⟨ls_length, _⟩ := Finset.mem_product.mp ls_length
    rw [<- ls_a_x]
    apply Nat.add_le_add_right
    apply ind
    assumption
  case inl k =>
    have := ind ls k
    exact Nat.le_add_right_of_le (ind ls k)

theorem List.rec_univ_finite' {α k} [Fintype α] [DecidableEq α]:
  ∀ x : List α, x.length ≤ k → x ∈ List.rec_univ k
:= by
  unfold rec_univ
  unfold Nat.recAux
  induction k; simp
  case _ n ind =>
  intro ls ls_len
  apply Finset.mem_union.mpr
  cases Nat.decLt ls.length (n + 1)
  case isFalse h =>
    right
    push_neg at h
    have : 1 ≤ ls.length := by exact Nat.one_le_of_lt h
    have : ls ≠ [] := by exact List.ne_nil_of_length_pos this
    rw [Finset.mem_map, Prod.exists]
    let head := ls.head this
    exists head
    exists ls.tail
    constructor
    · apply Finset.mem_product.mpr
      simp only [Finset.mem_univ, true_and]
      apply ind
      apply @Nat.le_of_add_le_add_right _ 1
      rw [List.length_tail, Nat.sub_add_cancel]
      repeat assumption
    · apply List.head_cons_tail
  case isTrue h =>
    left
    apply ind
    exact Nat.le_of_lt_succ h

def Fin.all {n} : Finset (Fin n) := by
  induction n
  case zero => exact {}
  case succ n ind =>
    refine Finset.cons n ?set ?prf
    · apply ind.map
      constructor
      case toFun => exact Fin.castSucc
      intro p q pq
      exact Fin.castSucc_inj.mp pq
    · intro neg
      have ⟨a, ⟨contra1, contra2⟩⟩ := Finset.mem_map.mp neg
      simp at contra2
      apply Fin.exists_castSucc_eq.mp
      exists a
      assumption

instance Fin.instFintypeNoChoice {n} : Fintype (Fin n) where
elems := Fin.all
complete := by
  unfold Fin.all
  unfold Nat.recAux
  induction n; simp
  case _ a ind =>
  intro x
  apply Finset.mem_cons.mpr
  cases (Nat.decLt x.val a)
  case isFalse h =>
    push_neg at h
    left
    rw [<- Fin.cast_val_eq_self x]
    congr
    symm
    apply Nat.le_antisymm h
    apply Fin.is_le
  case isTrue h =>
    right
    apply Finset.mem_map.mpr
    exists ⟨x.val, h⟩
    constructor
    apply ind
    simp only [Function.Embedding.coeFn_mk, Fin.castSucc_mk, Fin.eta]

instance instFinState {rows k} : Fintype (State rows k) where
elems := by
  refine ?resolving ∪ ?ready
  · have row_count : Finset (Fin rows) := Finset.univ
    let residue : Finset (List (Option FilledColumn)) := List.rec_univ k
    apply Finset.map
    case s => exact row_count.product residue.attach
    constructor
    case toFun =>
      intro ⟨f, ⟨g, g_residue⟩⟩
      exact State.resolving f g (List.rec_univ_finite g g_residue)
    intro p q
    intro pq
    injection pq with _ k
    ext
    · congr
    · rw [k]
  · apply Finset.map
    constructor
    case toFun => intro rows; exact State.ready rows
    intros _ ; simp
    exact Finset.univ
complete x := by
  simp only [Finset.mem_union, Finset.mem_map, Function.Embedding.coeFn_mk, Prod.exists,
    Subtype.exists, Finset.mem_univ, true_and]
  cases x
  case resolving filled residue rlen =>
    left
    exists filled
    exists residue
    exists List.rec_univ_finite' residue rlen
    constructor
    · apply Finset.mem_product.mpr
      simp only [Finset.mem_univ, Finset.mem_attach, and_self]
    · rfl
  case ready filled =>
    right
    exists filled

/-- Explanation of the types given to the NDPA:

- **Stack**: See [FilledColumn]
- **String**: The strings that the NDPA accepts are exactly piece queues, no suprises there.
- **State**: See [State]
-/
def machine (rows k: ℕ+) : NDPA (Option FilledColumn) (LeKShape k) (State rows k) where
-- start with an empty board
initial := {State.ready 0}
initial_stack := none
-- Once the queue is exhausted it doesn't matter whether or not a piece can be spawned
accept x := ∃ k, x = State.ready k
step state row shape := match (state, row, shape) with
| (State.ready k, stack_top, some piece) => by
  sorry
| (State.resolving filled residue rlen, _, none) => sorry
| (_, _, _) => {} -- no available transitions

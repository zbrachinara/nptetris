import NpTetris.Proofs.S3_2_TwoColumn.NDPA
import NpTetris.Mino.LekMino

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
recorded so that the machine knows whether to transition to the terminal state.
-/
| ready (filled : Fin rows)

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
finite := by
  constructor
  case elems => sorry
  case complete => sorry
step state row shape := match (state, row, shape) with
| (State.ready k, stack_top, some piece) => by
  sorry
| (State.resolving filled residue rlen, _, none) => sorry
| (_, _, _) => {} -- no available transitions

#print axioms machine

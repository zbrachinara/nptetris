import Mathlib.Data.Set.Defs
import Mathlib.Data.Fintype.Powerset

/-- Non-deterministic Pushdown Automaton. Not (yet) translatable to or from mathlib's NFA. For that
  we need to encode that the stack will always have an element to step with -/
structure NDPA (Stack_α String_α State: Type) where
initial : Set State
initial_stack : Stack_α
accept : Set State
step : State → Stack_α → String_α → Set (State × List Stack_α)

namespace NDPA

variable {Stack_α String_α State} {M : NDPA Stack_α String_α State}

inductive accepts' : State → List Stack_α → List String_α → Prop
where
| term stack state : state ∈ M.accept → accepts' state stack []
| step stack_a string_a stack string state state' stack' :
  accepts' state' (stack' ++ stack) string →
  (state', stack') ∈ M.step state stack_a string_a →
  accepts' state (stack_a :: stack) (string_a :: string)

def accepts (string : List String_α) := ∃ s ∈ M.initial, M.accepts' s [M.initial_stack] string

end NDPA

import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Fold

structure ThreePartitionProblem (size : ℕ) (int_set : Multiset ℕ) (T : ℕ) where
set_size : int_set.card = 3 * size
partitionable : int_set.sum = size * T
normal x : x ∈ int_set → T / 4 < x ∧ x < T / 2

namespace ThreePartitionProblem

variable {size int_set T} (problem : ThreePartitionProblem size int_set T)

structure solution (problem : ThreePartitionProblem size int_set T) where
part : List (ℕ × ℕ × ℕ)
partition_valid : part.foldr (λ ⟨a,b,c⟩ x ↦ {a,b,c} ∪ x) ∅ = int_set
partitions_sum x y z : ⟨x,y,z⟩ ∈ part → x + y + z = T

def solutions := { x | ∃ sol : problem.solution, x = sol.part }

def partition_exists := Inhabited problem.solution

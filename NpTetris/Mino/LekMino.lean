import NpTetris.Mino.KMino

/-- A type which encompasses all k-minos ≤k -/
@[ext]
structure LeKMino (k : ℕ+) where
  t : Fin k
  val : KMino ⟨t + 1, by apply Nat.zero_lt_succ⟩

instance LeKMino.instSMul (bound) : SMul Transform (LeKMino bound) where
smul a b := by
  constructor
  exact a • b.val

#print axioms LeKMino.instSMul

@[simp]
theorem lower_lekmino_val {b} (t : Transform) (p : LeKMino b) :
  (t • p).val = t • p.val := rfl

instance {b} : MulAction Transform (LeKMino b) where
one_smul _ := by
  ext; rfl
  rw [heq_eq_eq]
  ext; rw [lower_lekmino_val, one_smul]
mul_smul a b x := by
  ext; rfl
  rw [heq_eq_eq]
  repeat rw [lower_lekmino_val]
  rw [mul_smul]

def LeKShape (bound) := orbit_quotient Transform (LeKMino bound)

def LeKMino.shape {k} (mino : LeKMino k) : LeKShape k := Quotient.mk _ mino

def LeKShape.t {b} (shape : LeKShape b) : Fin b := by
  apply shape.lift
  case f => intro x; exact x.t
  intro p q pq
  cases pq with | intro t eq =>
  rw [<- eq]
  rfl

def LeKShape.minos {k} (shape : LeKShape k) : Set (LeKMino k) := {s | ⟦s⟧ = shape}


/-- There exist two minos which are absolutely identical, relating the shapes in each type -/
structure LeKShape.shape_eq {k k'} {lekmino : LeKMino k'} {kmino : KMino k}
  (leks: LeKShape k') (ks : KShape k) : Prop
where
shapes_id : lekmino.val.points = kmino.points
shape_lek : ⟦lekmino⟧ = leks
shape_k : ⟦kmino⟧ = ks

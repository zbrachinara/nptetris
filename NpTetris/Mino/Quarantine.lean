import Mathlib.Tactic

/-!
Gets rid of the usages of the choice axiom
-/

lemma int_square_one {x : ℤ} : x ^ 2 = 1 ↔ x = -1 ∨ x = 1 := by
  constructor
  · intro sq
    rw [pow_two] at sq
    by_cases h : x ≤ 0
    · left
      rw [<- Int.neg_mul_neg] at sq
      have : -x = 1 := by
        refine Int.eq_one_of_mul_eq_one_right ?h sq
        rw [<- Int.neg_zero]
        apply Int.neg_le_neg
        assumption
      exact Int.eq_neg_comm.mp (id (Eq.symm this))
    · right
      refine Int.eq_one_of_mul_eq_one_right ?h sq
      apply le_of_lt
      exact Int.lt_of_not_ge h
  · rintro (_ | _) <;> (subst x ; rfl)

lemma int_square_zro {x : ℤ} : x ^ 2 = 0 ↔ x = 0 := by
  constructor
  · intro sq
    rw [pow_two] at sq
    have := Int.mul_eq_zero.mp sq
    rw [or_self] at this
    assumption
  · intros ; subst x; rfl

lemma int_square_nonneg (x : ℤ) : 0 ≤ x ^ 2 := by
  rw [pow_two]
  cases x
  · apply Int.mul_nonneg <;> apply Int.zero_le_ofNat
  · apply le_of_lt; apply Int.mul_pos_of_neg_of_neg <;> apply Int.negSucc_lt_zero

lemma int_square_le_one {x : ℤ} : x ^ 2 ≤ 1 ↔ x = 0 ∨ x = -1 ∨ x = 1 := by
  constructor
  · intro le1
    have := int_square_nonneg x
    have : x^2 = 0 ∨ x^2 = 1 := by
      by_cases h : x^2 ≤ 0
      · left
        exact Eq.symm (Int.le_antisymm this h)
      · right
        push_neg at h
        exact Eq.symm (Int.le_antisymm h le1)
    cases this
    · left; apply int_square_zro.mp; assumption
    · right; apply int_square_one.mp; assumption
  · rintro (h | h)
    · calc
        _ = _ := int_square_zro.mpr h
        _ ≤ _ := Int.one_nonneg
    · calc
        _ = _ := int_square_one.mpr h
        _ ≤ _ := Int.le_refl 1

lemma int_square {x y : ℤ} : x^2 + y^2 = 1 → x = 0 ∨ x = -1 ∨ x = 1 := by
  intro xy_norm
  have : 0 ≤ y^2 := by
    cases y <;> rw [pow_two]
    · apply Int.mul_nonneg <;> apply Int.zero_le_ofNat
    · apply Int.le_of_lt; apply Int.mul_pos_of_neg_of_neg <;> apply Int.negSucc_lt_zero
  have sqx_le1: x^2 ≤ 1 := by
    by_cases h : x^2 ≤ 1
    · assumption
    · push_neg at h
      have : 1 < x^2 + y^2 := by exact lt_add_of_lt_of_nonneg h this
      rw [xy_norm] at this
      cases this
  apply int_square_le_one.mp
  apply sqx_le1

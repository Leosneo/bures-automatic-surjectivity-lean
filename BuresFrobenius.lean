import BuresTriangle

/-! Frobenius norm estimates for Gram matrices. The Frobenius norm is used only
on factors; it is not substituted for the Bures distance on positive matrices. -/

noncomputable section
open scoped MatrixOrder ComplexOrder Matrix.Norms.Frobenius
namespace Bures

theorem frobenius_sq_eq_tr_gram (S : Mat n) : ‖S‖ ^ 2 = tr (S * S.conjTranspose) := by
  rw [frobenius_norm_eq_sqrt_tr_gram, Real.sq_sqrt
    (tr_nonneg (Matrix.posSemidef_self_mul_conjTranspose S))]

theorem frobenius_gram_difference_le (S T : Mat n) :
    ‖S * S.conjTranspose - T * T.conjTranspose‖ ≤ (‖S‖ + ‖T‖) * ‖S - T‖ := by
  have he : S * S.conjTranspose - T * T.conjTranspose =
      S * (S - T).conjTranspose + (S - T) * T.conjTranspose := by
    rw [Matrix.conjTranspose_sub]
    noncomm_ring
  rw [he]
  calc
    _ ≤ ‖S * (S - T).conjTranspose‖ + ‖(S - T) * T.conjTranspose‖ := norm_add_le _ _
    _ ≤ ‖S‖ * ‖(S - T).conjTranspose‖ + ‖S - T‖ * ‖T.conjTranspose‖ :=
      add_le_add (Matrix.frobenius_norm_mul _ _) (Matrix.frobenius_norm_mul _ _)
    _ = (‖S‖ + ‖T‖) * ‖S - T‖ := by
      rw [Matrix.frobenius_norm_conjTranspose, Matrix.frobenius_norm_conjTranspose]
      ring

/-- The Bures distance controls ordinary matrix convergence on trace-bounded sets. -/
theorem frobenius_sub_le_distance (A B : PositiveDefinite n) :
    ‖A.val - B.val‖ ≤ (Real.sqrt (tr A.val) + Real.sqrt (tr B.val)) * distance A B := by
  obtain ⟨U, _, hUr, hd⟩ := distance_eq_frobenius_unitary A B
  have hA : matrixSqrt A.val * (matrixSqrt A.val).conjTranspose = A.val := by
    rw [(Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg A.val)).isHermitian.eq]
    exact matrixSqrt_mul_self A.property.posSemidef
  have hB : (matrixSqrt B.val * U) * (matrixSqrt B.val * U).conjTranspose = B.val := by
    rw [Matrix.conjTranspose_mul]
    simp only [mul_assoc]
    rw [← mul_assoc U U.conjTranspose, hUr, one_mul,
      (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg B.val)).isHermitian.eq]
    exact matrixSqrt_mul_self B.property.posSemidef
  have h := frobenius_gram_difference_le (matrixSqrt A.val) (matrixSqrt B.val * U)
  rw [hA, hB, ← hd, frobenius_norm_eq_sqrt_tr_gram (matrixSqrt A.val),
    frobenius_norm_eq_sqrt_tr_gram (matrixSqrt B.val * U), hA, hB] at h
  exact h

#print axioms frobenius_gram_difference_le
#print axioms frobenius_sub_le_distance
end Bures

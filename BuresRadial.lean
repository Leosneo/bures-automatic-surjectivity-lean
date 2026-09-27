import Bures

noncomputable section
open scoped MatrixOrder ComplexOrder
namespace Bures

lemma tr_nonneg {A : Mat n} (hA : A.PosSemidef) : 0 ≤ tr A :=
  (Complex.nonneg_iff.mp hA.trace_nonneg).1

lemma tr_smul (c : ℝ) (A : Mat n) : tr (c • A) = c * tr A := by
  simp [tr, Matrix.trace, Matrix.diag, Finset.mul_sum, Complex.re_sum]

lemma matrixSqrt_smul {A : Mat n} (hA : A.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    matrixSqrt (c • A) = Real.sqrt c • matrixSqrt A := by
  apply matrixSqrt_unique
  · exact Matrix.nonneg_iff_posSemidef.mp
      (smul_nonneg (Real.sqrt_nonneg c) (matrixSqrt_nonneg A))
  · rw [smul_mul_smul_comm, matrixSqrt_mul_self hA, Real.mul_self_sqrt hc]

/-- Scaling the underlying matrix by a positive real preserves definiteness. -/
def scale (c : ℝ) (hc : 0 < c) (A : PositiveDefinite n) : PositiveDefinite n :=
  ⟨c • A.val, A.property.smul hc⟩

lemma fidelityRoot_self (A : PositiveDefinite n) : fidelityRoot A.val A.val = tr A.val := by
  have h := matrixSqrt_mul_self A.property.posSemidef
  have hs : matrixSqrt A.val * A.val * matrixSqrt A.val = A.val * A.val := by
    calc
      _ = matrixSqrt A.val * (matrixSqrt A.val * matrixSqrt A.val) *
          matrixSqrt A.val := congrArg
            (fun X : Mat n => matrixSqrt A.val * X * matrixSqrt A.val) h.symm
      _ = (matrixSqrt A.val * matrixSqrt A.val) *
          (matrixSqrt A.val * matrixSqrt A.val) := by simp only [mul_assoc]
      _ = A.val * A.val := by rw [h]
  unfold fidelityRoot
  rw [hs, matrixSqrt_unique A.property.posSemidef rfl]

lemma fidelityRoot_smul_right (A B : PositiveDefinite n) {c : ℝ} (hc : 0 ≤ c) :
    fidelityRoot A.val (c • B.val) = Real.sqrt c * fidelityRoot A.val B.val := by
  unfold fidelityRoot
  rw [mul_smul_comm, smul_mul_assoc, matrixSqrt_smul (sandwich_posSemidef A B) hc,
    tr_smul]

/-- Along a radial ray the Bures distance is Euclidean in square-root radius. -/
theorem distance_scale (A : PositiveDefinite n) {c : ℝ} (hc : 0 < c) :
    distance A (scale c hc A) = |1 - Real.sqrt c| * Real.sqrt (tr A.val) := by
  unfold distance
  change Real.sqrt (tr A.val + tr (c • A.val) - 2 * fidelityRoot A.val (c • A.val)) = _
  rw [tr_smul, fidelityRoot_smul_right A A hc.le, fidelityRoot_self]
  have hsq := Real.sq_sqrt hc.le
  have heq : tr A.val + c * tr A.val - 2 * (Real.sqrt c * tr A.val) =
      (1 - Real.sqrt c)^2 * tr A.val := by nlinarith [congrArg (fun x : ℝ => x * tr A.val) hsq]
  rw [heq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

#print axioms distance_scale
end Bures

import BuresMetricTangents

/-! The infinitesimal Bures quadratic form has exact degree -1 under radial
scaling of the base matrix with the tangent held fixed. -/
noncomputable section
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator Matrix.Norms.Frobenius
namespace Bures

theorem sylvester_generator_rescale (A X K : Mat n) (c : ℝ) (hc : c ≠ 0)
    (hK : K * A + A * K = X) :
    (c⁻¹ • K) * (c • A) + (c • A) * (c⁻¹ • K) = X := by
  have h1 : (c⁻¹ • K) * (c • A) = K * A := by
    rw [smul_mul_smul_comm, inv_mul_cancel₀ hc]; exact one_smul ℝ (K * A)
  have h2 : (c • A) * (c⁻¹ • K) = A * K := by
    rw [smul_mul_smul_comm, mul_inv_cancel₀ hc]; exact one_smul ℝ (A * K)
  rw [h1, h2]
  exact hK

theorem metric_quadratic_rescale (X K : Mat n) (c : ℝ) :
    tr (X * (c • K)) / 2 = c * (tr (X * K) / 2) := by
  rw [mul_smul_comm, tr_smul]
  ring

/-- Under `A ↦ cA`, the same tangent X has a horizontal generator `K/c`
and its quadratic metric speed scales by `1/c`. -/
theorem horizontal_metric_homogeneity (A X K : Mat n) (c : ℝ) (hc : 0 < c)
    (hK : K * A + A * K = X) :
    (c⁻¹ • K) * (c • A) + (c • A) * (c⁻¹ • K) = X ∧
      tr (X * (c⁻¹ • K)) / 2 = (1 / c) * (tr (X * K) / 2) := by
  constructor
  · exact sylvester_generator_rescale A X K c hc.ne' hK
  · rw [metric_quadratic_rescale]
    ring

#print axioms horizontal_metric_homogeneity
end Bures

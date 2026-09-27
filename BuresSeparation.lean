import BuresFrobenius
import BuresTriangle
import BuresPSD
noncomputable section
open scoped MatrixOrder ComplexOrder Matrix.Norms.Frobenius
open Matrix Filter Topology
namespace Bures

theorem frobenius_sub_le_psdDistance (A B : PSD n) :
    ‖A.val - B.val‖ ≤ (Real.sqrt (tr A.val) + Real.sqrt (tr B.val)) * psdDistance A B := by
  have hA := tendsto_regularize A
  have hB := tendsto_regularize B
  have hAv := tendsto_subtype_rng.mp hA
  have hBv := tendsto_subtype_rng.mp hB
  have hleft := (hAv.sub hBv).norm
  have htA := (continuous_tr.tendsto A.val |>.comp hAv).sqrt
  have htB := (continuous_tr.tendsto B.val |>.comp hBv).sqrt
  have hf := continuous_fidelityRoot_psd.tendsto (A, B) |>.comp (hA.prodMk_nhds hB)
  have htrA := continuous_tr.tendsto A.val |>.comp hAv
  have htrB := continuous_tr.tendsto B.val |>.comp hBv
  have hdist := (htrA.add htrB |>.sub ((tendsto_const_nhds (x := (2 : ℝ))).mul hf)).sqrt
  exact le_of_tendsto_of_tendsto hleft ((htA.add htB).mul hdist)
    (Filter.Eventually.of_forall fun m => frobenius_sub_le_distance (regularize A m) (regularize B m))

/-- The literal formula separates positive semidefinite matrices, including singular ones. -/
theorem psdDistance_eq_zero_imp (A B : PSD n) (h : psdDistance A B = 0) : A = B := by
  have hb := frobenius_sub_le_psdDistance A B
  rw [h, mul_zero] at hb
  exact Subtype.ext (sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))))

#print axioms psdDistance_eq_zero_imp
end Bures

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-! Compactness of actual positive-semidefinite trace sublevels in the ordinary
matrix topology. No Bures metric or trace preservation is assumed or proved here. -/

noncomputable section
open scoped MatrixOrder ComplexOrder Matrix.Norms.Elementwise
namespace BuresSupport

abbrev CMat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

local instance (n : ℕ) :
    NonUnitalContinuousFunctionalCalculus ℝ (CMat n) IsSelfAdjoint :=
  ContinuousFunctionalCalculus.toNonUnital

local instance (n : ℕ) : NonnegSpectrumClass ℝ (CMat n) :=
  Matrix.instNonnegSpectrumClass

def gramEnergy (S : CMat n) : ℝ := ∑ i, ∑ j, ‖S i j‖ ^ 2

theorem gramEnergy_nonneg (S : CMat n) : 0 ≤ gramEnergy S := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

theorem continuous_gramEnergy : Continuous (gramEnergy (n := n)) := by
  unfold gramEnergy
  fun_prop

theorem entry_sq_le_gramEnergy (S : CMat n) (i j : Fin n) :
    ‖S i j‖ ^ 2 ≤ gramEnergy S := by
  exact (Finset.single_le_sum (fun k _ => sq_nonneg ‖S i k‖) (Finset.mem_univ j)).trans
    (Finset.single_le_sum
      (fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg ‖S k l‖) (Finset.mem_univ i))

theorem isCompact_gramEnergy_sublevel (R : ℝ) :
    IsCompact {S : CMat n | gramEnergy S ≤ R} := by
  by_cases hR : 0 ≤ R
  · apply (isCompact_closedBall (0 : CMat n) (Real.sqrt R)).of_isClosed_subset
      (isClosed_le continuous_gramEnergy continuous_const)
    intro S hS
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro j
    exact (Real.le_sqrt (norm_nonneg _) hR).mpr ((entry_sq_le_gramEnergy S i j).trans hS)
  · have he : {S : CMat n | gramEnergy S ≤ R} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro S hS
      exact hR ((gramEnergy_nonneg S).trans hS)
    rw [he]
    exact isCompact_empty

theorem trace_gram (S : CMat n) :
    (Matrix.trace (S * S.conjTranspose)).re = gramEnergy S := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    gramEnergy, Complex.mul_conj, Complex.sq_norm]

theorem trace_sublevel_eq_gram_image (R : ℝ) :
    {A : CMat n | A.PosSemidef ∧ (Matrix.trace A).re ≤ R} =
    (fun S : CMat n => S * S.conjTranspose) '' {S | gramEnergy S ≤ R} := by
  ext A
  constructor
  · rintro ⟨hA, ht⟩
    let S : CMat n := CFC.sqrt A
    have hS : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
    have hsq : S * S.conjTranspose = A := by
      rw [hS.isHermitian.eq]
      exact CFC.sqrt_mul_sqrt_self A hA.nonneg
    refine ⟨S, ?_, hsq⟩
    change gramEnergy S ≤ R
    rw [← trace_gram, hsq]
    exact ht
  · rintro ⟨S, hS, rfl⟩
    exact ⟨Matrix.posSemidef_self_mul_conjTranspose S, by rwa [trace_gram]⟩

theorem isCompact_psd_trace_sublevel (n : ℕ) (R : ℝ) :
    IsCompact {A : CMat n | A.PosSemidef ∧ (Matrix.trace A).re ≤ R} := by
  rw [trace_sublevel_eq_gram_image]
  exact (isCompact_gramEnergy_sublevel R).image (by fun_prop)

#print axioms isCompact_psd_trace_sublevel

end BuresSupport

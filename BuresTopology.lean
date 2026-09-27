import Bures
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-! Continuity in the ordinary finite-dimensional matrix topology. This file
does not install a metric instance or assert equivalence with a quotient metric. -/

noncomputable section
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace Bures

local instance (n : ℕ) : CStarAlgebra (Mat n) where

local instance (n : ℕ) :
    NonUnitalContinuousFunctionalCalculus ℝ (Mat n) IsSelfAdjoint :=
  ContinuousFunctionalCalculus.toNonUnital
local instance (n : ℕ) : NonnegSpectrumClass ℝ (Mat n) :=
  Matrix.instNonnegSpectrumClass

theorem continuousOn_matrixSqrt :
    ContinuousOn (matrixSqrt (n := n)) {A | A.PosSemidef} := by
  simpa only [matrixSqrt, Matrix.nonneg_iff_posSemidef] using
    (CFC.continuousOn_sqrt (A := Mat n))

theorem continuous_matrixSqrt_psd :
    Continuous (fun A : {A : Mat n // A.PosSemidef} => matrixSqrt A.val) :=
  continuousOn_matrixSqrt.restrict

theorem continuous_tr : Continuous (tr (n := n)) := by
  unfold tr Matrix.trace Matrix.diag
  fun_prop

theorem continuous_fidelityRoot_psd :
    Continuous (fun p : {A : Mat n // A.PosSemidef} × {A : Mat n // A.PosSemidef} =>
      fidelityRoot p.1.val p.2.val) := by
  have hsq := continuous_matrixSqrt_psd (n := n)
  have hsand : Continuous (fun p : {A : Mat n // A.PosSemidef} ×
      {A : Mat n // A.PosSemidef} =>
      matrixSqrt p.1.val * p.2.val * matrixSqrt p.1.val) :=
    ((hsq.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)).mul
      (hsq.comp continuous_fst)
  have hpos (p : {A : Mat n // A.PosSemidef} × {A : Mat n // A.PosSemidef}) :
      (matrixSqrt p.1.val * p.2.val * matrixSqrt p.1.val).PosSemidef := by
    have h := (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg p.1.val)).isHermitian
    simpa only [h.eq] using p.2.property.mul_mul_conjTranspose_same (matrixSqrt p.1.val)
  exact continuous_tr.comp (hsq.comp (hsand.subtype_mk hpos))

theorem continuous_distance :
    Continuous (fun p : PositiveDefinite n × PositiveDefinite n => distance p.1 p.2) := by
  have hc : Continuous (fun A : PositiveDefinite n =>
      (⟨A.val, A.property.posSemidef⟩ : {A : Mat n // A.PosSemidef})) :=
    continuous_subtype_val.subtype_mk _
  have hf := continuous_fidelityRoot_psd.comp
    ((hc.comp continuous_fst).prodMk (hc.comp continuous_snd))
  exact Real.continuous_sqrt.comp
    (((continuous_tr.comp (continuous_subtype_val.comp continuous_fst)).add
      (continuous_tr.comp (continuous_subtype_val.comp continuous_snd))).sub
        (continuous_const.mul hf))

#print axioms continuous_distance
end Bures

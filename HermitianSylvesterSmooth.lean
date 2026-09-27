import HermitianFiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations
set_option synthInstance.maxHeartbeats 100000

noncomputable section
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContinuousLinearMap
namespace Bures

local instance (n : ℕ) : CStarAlgebra (Mat n) where
local instance : ContinuousSMul ℝ ℂ where
  continuous_smul := by
    have h : (fun p : ℝ × ℂ => p.1 • p.2) =
        (fun p : ℝ × ℂ => (p.1 : ℂ) * p.2) := by
      funext p
      exact Complex.real_smul
    rw [h]
    fun_prop
local instance (n : ℕ) : ContinuousSMul ℝ (Mat n) :=
  IsScalarTower.continuousSMul ℂ
local instance (n : ℕ) : CompleteSpace (Hermitian n) :=
  (show IsClosed (selfAdjoint (Mat n) : Set (Mat n)) by
    change IsClosed {x : Mat n | star x = x}
    exact isClosed_eq continuous_star continuous_id).completeSpace_coe
instance (n : ℕ) : ContinuousSMul ℝ (Hermitian n) where
  continuous_smul := by
    apply Continuous.subtype_mk
    exact continuous_smul.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
instance (n : ℕ) : SMulCommClass ℝ ℝ (Hermitian n) where
  smul_comm r s H := by
    apply Subtype.ext
    exact smul_comm r s H.val
instance (n : ℕ) : ContinuousConstSMul ℝ (Hermitian n) :=
  ContinuousSMul.continuousConstSMul
/-! These scalar-action instances are prerequisites for treating Hermitian Sylvester
operators as a smoothly varying family in the operator norm topology. -/

end Bures

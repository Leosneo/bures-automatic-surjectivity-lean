import HermitianSquareSmooth
import BuresSymmetry
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContinuousLinearMap
namespace Bures
local instance (n : ℕ) : CStarAlgebra (Mat n) where

/-- Real trace is a continuous real-linear map. -/
def traceRealCLM (n : ℕ) : Mat n →L[ℝ] ℝ :=
  Complex.reCLM.comp ⟨Matrix.traceLinearMap (Fin n) ℝ ℂ,
    (Matrix.traceLinearMap (Fin n) ℝ ℂ).continuous_of_finiteDimensional⟩

@[simp] theorem traceRealCLM_apply (A : Mat n) : traceRealCLM n A = tr A := rfl

/-- Hermitian sandwich product formed with the CFC square root. -/
def hermitianSandwich (B X : Hermitian n) : Hermitian n :=
  ⟨(hermitianSqrt X).val * B.val * (hermitianSqrt X).val, by
    change star ((hermitianSqrt X).val * B.val * (hermitianSqrt X).val) = _
    simp [star_mul, mul_assoc]⟩

private theorem hermitianSandwich_eq_projection (B X : Hermitian n) :
    hermitianSandwich B X = (selfAdjointPartL ℝ (Mat n))
      ((hermitianSqrt X).val * B.val * (hermitianSqrt X).val) := by
  exact (IsSelfAdjoint.selfAdjointPart_apply ℝ
    (show IsSelfAdjoint ((hermitianSqrt X).val * B.val * (hermitianSqrt X).val) by
      change star ((hermitianSqrt X).val * B.val * (hermitianSqrt X).val) = _
      simp [star_mul, mul_assoc])).symm

/-- Positivity of the inner matrix in the literal fidelity formula. -/
theorem hermitianSandwich_posDef (B X : Hermitian n)
    (hB : B.val.PosDef) (hX : X.val.PosDef) : (hermitianSandwich B X).val.PosDef := by
  have hS : (hermitianSqrt X).val.PosDef :=
    (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg X.val)).posDef_iff_isUnit.mpr
      (hX.isStrictlyPositive.sqrt).2
  have hinj : Function.Injective ((hermitianSqrt X).val).vecMul :=
    Matrix.vecMul_injective_iff_isUnit.mpr hS.isUnit
  have hp := hB.mul_mul_conjTranspose_same hinj
  change ((hermitianSqrt X).val * B.val * (hermitianSqrt X).val).PosDef
  have hh : (hermitianSqrt X).val.conjTranspose = (hermitianSqrt X).val :=
    (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg X.val)).isHermitian.eq
  rw [hh] at hp
  exact hp

/-- The CFC sandwich product is differentiable in its positive definite input. -/
theorem differentiableAt_hermitianSandwich (B A : Hermitian n)
    (hA : A.val.PosDef) : DifferentiableAt ℝ (hermitianSandwich B) A := by
  have hs : DifferentiableAt ℝ
      (fun X : Hermitian n => (hermitianSqrt X).val) A := by
    simpa only [Function.comp_def] using
      (hermitianInclusion n).differentiableAt.comp A
        (hasFDerivAt_hermitianSqrt A hA).differentiableAt
  have hm : DifferentiableAt ℝ
      (fun X : Hermitian n =>
        (hermitianSqrt X).val * B.val * (hermitianSqrt X).val) A :=
    (hs.mul_const B.val).mul hs
  have hp := (selfAdjointPartL ℝ (Mat n)).differentiableAt.comp A hm
  change DifferentiableAt ℝ (fun X : Hermitian n =>
    (selfAdjointPartL ℝ (Mat n))
      ((hermitianSqrt X).val * B.val * (hermitianSqrt X).val)) A at hp
  simpa only [← hermitianSandwich_eq_projection] using hp

/-- Literal squared Bures radicand in real Hermitian coordinates, valid as a
formula even outside the positive definite cone. -/
def squaredBuresHermitian (B X : Hermitian n) : ℝ :=
  tr X.val + tr B.val - 2 * tr (hermitianSqrt (hermitianSandwich B X)).val

/-- For positive definite matrices this is exactly the square of the
literature's Bures distance. -/
theorem squaredBuresHermitian_eq_distance_sq (A B : PositiveDefinite n) :
    squaredBuresHermitian
      (⟨B.val, B.property.isHermitian⟩ : Hermitian n)
      (⟨A.val, A.property.isHermitian⟩ : Hermitian n) = distance A B ^ 2 := by
  rw [distance_sq]
  rfl

/-- The literal squared Bures distance is differentiable in the first matrix
at every pair of positive definite Hermitian matrices. -/
theorem differentiableAt_squaredBuresHermitian (B A : Hermitian n)
    (hB : B.val.PosDef) (hA : A.val.PosDef) :
    DifferentiableAt ℝ (squaredBuresHermitian B) A := by
  have hS : DifferentiableAt ℝ (hermitianSandwich B) A :=
    differentiableAt_hermitianSandwich B A hA
  have hP : (hermitianSandwich B A).val.PosDef :=
    hermitianSandwich_posDef B A hB hA
  have hR : DifferentiableAt ℝ
      (fun X : Hermitian n => hermitianSqrt (hermitianSandwich B X)) A := by
    simpa only [Function.comp_def] using
      (hasFDerivAt_hermitianSqrt (hermitianSandwich B A) hP).differentiableAt.comp A hS
  have htr : DifferentiableAt ℝ (fun X : Hermitian n => tr X.val) A := by
    simpa only [traceRealCLM_apply, Function.comp_def] using
      (traceRealCLM n).differentiableAt.comp A
        (hermitianInclusion n).differentiableAt
  have houter : DifferentiableAt ℝ
      (fun X : Hermitian n => tr (hermitianSqrt (hermitianSandwich B X)).val) A := by
    have hval : DifferentiableAt ℝ
        (fun X : Hermitian n => (hermitianSqrt (hermitianSandwich B X)).val) A := by
      simpa only [Function.comp_def] using
        (hermitianInclusion n).differentiableAt.comp A hR
    simpa only [traceRealCLM_apply, Function.comp_def] using
      (traceRealCLM n).differentiableAt.comp A hval
  exact (htr.add_const (tr B.val)).sub (houter.const_mul 2)

/-- Differentiability on the positive definite cone for each positive definite anchor. -/
theorem differentiableOn_squaredBuresHermitian (B : Hermitian n)
    (hB : B.val.PosDef) :
    DifferentiableOn ℝ (squaredBuresHermitian B)
      {A : Hermitian n | A.val.PosDef} := by
  intro A hA
  exact (differentiableAt_squaredBuresHermitian B A hB hA).differentiableWithinAt

#print axioms differentiableAt_squaredBuresHermitian
#print axioms squaredBuresHermitian_eq_distance_sq

end Bures

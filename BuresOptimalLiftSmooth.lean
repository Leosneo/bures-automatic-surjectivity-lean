import BuresApexFourPoint
import BuresOptimalLift
import HermitianSquareSmooth

/-! A differentiable fixed-base optimal-lift chart in real Hermitian coordinates. -/

noncomputable section
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContinuousLinearMap
namespace Bures

private def hermitianSandwichCLM (S : Hermitian n) :
    Hermitian n →L[ℝ] Hermitian n where
  toFun X := ⟨S.val * X.val * S.val, by
    change star (S.val * X.val * S.val) = _
    simp [star_mul, mul_assoc]⟩
  map_add' := by
    intro X Y
    apply Subtype.ext
    change S.val * (X.val + Y.val) * S.val =
      S.val * X.val * S.val + S.val * Y.val * S.val
    noncomm_ring
  map_smul' := by
    intro r X
    apply Subtype.ext
    change S.val * (r • X.val) * S.val = r • (S.val * X.val * S.val)
    simp only [mul_smul_comm, smul_mul_assoc]
  cont := by
    exact ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

/-- The canonical lift formula extended to all Hermitian matrices; near a
positive definite input this agrees with the literal optimal Bures lift. -/
def optimalLiftHermitian (A : PositiveDefinite n) (X : Hermitian n) : Mat n :=
  let S := matrixSqrt A.val
  S⁻¹ * (hermitianSqrt (hermitianSandwichCLM
    ⟨S, (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg A.val)).isHermitian⟩ X)).val

theorem optimalLiftHermitian_eq (A B : PositiveDefinite n) :
    optimalLiftHermitian A ⟨B.val, B.property.isHermitian⟩ = optimalLift A B := rfl

theorem differentiableAt_optimalLiftHermitian (A B : PositiveDefinite n) :
    DifferentiableAt ℝ (optimalLiftHermitian A)
      ⟨B.val, B.property.isHermitian⟩ := by
  let S : Hermitian n :=
    ⟨matrixSqrt A.val,
      (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg A.val)).isHermitian⟩
  let P : Hermitian n := hermitianSandwichCLM S ⟨B.val, B.property.isHermitian⟩
  have hP : P.val.PosDef := by
    have hinj : Function.Injective S.val.vecMul :=
      Matrix.vecMul_injective_iff_isUnit.mpr (matrixSqrt_isUnit A)
    have h := B.property.mul_mul_conjTranspose_same hinj
    change (S.val * B.val * S.val).PosDef
    rw [show S.val.conjTranspose = S.val from S.property] at h
    exact h
  have hs : DifferentiableAt ℝ (fun X : Hermitian n =>
      hermitianSqrt (hermitianSandwichCLM S X))
      ⟨B.val, B.property.isHermitian⟩ := by
    simpa only [Function.comp_def] using
      (hasFDerivAt_hermitianSqrt P hP).differentiableAt.comp
        (⟨B.val, B.property.isHermitian⟩ : Hermitian n)
        (hermitianSandwichCLM S).differentiableAt
  have hv : DifferentiableAt ℝ (fun X : Hermitian n =>
      (hermitianSqrt (hermitianSandwichCLM S X)).val)
      ⟨B.val, B.property.isHermitian⟩ := by
    simpa only [Function.comp_def] using
      (hermitianInclusion n).differentiableAt.comp
        (⟨B.val, B.property.isHermitian⟩ : Hermitian n) hs
  have hm := (differentiableAt_const (c := S.val⁻¹)).mul hv
  simpa only [optimalLiftHermitian, S, hermitianSandwichCLM] using hm

#print axioms differentiableAt_optimalLiftHermitian

end Bures

import BuresRadicand
noncomputable section
open scoped MatrixOrder ComplexOrder
open Matrix
namespace Bures
lemma matrixSqrt_isUnit (A : PositiveDefinite n) : IsUnit (matrixSqrt A.val) := by
  apply isUnit_of_mul_isUnit_left (y := matrixSqrt A.val)
  rw [matrixSqrt_mul_self A.property.posSemidef]
  exact A.property.isUnit

/-- The sandwich square root supplies an explicit square root for the reversed sandwich. -/
theorem fidelityRoot_comm (A B : PositiveDefinite n) :
    fidelityRoot A.val B.val = fidelityRoot B.val A.val := by
  let X := matrixSqrt A.val
  let Y := matrixSqrt B.val
  let S := matrixSqrt (X * B.val * X)
  have hX : X * X = A.val := matrixSqrt_mul_self A.property.posSemidef
  have hY : Y * Y = B.val := matrixSqrt_mul_self B.property.posSemidef
  have hS : S * S = X * B.val * X := matrixSqrt_mul_self (sandwich_posSemidef A B)
  have hXp : X.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg _)
  have hYp : Y.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg _)
  have hSp : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg _)
  have huX : IsUnit X := matrixSqrt_isUnit A
  have huS : IsUnit S := by
    apply isUnit_of_mul_isUnit_left (y := S)
    rw [hS]
    exact (huX.mul B.property.isUnit).mul huX
  have hdS := (Matrix.isUnit_iff_isUnit_det _).mp huS
  have hiS := Matrix.nonsing_inv_mul S hdS
  have hSi := Matrix.mul_nonsing_inv S hdS
  let T := Y * X * S⁻¹ * X * Y
  have hTp : T.PosSemidef := by
    have ht := hSp.inv.mul_mul_conjTranspose_same (Y * X)
    simpa only [T, Matrix.conjTranspose_mul, hXp.isHermitian.eq, hYp.isHermitian.eq,
      mul_assoc] using ht
  have hT : T * T = Y * A.val * Y := by
    calc
      _ = Y * X * S⁻¹ * (X * (Y * Y) * X) * S⁻¹ * X * Y := by
        dsimp [T]; simp only [mul_assoc]
      _ = Y * X * S⁻¹ * (S * S) * S⁻¹ * X * Y := by rw [hY, hS]
      _ = Y * A.val * Y := by
        simp only [mul_assoc, hSi, mul_one]
        rw [← mul_assoc S⁻¹ S, hiS, one_mul, ← mul_assoc X X, hX]
  have hroot : matrixSqrt (Y * A.val * Y) = T := matrixSqrt_unique hTp hT
  have htr : tr T = tr S := by
    calc
      _ = tr (S⁻¹ * (X * (Y * Y) * X)) := by
        dsimp [T]
        rw [tr_mul_comm (Y * X * S⁻¹ * X) Y]
        rw [show Y * (Y * X * S⁻¹ * X) = (Y * Y * X) * (S⁻¹ * X) by simp [mul_assoc]]
        rw [tr_mul_comm]
        congr 1
        simp only [mul_assoc]
      _ = tr (S⁻¹ * (S * S)) := by rw [hY, hS]
      _ = tr S := by rw [← mul_assoc, hiS, one_mul]
  change tr S = tr (matrixSqrt (Y * A.val * Y))
  rw [hroot, htr]

 theorem distance_comm (A B : PositiveDefinite n) : distance A B = distance B A := by
  unfold distance
  rw [fidelityRoot_comm A B, add_comm (tr A.val) (tr B.val)]
#print axioms fidelityRoot_comm
end Bures

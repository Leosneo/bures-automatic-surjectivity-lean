import BuresVariational
import TraceCompactness
import Mathlib.Analysis.Matrix.Normed

/-! Frobenius quotient bounds and the triangle inequality for the literal
positive-definite Bures distance. -/
noncomputable section
open scoped MatrixOrder ComplexOrder Matrix.Norms.Frobenius
open Matrix
namespace Bures

lemma frobenius_norm_eq_sqrt_tr_gram (X : Mat n) :
    ‖X‖ = Real.sqrt (tr (X * Xᴴ)) := by
  rw [Matrix.frobenius_norm_def]
  change _ = Real.sqrt (Matrix.trace (X * Xᴴ)).re
  rw [BuresSupport.trace_gram]
  simp only [BuresSupport.gramEnergy, Real.rpow_two, Real.sqrt_eq_rpow]

lemma frobenius_norm_mul_unitary (X U : Mat n) (hU : U * Uᴴ = 1) :
    ‖X * U‖ = ‖X‖ := by
  rw [frobenius_norm_eq_sqrt_tr_gram, frobenius_norm_eq_sqrt_tr_gram]
  congr 2
  simp only [Matrix.conjTranspose_mul, mul_assoc]
  rw [← mul_assoc U Uᴴ, hU, one_mul]

lemma tr_gram_factor_difference (A B : PositiveDefinite n) (U : Mat n)
    (hU : U * Uᴴ = 1) :
    tr ((matrixSqrt A.val - matrixSqrt B.val * U) *
      (matrixSqrt A.val - matrixSqrt B.val * U)ᴴ) =
      tr A.val + tr B.val - 2 * tr (matrixSqrt A.val * matrixSqrt B.val * U) := by
  let X := matrixSqrt A.val
  let Y := matrixSqrt B.val
  have hXh : X.IsHermitian := Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg _) |>.isHermitian
  have hYh : Y.IsHermitian := Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg _) |>.isHermitian
  have hX : X * X = A.val := matrixSqrt_mul_self A.property.posSemidef
  have hY : Y * Y = B.val := matrixSqrt_mul_self B.property.posSemidef
  have he : (X - Y * U) * (X - Y * U)ᴴ =
      A.val - X * Uᴴ * Y - Y * U * X + B.val := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hXh.eq, hYh.eq]
    have hl : Y * U * (Uᴴ * Y) = B.val := by
      rw [mul_assoc Y U, ← mul_assoc U Uᴴ, hU, one_mul, hY]
    calc
      _ = X * X - X * Uᴴ * Y - Y * U * X + Y * U * (Uᴴ * Y) := by noncomm_ring
      _ = _ := by rw [hX, hl]
  have hc : tr (X * Uᴴ * Y) = tr (X * Y * U) := by
    rw [← tr_conjTranspose (X * Uᴴ * Y)]
    simp only [Matrix.conjTranspose_mul, hXh.eq, hYh.eq,
      Matrix.conjTranspose_conjTranspose]
    rw [← mul_assoc, tr_mul_comm (Y * U) X]
    simp only [mul_assoc]
  change tr ((X - Y * U) * (X - Y * U)ᴴ) = _
  rw [he, tr_add, tr_sub, tr_sub, hc, tr_mul_comm (Y * U) X]
  change tr A.val - tr (X * Y * U) - tr (X * (Y * U)) + tr B.val = _
  simp only [mul_assoc]
  ring

/-- Every unitary alignment gives an upper bound for the literal Bures distance. -/
theorem distance_le_frobenius_unitary (A B : PositiveDefinite n) (U : Mat n)
    (hUl : Uᴴ * U = 1) (hUr : U * Uᴴ = 1) :
    distance A B ≤ ‖matrixSqrt A.val - matrixSqrt B.val * U‖ := by
  rw [frobenius_norm_eq_sqrt_tr_gram, tr_gram_factor_difference A B U hUr]
  unfold distance
  apply Real.sqrt_le_sqrt
  have h := (fidelityRoot_variational A B).1 U hUl
  linarith

/-- The unitary alignment bound is attained. -/
theorem distance_eq_frobenius_unitary (A B : PositiveDefinite n) :
    ∃ U : Mat n, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      distance A B = ‖matrixSqrt A.val - matrixSqrt B.val * U‖ := by
  obtain ⟨U, hUl, hUr, htr⟩ := (fidelityRoot_variational A B).2
  refine ⟨U, hUl, hUr, ?_⟩
  rw [frobenius_norm_eq_sqrt_tr_gram, tr_gram_factor_difference A B U hUr, htr]
  rfl

/-- Triangle inequality for the actual matrix square-root Bures formula. -/
theorem distance_triangle (A B C : PositiveDefinite n) :
    distance A C ≤ distance A B + distance B C := by
  obtain ⟨U, hUl, hUr, hAB⟩ := distance_eq_frobenius_unitary A B
  obtain ⟨V, hVl, hVr, hBC⟩ := distance_eq_frobenius_unitary B C
  have hWl : (V * U)ᴴ * (V * U) = 1 := by
    rw [Matrix.conjTranspose_mul]
    calc
      _ = Uᴴ * (Vᴴ * V) * U := by simp only [mul_assoc]
      _ = 1 := by rw [hVl, mul_one, hUl]
  have hWr : (V * U) * (V * U)ᴴ = 1 := by
    rw [Matrix.conjTranspose_mul]
    calc
      _ = V * (U * Uᴴ) * Vᴴ := by simp only [mul_assoc]
      _ = 1 := by rw [hUr, mul_one, hVr]
  calc
    distance A C ≤ ‖matrixSqrt A.val - matrixSqrt C.val * (V * U)‖ :=
      distance_le_frobenius_unitary A C (V * U) hWl hWr
    _ = ‖(matrixSqrt A.val - matrixSqrt B.val * U) +
        (matrixSqrt B.val - matrixSqrt C.val * V) * U‖ := by
      congr 1
      noncomm_ring
    _ ≤ ‖matrixSqrt A.val - matrixSqrt B.val * U‖ +
        ‖(matrixSqrt B.val - matrixSqrt C.val * V) * U‖ := norm_add_le _ _
    _ = distance A B + distance B C := by
      rw [frobenius_norm_mul_unitary _ U hUr, ← hAB, ← hBC]

#print axioms distance_triangle
end Bures

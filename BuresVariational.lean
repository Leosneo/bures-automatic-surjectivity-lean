import BuresSymmetry
noncomputable section
open scoped MatrixOrder ComplexOrder
open Matrix
namespace Bures
lemma tr_conjTranspose (A : Mat n) : tr Aᴴ = tr A := by
  simp [tr, Matrix.trace_conjTranspose]

/-- The real trace of a positive matrix times a unitary never exceeds its trace. -/
lemma tr_mul_le_of_unitary {S U : Mat n} (hS : S.PosSemidef)
    (hU : Uᴴ * U = 1) : tr (S * U) ≤ tr S := by
  let R := matrixSqrt S
  have hRR : R * R = S := matrixSqrt_mul_self hS
  have hRh : R.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg S)).isHermitian
  have hg := tr_nonneg (Matrix.posSemidef_self_mul_conjTranspose (R - U * R))
  have hex : (R - U * R) * (R - U * R)ᴴ = S - S * Uᴴ - U * S + U * S * Uᴴ := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hRh.eq]
    calc
      _ = R * R - (R * R) * Uᴴ - U * (R * R) + U * (R * R) * Uᴴ := by noncomm_ring
      _ = _ := by rw [hRR]
  have hlast : tr (U * S * Uᴴ) = tr S := by
    rw [tr_mul_comm, ← mul_assoc, hU, one_mul]
  have hc : tr (S * Uᴴ) = tr (S * U) := by
    rw [← tr_conjTranspose (S * Uᴴ)]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hS.isHermitian.eq]
    exact tr_mul_comm _ _
  rw [hex, tr_add, tr_sub, tr_sub, hlast, hc, tr_mul_comm U S] at hg
  linarith

/-- The fidelity is the maximum overlap of square-root factors over unitary alignment. -/
theorem fidelityRoot_variational (A B : PositiveDefinite n) :
    (∀ U : Mat n, Uᴴ * U = 1 →
      tr (matrixSqrt A.val * matrixSqrt B.val * U) ≤ fidelityRoot A.val B.val) ∧
    ∃ U : Mat n, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      tr (matrixSqrt A.val * matrixSqrt B.val * U) = fidelityRoot A.val B.val := by
  let X := matrixSqrt A.val
  let Y := matrixSqrt B.val
  let S := matrixSqrt (X * B.val * X)
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
  let V := S⁻¹ * X * Y
  have hVV : V * Vᴴ = 1 := by
    change (S⁻¹ * X * Y) * (S⁻¹ * X * Y)ᴴ = 1
    simp only [Matrix.conjTranspose_mul, hXp.isHermitian.eq, hYp.isHermitian.eq,
      hSp.isHermitian.inv.eq]
    calc
      _ = S⁻¹ * (X * (Y * Y) * X) * S⁻¹ := by simp only [mul_assoc]
      _ = S⁻¹ * (S * S) * S⁻¹ := by rw [hY, hS]
      _ = 1 := by simp only [← mul_assoc, hiS, one_mul, hSi]
  have hVV' : Vᴴ * V = 1 := by exact mul_eq_one_comm.mp hVV
  have hC : X * Y = S * V := by
    dsimp [V]
    rw [← mul_assoc, ← mul_assoc, hSi, one_mul]
  constructor
  · intro U hU
    have hVU : (V * U)ᴴ * (V * U) = 1 := by
      simp only [Matrix.conjTranspose_mul, mul_assoc]
      rw [← mul_assoc Vᴴ V, hVV', one_mul, hU]
    change tr (X * Y * U) ≤ tr S
    rw [hC, mul_assoc]
    exact tr_mul_le_of_unitary hSp hVU
  · refine ⟨Vᴴ, ?_, ?_, ?_⟩
    · simpa only [Matrix.conjTranspose_conjTranspose] using hVV
    · simpa only [Matrix.conjTranspose_conjTranspose] using hVV'
    · change tr (X * Y * Vᴴ) = tr S
      rw [hC, mul_assoc, hVV, mul_one]

#print axioms tr_mul_le_of_unitary
#print axioms fidelityRoot_variational
end Bures

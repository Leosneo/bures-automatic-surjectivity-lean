import BuresRadial
noncomputable section
open scoped MatrixOrder ComplexOrder
open Matrix
namespace Bures

lemma tr_add (A B : Mat n) : tr (A+B) = tr A + tr B := by simp [tr, Matrix.trace_add]
lemma tr_sub (A B : Mat n) : tr (A-B) = tr A - tr B := by simp [tr, Matrix.trace_sub]
lemma tr_mul_comm (A B : Mat n) : tr (A*B) = tr (B*A) := by
  unfold tr
  rw [Matrix.trace_mul_comm]

/-- A concrete Gram witness for the literal Bures radicand. -/
theorem radicand_gram (A B : PositiveDefinite n) :
    ∃ Y : Mat n, tr (Y * Yᴴ) = tr A.val + tr B.val - 2 * fidelityRoot A.val B.val ∧
      (Y = 0 → A = B) := by
  let X := matrixSqrt A.val
  let S := matrixSqrt (X * B.val * X)
  have hX : X * X = A.val := matrixSqrt_mul_self A.property.posSemidef
  have hS : S * S = X * B.val * X := matrixSqrt_mul_self (sandwich_posSemidef A B)
  have hXh : X.IsHermitian := Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg _) |>.isHermitian
  have hSh : S.IsHermitian := Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg _) |>.isHermitian
  have hu : IsUnit X.det := by
    apply isUnit_of_mul_isUnit_left (y := X.det)
    rw [← Matrix.det_mul, hX]
    exact (Matrix.isUnit_iff_isUnit_det _).mp A.property.isUnit
  have hXi := Matrix.mul_nonsing_inv X hu
  have hiX := Matrix.nonsing_inv_mul X hu
  have hgram : (X - X⁻¹ * S) * (X - X⁻¹ * S)ᴴ =
      A.val - X * S * X⁻¹ - X⁻¹ * S * X + B.val := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hXh.eq, hSh.eq,
      hXh.inv.eq]
    have hlast : X⁻¹ * S * (S * X⁻¹) = B.val := by
      calc
        _ = X⁻¹ * (S * S) * X⁻¹ := by simp only [mul_assoc]
        _ = X⁻¹ * (X * B.val * X) * X⁻¹ := by rw [hS]
        _ = B.val := by
          simp only [mul_assoc, hXi, mul_one]
          rw [← mul_assoc, hiX, one_mul]
    calc
      _ = X * X - X * S * X⁻¹ - X⁻¹ * S * X + X⁻¹ * S * (S * X⁻¹) := by noncomm_ring
      _ = _ := by rw [hX, hlast]
  have hcyc1 : tr (X * S * X⁻¹) = tr S := by
    rw [tr_mul_comm, ← mul_assoc, hiX, one_mul]
  have hcyc2 : tr (X⁻¹ * S * X) = tr S := by
    rw [tr_mul_comm, ← mul_assoc, hXi, one_mul]
  refine ⟨X - X⁻¹ * S, ?_, ?_⟩
  · rw [hgram, tr_add, tr_sub, tr_sub, hcyc1, hcyc2]
    change tr A.val - tr S - tr S + tr B.val = tr A.val + tr B.val - 2 * tr S
    ring
  · intro hz
    have he : X = X⁻¹ * S := sub_eq_zero.mp hz
    have hsA : S = A.val := by
      calc
        S = X * (X⁻¹ * S) := by rw [← mul_assoc, hXi, one_mul]
        _ = X * X := by rw [← he]
        _ = A.val := hX
    have hb : X * B.val * X = X * A.val * X := by
      rw [← hS, hsA, ← hX]
      simp only [mul_assoc]
    have hh := congrArg (fun M : Mat n => X⁻¹ * M * X⁻¹) hb
    simp only [← mul_assoc, hiX, one_mul] at hh
    simp only [mul_assoc, hXi, mul_one] at hh
    exact Subtype.ext hh.symm

theorem radicand_nonneg (A B : PositiveDefinite n) :
    0 ≤ tr A.val + tr B.val - 2 * fidelityRoot A.val B.val := by
  obtain ⟨Y, he, _⟩ := radicand_gram A B
  rw [← he]
  exact tr_nonneg (Matrix.posSemidef_self_mul_conjTranspose Y)

/-- The literal Bures formula separates positive-definite matrices. -/
theorem distance_eq_zero_iff (A B : PositiveDefinite n) : distance A B = 0 ↔ A = B := by
  constructor
  · intro hd
    have hr := (Real.sqrt_eq_zero (radicand_nonneg A B)).mp hd
    obtain ⟨Y, he, hy⟩ := radicand_gram A B
    apply hy
    apply Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp
    have hp := (Complex.nonneg_iff.mp (Matrix.posSemidef_self_mul_conjTranspose Y).trace_nonneg).2
    apply Complex.ext
    · exact he.trans hr
    · exact hp.symm
  · rintro rfl
    exact distance_self A


theorem distance_sq (A B : PositiveDefinite n) :
    distance A B ^ 2 = tr A.val + tr B.val - 2 * fidelityRoot A.val B.val :=
  Real.sq_sqrt (radicand_nonneg A B)

/-- Injectivity is a consequence of the literal distance-preservation hypothesis. -/
theorem PreservesDistance.injective {F : PositiveDefinite n → PositiveDefinite n}
    (hF : PreservesDistance F) : Function.Injective F := by
  intro A B h
  apply (distance_eq_zero_iff A B).mp
  rw [← hF A B, h, distance_self]

#print axioms radicand_nonneg
#print axioms distance_eq_zero_iff
end Bures

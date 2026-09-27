import BuresInfinitesimalMetric

/-! Canonical positive overlap lift of the second endpoint. -/

noncomputable section
open scoped MatrixOrder ComplexOrder Matrix.Norms.Frobenius
namespace Bures

/-- For fixed `A`, this lift of `B` has positive overlap with `√A`. -/
def optimalLift (A B : PositiveDefinite n) : Mat n :=
  let S := matrixSqrt A.val
  S⁻¹ * matrixSqrt (S * B.val * S)

theorem optimalLift_gram (A B : PositiveDefinite n) :
    gram (optimalLift A B) = B.val := by
  let S := matrixSqrt A.val
  let M := matrixSqrt (S * B.val * S)
  have hSh : S.IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg A.val)).isHermitian
  have hMh : M.IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg _)).isHermitian
  have hMM : M * M = S * B.val * S := matrixSqrt_mul_self (sandwich_posSemidef A B)
  have hdS := (Matrix.isUnit_iff_isUnit_det _).mp (matrixSqrt_isUnit A)
  have hSi := Matrix.mul_nonsing_inv S hdS
  have hiS := Matrix.nonsing_inv_mul S hdS
  change gram (S⁻¹ * M) = B.val
  simp only [gram, Matrix.conjTranspose_mul, hMh.eq, hSh.inv.eq]
  calc
    S⁻¹ * M * (M * S⁻¹) = S⁻¹ * (M * M) * S⁻¹ := by simp only [mul_assoc]
    _ = S⁻¹ * (S * B.val * S) * S⁻¹ := by rw [hMM]
    _ = B.val := by
      calc
        _ = (S⁻¹ * S) * B.val * (S * S⁻¹) := by noncomm_ring
        _ = B.val := by rw [hiS, hSi, one_mul, mul_one]

theorem optimalLift_overlap (A B : PositiveDefinite n) :
    matrixSqrt A.val * optimalLift A B =
      matrixSqrt (matrixSqrt A.val * B.val * matrixSqrt A.val) := by
  have hdS := (Matrix.isUnit_iff_isUnit_det _).mp (matrixSqrt_isUnit A)
  have hSi := Matrix.mul_nonsing_inv (matrixSqrt A.val) hdS
  simp only [optimalLift, ← mul_assoc, hSi, one_mul]

theorem optimalLift_self (A : PositiveDefinite n) :
    optimalLift A A = matrixSqrt A.val := by
  have hS := matrixSqrt_mul_self A.property.posSemidef
  have hsa : matrixSqrt A.val * A.val * matrixSqrt A.val = A.val * A.val := by
    calc
      _ = matrixSqrt A.val *
          (matrixSqrt A.val * matrixSqrt A.val) * matrixSqrt A.val := by rw [hS]
      _ = (matrixSqrt A.val * matrixSqrt A.val) *
          (matrixSqrt A.val * matrixSqrt A.val) := by noncomm_ring
      _ = A.val * A.val := by rw [hS]
  have hroot : matrixSqrt (matrixSqrt A.val * A.val * matrixSqrt A.val) = A.val := by
    rw [hsa]
    exact matrixSqrt_unique A.property.posSemidef rfl
  have hdS := (Matrix.isUnit_iff_isUnit_det _).mp (matrixSqrt_isUnit A)
  have hiS := Matrix.nonsing_inv_mul (matrixSqrt A.val) hdS
  change (matrixSqrt A.val)⁻¹ *
    matrixSqrt (matrixSqrt A.val * A.val * matrixSqrt A.val) = matrixSqrt A.val
  rw [hroot]
  calc
    (matrixSqrt A.val)⁻¹ * A.val =
        (matrixSqrt A.val)⁻¹ * (matrixSqrt A.val * matrixSqrt A.val) := by rw [hS]
    _ = matrixSqrt A.val := by rw [← mul_assoc, hiS, one_mul]

/-- The chosen Gram lift realizes the literal Bures distance exactly. -/
theorem distance_eq_optimalLift_norm (A B : PositiveDefinite n) :
    distance A B = ‖matrixSqrt A.val - optimalLift A B‖ := by
  let S := matrixSqrt A.val
  let T := optimalLift A B
  let M := matrixSqrt (S * B.val * S)
  have hSh : S.IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg A.val)).isHermitian
  have hST : S * T = M := optimalLift_overlap A B
  have hSS : S * S.conjTranspose = A.val := by
    rw [hSh.eq]
    exact matrixSqrt_mul_self A.property.posSemidef
  have hTT : T * T.conjTranspose = B.val := optimalLift_gram A B
  have hcross₁ : tr (S * T.conjTranspose) = tr M := by
    calc
      tr (S * T.conjTranspose) = tr ((S * T.conjTranspose).conjTranspose) :=
        (tr_conjTranspose _).symm
      _ = tr (T * S) := by rw [Matrix.conjTranspose_mul, hSh.eq,
        Matrix.conjTranspose_conjTranspose]
      _ = tr (S * T) := tr_mul_comm T S
      _ = tr M := by rw [hST]
  have hcross₂ : tr (T * S.conjTranspose) = tr M := by
    rw [hSh.eq, tr_mul_comm T S, hST]
  have hnormsq : ‖S - T‖ ^ 2 = tr A.val + tr B.val - 2 * tr M := by
    rw [frobenius_sq_eq_tr_gram]
    have hex : (S - T) * (S - T).conjTranspose =
        S * S.conjTranspose + T * T.conjTranspose -
          S * T.conjTranspose - T * S.conjTranspose := by
      rw [Matrix.conjTranspose_sub]
      noncomm_ring
    rw [hex, tr_sub, tr_sub, tr_add, hSS, hTT, hcross₁, hcross₂]
    ring
  have hsqd : ‖S - T‖ ^ 2 = distance A B ^ 2 := by
    rw [hnormsq, distance_sq]
    rfl
  have hn := norm_nonneg (S - T)
  have hd := distance_nonneg A B
  dsimp [S, T] at hsqd ⊢
  nlinarith

/-- A Gram factor with positive overlap with `√A` is the canonical optimal
lift; this characterizes the local horizontal geodesic alignment. -/
theorem optimalLift_eq_of_positive_overlap (A B : PositiveDefinite n)
    (T : Mat n) (hGram : gram T = B.val)
    (hOverlap : (matrixSqrt A.val * T).PosSemidef) :
    optimalLift A B = T := by
  let S := matrixSqrt A.val
  have hSh : S.IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg A.val)).isHermitian
  have hSym : T.conjTranspose * S = S * T := by
    have hh := hOverlap.isHermitian.eq
    change (S * T).conjTranspose = S * T at hh
    rw [Matrix.conjTranspose_mul, hSh.eq] at hh
    exact hh
  have hSq : (S * T) * (S * T) = S * B.val * S := by
    calc
      (S * T) * (S * T) = S * T * (T.conjTranspose * S) := by rw [hSym]
      _ = S * gram T * S := by simp only [gram, mul_assoc]
      _ = S * B.val * S := by rw [hGram]
  have hroot : matrixSqrt (S * B.val * S) = S * T :=
    matrixSqrt_unique hOverlap hSq
  have hdS := (Matrix.isUnit_iff_isUnit_det _).mp (matrixSqrt_isUnit A)
  have hiS := Matrix.nonsing_inv_mul S hdS
  change S⁻¹ * matrixSqrt (S * B.val * S) = T
  rw [hroot, ← mul_assoc, hiS, one_mul]

theorem distance_eq_positive_overlap_factor (A B : PositiveDefinite n)
    (T : Mat n) (hGram : gram T = B.val)
    (hOverlap : (matrixSqrt A.val * T).PosSemidef) :
    distance A B = ‖matrixSqrt A.val - T‖ := by
  rw [distance_eq_optimalLift_norm,
    optimalLift_eq_of_positive_overlap A B T hGram hOverlap]

/-- Exact speed of a horizontal Gram curve whenever its overlap remains
positive; the local existence of this positivity is a separate open-cone
lemma. -/
theorem distance_horizontal_gram_curve (A : PositiveDefinite n)
    (K : Mat n) (t : ℝ)
    (hB : (gram (matrixSqrt A.val + t • (K * matrixSqrt A.val))).PosDef)
    (hOverlap : (matrixSqrt A.val *
      (matrixSqrt A.val + t • (K * matrixSqrt A.val))).PosSemidef) :
    distance A ⟨gram (matrixSqrt A.val + t • (K * matrixSqrt A.val)), hB⟩ =
      |t| * ‖K * matrixSqrt A.val‖ := by
  let T := matrixSqrt A.val + t • (K * matrixSqrt A.val)
  have h := distance_eq_positive_overlap_factor A ⟨gram T, hB⟩ T rfl hOverlap
  change distance A ⟨gram T, hB⟩ = _
  rw [h]
  have he : matrixSqrt A.val - T = -(t • (K * matrixSqrt A.val)) := by
    dsimp [T]
    abel
  rw [he, norm_neg]
  have hsm : (t • (K * matrixSqrt A.val) : Mat n) =
      (t : ℂ) • (K * matrixSqrt A.val) := by
    ext i j
    simp [Matrix.smul_apply, Complex.real_smul]
  rw [hsm, norm_smul, Complex.norm_real, Real.norm_eq_abs]

/-- Positive overlap alone ensures the Gram endpoint is positive definite
and gives the exact horizontal speed. -/
theorem horizontal_gram_curve_exists (A : PositiveDefinite n)
    (K : Mat n) (t : ℝ)
    (hOverlap : (matrixSqrt A.val *
      (matrixSqrt A.val + t • (K * matrixSqrt A.val))).PosDef) :
    ∃ B : PositiveDefinite n,
      B.val = gram (matrixSqrt A.val + t • (K * matrixSqrt A.val)) ∧
      distance A B = |t| * ‖K * matrixSqrt A.val‖ := by
  let T := matrixSqrt A.val + t • (K * matrixSqrt A.val)
  have hTunit : IsUnit T := isUnit_of_mul_isUnit_right hOverlap.isUnit
  have hB : (gram T).PosDef :=
    Matrix.PosDef.mul_conjTranspose_self T
      (Matrix.vecMul_injective_of_isUnit hTunit)
  refine ⟨⟨gram T, hB⟩, rfl, ?_⟩
  exact distance_horizontal_gram_curve A K t hB hOverlap.posSemidef

/-- Along each valid horizontal Gram curve, the quadratic coefficient of the
literal Bures distance is exactly the Sylvester quotient-metric form. -/
theorem distance_horizontal_gram_curve_quadratic (A : PositiveDefinite n)
    (K : Mat n) (hK : K.IsHermitian) (t : ℝ) (ht : t ≠ 0)
    (hB : (gram (matrixSqrt A.val + t • (K * matrixSqrt A.val))).PosDef)
    (hOverlap : (matrixSqrt A.val *
      (matrixSqrt A.val + t • (K * matrixSqrt A.val))).PosSemidef) :
    distance A ⟨gram (matrixSqrt A.val + t • (K * matrixSqrt A.val)), hB⟩ ^ 2 / t ^ 2 =
      tr ((K * A.val + A.val * K) * K) / 2 := by
  rw [distance_horizontal_gram_curve A K t hB hOverlap]
  have hA : gram (matrixSqrt A.val) = A.val := by
    rw [gram, (Matrix.nonneg_iff_posSemidef.mp
      (matrixSqrt_nonneg A.val)).isHermitian.eq]
    exact matrixSqrt_mul_self A.property.posSemidef
  have henergy := horizontal_energy_eq_sylvester (matrixSqrt A.val) K hK
  rw [hA] at henergy
  have hnorm : tr ((K * matrixSqrt A.val).conjTranspose *
      (K * matrixSqrt A.val)) = ‖K * matrixSqrt A.val‖ ^ 2 := by
    rw [tr_mul_comm, ← frobenius_sq_eq_tr_gram]
  rw [← henergy, hnorm]
  rw [mul_pow, sq_abs]
  field_simp

#print axioms distance_eq_optimalLift_norm

end Bures

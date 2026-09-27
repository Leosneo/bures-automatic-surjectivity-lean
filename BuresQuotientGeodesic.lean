import BuresTriangle

/-! The optimal alignment of two square-root factors stays invertible under
straight interpolation. This is the algebraic interior condition needed to
identify the quotient path distance with the explicit Bures distance. -/

noncomputable section
open scoped MatrixOrder ComplexOrder Matrix.Norms.Frobenius
open Matrix
namespace Bures

/-- If the two endpoint Gram matrices and their aligned cross Gram matrix are
positive definite, their straight interpolation consists of invertible lifts. -/
theorem aligned_segment_isUnit {X Y : Mat n}
    (hXX : (X * X).PosDef) (hXY : (X * Y).PosDef)
    (hY : IsUnit Y) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsUnit ((1 - t) • X + t • Y) := by
  by_cases ht : t = 0
  · subst t
    have he : ((1 - (0 : ℝ)) • X + (0 : ℝ) • Y) = X := by
      ext i j
      simp [Matrix.smul_apply]
    rw [he]
    exact isUnit_of_mul_isUnit_left hXX.isUnit
  by_cases ht' : t = 1
  · subst t
    have he : ((1 - (1 : ℝ)) • X + (1 : ℝ) • Y) = Y := by
      ext i j
      simp [Matrix.smul_apply]
    rw [he]
    exact hY
  have htp : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
  have h1tp : 0 < 1 - t := sub_pos.mpr (lt_of_le_of_ne ht1 ht')
  have hZ : ((1 - t) • (X * X) + t • (X * Y)).PosDef :=
    (hXX.smul h1tp).add (hXY.smul htp)
  have heq : X * ((1 - t) • X + t • Y) =
      (1 - t) • (X * X) + t • (X * Y) := by
    rw [mul_add]
    rw [mul_smul_comm, mul_smul_comm]
  exact isUnit_of_mul_isUnit_right (heq ▸ hZ.isUnit)

/-- There is an optimal unitary alignment for which the Euclidean segment
between the square-root lifts remains in the invertible matrices. -/
theorem optimal_alignment_invertible_segment (A B : PositiveDefinite n) :
    ∃ U : Mat n, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      distance A B = ‖matrixSqrt A.val - matrixSqrt B.val * U‖ ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        IsUnit ((1 - t) • matrixSqrt A.val + t • (matrixSqrt B.val * U)) := by
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
  have hSpos : S.PosDef := hSp.posDef_iff_isUnit.mpr huS
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
  have hVV' : Vᴴ * V = 1 := mul_eq_one_comm.mp hVV
  have hXY : X * Y = S * V := by
    dsimp [V]
    rw [← mul_assoc, ← mul_assoc, hSi, one_mul]
  have hXU : X * (Y * Vᴴ) = S := by
    rw [← mul_assoc, hXY, mul_assoc, hVV, mul_one]
  have hXX : (X * X).PosDef := by
    rw [matrixSqrt_mul_self A.property.posSemidef]
    exact A.property
  have huV : IsUnit V := by
    apply isUnit_of_mul_isUnit_left (y := Vᴴ)
    rw [hVV]
    exact isUnit_one
  have hYU : IsUnit (Y * Vᴴ) :=
    (matrixSqrt_isUnit B).mul ((isUnit_conjTranspose V).mpr huV)
  refine ⟨Vᴴ, ?_, ?_, ?_, ?_⟩
  · simpa only [Matrix.conjTranspose_conjTranspose] using hVV
  · simpa only [Matrix.conjTranspose_conjTranspose] using hVV'
  · rw [frobenius_norm_eq_sqrt_tr_gram]
    have htr : tr (X * Y * Vᴴ) = tr S := by
      rw [mul_assoc, ← hXU]
    rw [tr_gram_factor_difference A B Vᴴ (by
      simpa only [Matrix.conjTranspose_conjTranspose] using hVV'), htr]
    rfl
  · intro t ht0 ht1
    exact aligned_segment_isUnit hXX (hXU ▸ hSpos) hYU ht0 ht1

/-- The aligned Euclidean segment projects to a path inside the positive
definite cone, including its two endpoints. -/
theorem optimal_alignment_posDef_segment (A B : PositiveDefinite n) :
    ∃ U : Mat n, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      distance A B = ‖matrixSqrt A.val - matrixSqrt B.val * U‖ ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        (((1 - t) • matrixSqrt A.val + t • (matrixSqrt B.val * U)) *
          ((1 - t) • matrixSqrt A.val + t • (matrixSqrt B.val * U))ᴴ).PosDef := by
  obtain ⟨U, hUl, hUr, hd, hseg⟩ := optimal_alignment_invertible_segment A B
  refine ⟨U, hUl, hUr, hd, ?_⟩
  intro t ht0 ht1
  let W := (1 - t) • matrixSqrt A.val + t • (matrixSqrt B.val * U)
  exact Matrix.PosDef.mul_conjTranspose_self W
    (Matrix.vecMul_injective_of_isUnit (hseg t ht0 ht1))

/-- Polar factorization of an invertible lift, with the canonical positive
square root on the left and a unitary factor on the right. -/
theorem invertible_factor_polar (P : Mat n) (hP : IsUnit P) :
    ∃ U : Mat n, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      P = matrixSqrt (P * Pᴴ) * U := by
  have hA : (P * Pᴴ).PosDef :=
    Matrix.PosDef.mul_conjTranspose_self P (Matrix.vecMul_injective_of_isUnit hP)
  let X := matrixSqrt (P * Pᴴ)
  have hXh : X.IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg _)).isHermitian
  have hXX : X * X = P * Pᴴ := matrixSqrt_mul_self hA.posSemidef
  have huX : IsUnit X := matrixSqrt_isUnit ⟨P * Pᴴ, hA⟩
  have hdX := (Matrix.isUnit_iff_isUnit_det _).mp huX
  have hXi := Matrix.nonsing_inv_mul X hdX
  have hiX := Matrix.mul_nonsing_inv X hdX
  let U := X⁻¹ * P
  have hUU : U * Uᴴ = 1 := by
    change (X⁻¹ * P) * (X⁻¹ * P)ᴴ = 1
    simp only [Matrix.conjTranspose_mul, hXh.inv.eq]
    calc
      _ = X⁻¹ * (P * Pᴴ) * X⁻¹ := by simp only [mul_assoc]
      _ = X⁻¹ * (X * X) * X⁻¹ := by rw [hXX]
      _ = 1 := by simp only [← mul_assoc, hXi, one_mul, hiX]
  refine ⟨U, mul_eq_one_comm.mp hUU, hUU, ?_⟩
  change P = X * (X⁻¹ * P)
  rw [← mul_assoc, hiX, one_mul]

/-- Any two invertible lifts give an upper bound for the literal Bures
distance between their Gram matrices. -/
theorem distance_le_frobenius_factors (P Q : Mat n)
    (hP : IsUnit P) (hQ : IsUnit Q) :
    distance
      ⟨P * Pᴴ, Matrix.PosDef.mul_conjTranspose_self P
        (Matrix.vecMul_injective_of_isUnit hP)⟩
      ⟨Q * Qᴴ, Matrix.PosDef.mul_conjTranspose_self Q
        (Matrix.vecMul_injective_of_isUnit hQ)⟩ ≤ ‖P - Q‖ := by
  let A : PositiveDefinite n := ⟨P * Pᴴ, Matrix.PosDef.mul_conjTranspose_self P
    (Matrix.vecMul_injective_of_isUnit hP)⟩
  let B : PositiveDefinite n := ⟨Q * Qᴴ, Matrix.PosDef.mul_conjTranspose_self Q
    (Matrix.vecMul_injective_of_isUnit hQ)⟩
  obtain ⟨U, hUl, hUr, hPU⟩ := invertible_factor_polar P hP
  obtain ⟨V, hVl, hVr, hQV⟩ := invertible_factor_polar Q hQ
  have hWl : (V * Uᴴ)ᴴ * (V * Uᴴ) = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = U * (Vᴴ * V) * Uᴴ := by simp only [mul_assoc]
      _ = 1 := by rw [hVl, mul_one, hUr]
  have hWr : (V * Uᴴ) * (V * Uᴴ)ᴴ = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = V * (Uᴴ * U) * Vᴴ := by simp only [mul_assoc]
      _ = 1 := by rw [hUl, mul_one, hVr]
  have hb := distance_le_frobenius_unitary A B (V * Uᴴ) hWl hWr
  change distance A B ≤ ‖P - Q‖
  calc
    distance A B ≤ ‖matrixSqrt A.val - matrixSqrt B.val * (V * Uᴴ)‖ := hb
    _ = ‖(matrixSqrt A.val - matrixSqrt B.val * V * Uᴴ) * U‖ := by
      rw [frobenius_norm_mul_unitary _ U hUr]
      congr 1
      simp only [mul_assoc]
    _ = ‖P - Q‖ := by
      congr 1
      calc
        (matrixSqrt A.val - matrixSqrt B.val * V * Uᴴ) * U =
            matrixSqrt A.val * U - (matrixSqrt B.val * V) * (Uᴴ * U) := by
          rw [sub_mul]
          simp only [mul_assoc]
        _ = matrixSqrt A.val * U - matrixSqrt B.val * V := by rw [hUl, mul_one]
        _ = P - Q := by simpa only [A, B] using congrArg₂ (· - ·) hPU.symm hQV.symm

private theorem frobenius_norm_real_smul (r : ℝ) (M : Mat n) :
    ‖r • M‖ = |r| * ‖M‖ := by
  have h : r • M = (r : ℂ) • M := by
    ext i j
    simp [Matrix.smul_apply, Complex.real_smul]
  rw [h, norm_smul, Complex.norm_real, Real.norm_eq_abs]

/-- The explicit Bures metric has a constant-speed geodesic between every
two positive-definite matrices, obtained by projecting an optimal straight
segment of invertible square-root factors. This is a metric-length statement;
it does not identify the Riemannian tensor or its curvature. -/
theorem exists_constant_speed_geodesic (A B : PositiveDefinite n) :
    ∃ γ : Set.Icc (0 : ℝ) 1 → PositiveDefinite n,
      γ ⟨0, by norm_num⟩ = A ∧ γ ⟨1, by norm_num⟩ = B ∧
      ∀ s t, distance (γ s) (γ t) = |s.val - t.val| * distance A B := by
  obtain ⟨U, hUl, hUr, hd, hseg⟩ := optimal_alignment_invertible_segment A B
  let X := matrixSqrt A.val
  let Y := matrixSqrt B.val * U
  let W (t : Set.Icc (0 : ℝ) 1) : Mat n := (1 - t.val) • X + t.val • Y
  have hW (t : Set.Icc (0 : ℝ) 1) : IsUnit (W t) :=
    hseg t.val t.property.1 t.property.2
  let γ (t : Set.Icc (0 : ℝ) 1) : PositiveDefinite n :=
    ⟨W t * (W t)ᴴ, Matrix.PosDef.mul_conjTranspose_self (W t)
      (Matrix.vecMul_injective_of_isUnit (hW t))⟩
  have hzero : γ ⟨0, by norm_num⟩ = A := by
    apply Subtype.ext
    change W ⟨0, by norm_num⟩ * (W ⟨0, by norm_num⟩)ᴴ = A.val
    have hW0 : W ⟨0, by norm_num⟩ = X := by
      ext i j
      simp [W, Matrix.smul_apply]
    rw [hW0, (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg A.val)).isHermitian.eq]
    exact matrixSqrt_mul_self A.property.posSemidef
  have hone : γ ⟨1, by norm_num⟩ = B := by
    apply Subtype.ext
    change W ⟨1, by norm_num⟩ * (W ⟨1, by norm_num⟩)ᴴ = B.val
    have hW1 : W ⟨1, by norm_num⟩ = Y := by
      ext i j
      simp [W, Matrix.smul_apply]
    rw [hW1, Matrix.conjTranspose_mul]
    simp only [Y, mul_assoc]
    rw [← mul_assoc U Uᴴ, hUr, one_mul,
      (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg B.val)).isHermitian.eq]
    exact matrixSqrt_mul_self B.property.posSemidef
  have hdiff (s t : Set.Icc (0 : ℝ) 1) :
      W s - W t = (t.val - s.val) • (X - Y) := by
    ext i j
    simp [W, Matrix.smul_apply, Complex.real_smul]
    ring
  have hupper (s t : Set.Icc (0 : ℝ) 1) :
      distance (γ s) (γ t) ≤ |s.val - t.val| * distance A B := by
    have h := distance_le_frobenius_factors (W s) (W t) (hW s) (hW t)
    change distance (γ s) (γ t) ≤ ‖W s - W t‖ at h
    rw [hdiff, frobenius_norm_real_smul, abs_sub_comm] at h
    have hd' : distance A B = ‖X - Y‖ := hd
    rw [← hd'] at h
    exact h
  have hD : 0 ≤ distance A B := distance_nonneg A B
  have hforward (s t : Set.Icc (0 : ℝ) 1) (hst : s.val ≤ t.val) :
      distance (γ s) (γ t) = |s.val - t.val| * distance A B := by
    have h0s := hupper ⟨0, by norm_num⟩ s
    have ht1 := hupper t ⟨1, by norm_num⟩
    have hstup := hupper s t
    have htri : distance A B ≤
        distance (γ ⟨0, by norm_num⟩) (γ s) +
        distance (γ s) (γ t) +
        distance (γ t) (γ ⟨1, by norm_num⟩) := by
      rw [← hzero, ← hone]
      calc
        distance (γ ⟨0, by norm_num⟩) (γ ⟨1, by norm_num⟩) ≤
            distance (γ ⟨0, by norm_num⟩) (γ s) +
            distance (γ s) (γ ⟨1, by norm_num⟩) := distance_triangle _ _ _
        _ ≤ distance (γ ⟨0, by norm_num⟩) (γ s) +
            (distance (γ s) (γ t) + distance (γ t) (γ ⟨1, by norm_num⟩)) := by
          gcongr
          exact distance_triangle _ _ _
        _ = _ := by ring
    have hs0 := s.property.1
    have ht1' := t.property.2
    simp only [zero_sub, abs_neg, abs_of_nonneg hs0,
      abs_of_nonpos (sub_nonpos.mpr ht1'), abs_of_nonpos (sub_nonpos.mpr hst)] at h0s ht1 hstup
    rw [abs_of_nonpos (sub_nonpos.mpr hst)]
    apply le_antisymm hstup
    nlinarith
  refine ⟨γ, hzero, hone, ?_⟩
  intro s t
  rcases le_total s.val t.val with hst | hts
  · exact hforward s t hst
  · rw [distance_comm, abs_sub_comm]
    exact hforward t s hts

#print axioms aligned_segment_isUnit
#print axioms optimal_alignment_invertible_segment
#print axioms optimal_alignment_posDef_segment
#print axioms invertible_factor_polar
#print axioms distance_le_frobenius_factors
#print axioms exists_constant_speed_geodesic

end Bures

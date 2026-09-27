import BuresGeodesicRigidity
import Mathlib.Analysis.InnerProductSpace.Basic
import BuresFrobenius

/-! Strict convexity ingredient for uniqueness of projected Bures segments.
The matrix quotient lift still needs a separate optimal-alignment uniqueness
argument. -/
noncomputable section
open scoped MatrixOrder ComplexOrder Matrix.Norms.Frobenius
open Matrix
namespace Bures

theorem euclidean_midpoint_unique
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x y z : E}
    (hx : ‖x - z‖ = ‖x - y‖ / 2)
    (hy : ‖z - y‖ = ‖x - y‖ / 2) :
    z = (1 / 2 : ℝ) • (x + y) := by
  have htri : ‖x - y‖ ≤ ‖x - z‖ + ‖z - y‖ := by
    calc
      ‖x - y‖ = ‖(x - z) + (z - y)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have heq : ‖(x - z) + (z - y)‖ = ‖x - z‖ + ‖z - y‖ := by
    rw [show (x - z) + (z - y) = x - y by abel, hx, hy]
    ring
  have hcol := (norm_add_eq_iff_real).mp heq
  rw [hx, hy] at hcol
  have hz : x - z = z - y := by
    by_cases hxy : ‖x - y‖ = 0
    · have : x = y := sub_eq_zero.mp (norm_eq_zero.mp hxy)
      subst y
      have : x = z := sub_eq_zero.mp (norm_eq_zero.mp (by simpa using hx))
      subst z
      simp
    · have hhalf : ‖x - y‖ / 2 ≠ 0 := by exact div_ne_zero hxy (by norm_num)
      have hcancel := congrArg (fun v : E => (‖x - y‖ / 2)⁻¹ • v) hcol
      simpa [smul_smul, hhalf, div_self hxy] using hcancel
  have heq2 : (2 : ℝ) • z = x + y := by
    calc
      (2 : ℝ) • z = z + z := by simp [two_smul]
      _ = x + y := by have := congrArg (fun q : E => q + z + y) hz; abel_nf at this ⊢; exact this.symm
  calc
    z = (1 / 2 : ℝ) • ((2 : ℝ) • z) := by simp [smul_smul]
    _ = (1 / 2 : ℝ) • (x + y) := by rw [heq2]

/-- For a strictly positive overlap matrix the maximizing unitary is unique. -/
theorem tr_mul_eq_of_posDef_unitary {S U : Mat n}
    (hS : S.PosDef) (hU : Uᴴ * U = 1)
    (heq : tr (S * U) = tr S) : U = 1 := by
  let R := matrixSqrt S
  have hRR : R * R = S := matrixSqrt_mul_self hS.posSemidef
  have hRh : R.IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg S)).isHermitian
  have hex : (R - U * R) * (R - U * R)ᴴ =
      S - S * Uᴴ - U * S + U * S * Uᴴ := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hRh.eq]
    calc
      _ = R * R - (R * R) * Uᴴ - U * (R * R) + U * (R * R) * Uᴴ := by noncomm_ring
      _ = _ := by rw [hRR]
  have hlast : tr (U * S * Uᴴ) = tr S := by
    rw [tr_mul_comm, ← mul_assoc, hU, one_mul]
  have hc : tr (S * Uᴴ) = tr (S * U) := by
    rw [← tr_conjTranspose (S * Uᴴ)]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hS.isHermitian.eq]
    exact tr_mul_comm _ _
  have hzero : tr ((R - U * R) * (R - U * R)ᴴ) = 0 := by
    rw [hex, tr_add, tr_sub, tr_sub, hlast, hc, tr_mul_comm U S, heq]
    ring
  have hnorm : ‖R - U * R‖ = 0 := by
    have hsquare : ‖R - U * R‖ ^ 2 = 0 := by
      rw [frobenius_sq_eq_tr_gram]
      exact hzero
    nlinarith [norm_nonneg (R - U * R)]
  have hUR : U * R = R := by
    have := norm_eq_zero.mp hnorm
    exact sub_eq_zero.mp this |>.symm
  have hunitR : IsUnit R := by
    apply isUnit_of_mul_isUnit_left (y := R)
    rw [hRR]
    exact hS.isUnit
  exact hunitR.mul_eq_right.mp hUR

/-- For positive-definite endpoints, the unitary that maximizes the
Procrustes overlap is unique. -/
theorem unique_fidelity_alignment (A B : PositiveDefinite n)
    {U V : Mat n}
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1)
    (hUmax : tr (matrixSqrt A.val * matrixSqrt B.val * U) =
      fidelityRoot A.val B.val)
    (hVmax : tr (matrixSqrt A.val * matrixSqrt B.val * V) =
      fidelityRoot A.val B.val) : U = V := by
  let X := matrixSqrt A.val
  let Y := matrixSqrt B.val
  let S := matrixSqrt (X * B.val * X)
  have hXh : X.IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg A.val)).isHermitian
  have hYh : Y.IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg B.val)).isHermitian
  have hYY : Y * Y = B.val := matrixSqrt_mul_self B.property.posSemidef
  have hSpos : S.PosDef := by
    have hSsemi := sandwich_posSemidef A B
    have hunit : IsUnit S := by
      apply isUnit_of_mul_isUnit_left (y := S)
      rw [matrixSqrt_mul_self hSsemi]
      exact ((matrixSqrt_isUnit A).mul B.property.isUnit).mul
        (matrixSqrt_isUnit A)
    exact (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg _)).posDef_iff_isUnit.mpr
      hunit
  have hXYunit : IsUnit (X * Y) :=
    (matrixSqrt_isUnit A).mul (matrixSqrt_isUnit B)
  obtain ⟨W, hWl, hWr, hpolar⟩ := invertible_factor_polar (X * Y) hXYunit
  have hgram : (X * Y) * (X * Y)ᴴ = X * B.val * X := by
    rw [Matrix.conjTranspose_mul, hXh.eq, hYh.eq]
    calc
      X * Y * (Y * X) = X * (Y * Y) * X := by noncomm_ring
      _ = X * B.val * X := by rw [hYY]
  have hfact : X * Y = S * W := by
    simpa only [hgram] using hpolar
  have hWUunit : (W * U)ᴴ * (W * U) = 1 := by
    rw [Matrix.conjTranspose_mul]
    calc
      Uᴴ * Wᴴ * (W * U) = Uᴴ * (Wᴴ * W) * U := by noncomm_ring
      _ = 1 := by rw [hWl, mul_one, hU]
  have hWVunit : (W * V)ᴴ * (W * V) = 1 := by
    rw [Matrix.conjTranspose_mul]
    calc
      Vᴴ * Wᴴ * (W * V) = Vᴴ * (Wᴴ * W) * V := by noncomm_ring
      _ = 1 := by rw [hWl, mul_one, hV]
  have hWU : W * U = 1 := by
    apply tr_mul_eq_of_posDef_unitary hSpos hWUunit
    change tr (S * (W * U)) = tr S
    rw [← mul_assoc, ← hfact]
    exact hUmax
  have hWV : W * V = 1 := by
    apply tr_mul_eq_of_posDef_unitary hSpos hWVunit
    change tr (S * (W * V)) = tr S
    rw [← mul_assoc, ← hfact]
    exact hVmax
  have hWunit : IsUnit W := by
    apply isUnit_of_mul_isUnit_left (y := Wᴴ)
    rw [hWr]
    exact isUnit_one
  exact hWunit.mul_left_cancel (hWU.trans hWV.symm)

theorem alignment_max_of_distance_eq (A B : PositiveDefinite n)
    {U : Mat n} (hUr : U * Uᴴ = 1)
    (hd : distance A B = ‖matrixSqrt A.val - matrixSqrt B.val * U‖) :
    tr (matrixSqrt A.val * matrixSqrt B.val * U) = fidelityRoot A.val B.val := by
  have hnorm : ‖matrixSqrt A.val - matrixSqrt B.val * U‖ ^ 2 =
      tr A.val + tr B.val - 2 * tr (matrixSqrt A.val * matrixSqrt B.val * U) := by
    rw [frobenius_sq_eq_tr_gram, tr_gram_factor_difference A B U hUr]
  have hdist := distance_sq A B
  rw [hd] at hdist
  linarith

theorem unique_distance_alignment (A B : PositiveDefinite n)
    {U V : Mat n} (hUl : Uᴴ * U = 1) (hUr : U * Uᴴ = 1)
    (hVl : Vᴴ * V = 1) (hVr : V * Vᴴ = 1)
    (hU : distance A B = ‖matrixSqrt A.val - matrixSqrt B.val * U‖)
    (hV : distance A B = ‖matrixSqrt A.val - matrixSqrt B.val * V‖) :
    U = V :=
  unique_fidelity_alignment A B hUl hVl
    (alignment_max_of_distance_eq A B hUr hU)
    (alignment_max_of_distance_eq A B hVr hV)

/-- The parallelogram identity for the actual Frobenius matrix norm. -/
theorem frobenius_parallelogram (X Y : Mat n) :
    ‖X + Y‖ ^ 2 + ‖X - Y‖ ^ 2 = 2 * ‖X‖ ^ 2 + 2 * ‖Y‖ ^ 2 := by
  rw [frobenius_sq_eq_tr_gram, frobenius_sq_eq_tr_gram,
    frobenius_sq_eq_tr_gram, frobenius_sq_eq_tr_gram]
  have hgram :
      (X + Y) * (X + Y)ᴴ + (X - Y) * (X - Y)ᴴ =
      (X * Xᴴ + X * Xᴴ) + (Y * Yᴴ + Y * Yᴴ) := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_sub]
    noncomm_ring
  calc
    tr ((X + Y) * (X + Y)ᴴ) + tr ((X - Y) * (X - Y)ᴴ) =
        tr ((X + Y) * (X + Y)ᴴ + (X - Y) * (X - Y)ᴴ) := (tr_add _ _).symm
    _ = tr ((X * Xᴴ + X * Xᴴ) + (Y * Yᴴ + Y * Yᴴ)) := by rw [hgram]
    _ = 2 * tr (X * Xᴴ) + 2 * tr (Y * Yᴴ) := by rw [tr_add, tr_add, tr_add]; ring

theorem frobenius_midpoint_unique {P Q R : Mat n}
    (hPQ : ‖P - Q‖ = ‖P - R‖ / 2)
    (hQR : ‖Q - R‖ = ‖P - R‖ / 2) :
    Q = (1 / 2 : ℝ) • (P + R) := by
  have hpara := frobenius_parallelogram (P - Q) (Q - R)
  have hplus : (P - Q) + (Q - R) = P - R := by abel
  have hminus : ‖(P - Q) - (Q - R)‖ = 0 := by
    rw [hplus, hPQ, hQR] at hpara
    have hnonneg := norm_nonneg ((P - Q) - (Q - R))
    nlinarith
  have heq : P - Q = Q - R := sub_eq_zero.mp (norm_eq_zero.mp hminus)
  have htwo : (2 : ℝ) • Q = P + R := by
    calc
      (2 : ℝ) • Q = Q + Q := by module
      _ = P + R := by
        have h := congrArg (fun M : Mat n => M + Q + R) heq
        abel_nf at h ⊢
        exact h.symm
  calc
    Q = (1 / 2 : ℝ) • ((2 : ℝ) • Q) := by module
    _ = (1 / 2 : ℝ) • (P + R) := by rw [htwo]

/-- Every metric midpoint is the Gram image of the straight midpoint between
the uniquely optimally aligned square-root lifts of its endpoints. -/
theorem metric_midpoint_lift (A M B : PositiveDefinite n)
    (hM : IsMetricMidpoint A M B) :
    ∃ W : Mat n, Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧
      distance A B = ‖matrixSqrt A.val - matrixSqrt B.val * W‖ ∧
      M.val =
        ((1 / 2 : ℝ) • (matrixSqrt A.val + matrixSqrt B.val * W)) *
        ((1 / 2 : ℝ) • (matrixSqrt A.val + matrixSqrt B.val * W))ᴴ := by
  obtain ⟨U, hUl, hUr, hAM⟩ := distance_eq_frobenius_unitary A M
  obtain ⟨V, hVl, hVr, hMB⟩ := distance_eq_frobenius_unitary M B
  let X := matrixSqrt A.val
  let Y := matrixSqrt M.val * U
  let W := V * U
  let Z := matrixSqrt B.val * W
  have hWl : Wᴴ * W = 1 := by
    dsimp [W]
    rw [Matrix.conjTranspose_mul]
    calc
      Uᴴ * Vᴴ * (V * U) = Uᴴ * (Vᴴ * V) * U := by noncomm_ring
      _ = 1 := by rw [hVl, mul_one, hUl]
  have hWr : W * Wᴴ = 1 := by
    dsimp [W]
    rw [Matrix.conjTranspose_mul]
    calc
      V * U * (Uᴴ * Vᴴ) = V * (U * Uᴴ) * Vᴴ := by noncomm_ring
      _ = 1 := by rw [hUr, mul_one, hVr]
  have hXY : ‖X - Y‖ = distance A M := hAM.symm
  have hYZ : ‖Y - Z‖ = distance M B := by
    have hfactor : Y - Z = (matrixSqrt M.val - matrixSqrt B.val * V) * U := by
      dsimp [Y, Z, W]
      noncomm_ring
    rw [hfactor, frobenius_norm_mul_unitary _ U hUr]
    exact hMB.symm
  have hbound : distance A B ≤ ‖X - Z‖ :=
    distance_le_frobenius_unitary A B W hWl hWr
  have htri : ‖X - Z‖ ≤ ‖X - Y‖ + ‖Y - Z‖ := by
    calc
      ‖X - Z‖ = ‖(X - Y) + (Y - Z)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have hXZ : distance A B = ‖X - Z‖ := by
    rcases hM with ⟨hhalf1, hhalf2⟩
    rw [hXY, hYZ, hhalf1, hhalf2] at htri
    linarith
  have hmid : Y = (1 / 2 : ℝ) • (X + Z) := by
    apply frobenius_midpoint_unique
    · rw [hXY, hM.1, hXZ]
    · rw [hYZ, hM.2, hXZ]
  have hGram : Y * Yᴴ = M.val := by
    dsimp [Y]
    rw [Matrix.conjTranspose_mul]
    calc
      matrixSqrt M.val * U * (Uᴴ * (matrixSqrt M.val)ᴴ) =
          matrixSqrt M.val * (U * Uᴴ) * (matrixSqrt M.val)ᴴ := by noncomm_ring
      _ = M.val := by
        rw [hUr, mul_one,
          (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg M.val)).isHermitian.eq]
        exact matrixSqrt_mul_self M.property.posSemidef
  refine ⟨W, hWl, hWr, hXZ, ?_⟩
  change M.val = ((1 / 2 : ℝ) • (X + Z)) * ((1 / 2 : ℝ) • (X + Z))ᴴ
  rw [← hmid, hGram]

/-- The literal Bures metric has a unique midpoint between any two PD
matrices. -/
theorem metric_midpoint_unique (A B : PositiveDefinite n)
    {M N : PositiveDefinite n}
    (hM : IsMetricMidpoint A M B) (hN : IsMetricMidpoint A N B) :
    M = N := by
  obtain ⟨U, hUl, hUr, hUd, hMg⟩ := metric_midpoint_lift A M B hM
  obtain ⟨V, hVl, hVr, hVd, hNg⟩ := metric_midpoint_lift A N B hN
  have hUV : U = V := unique_distance_alignment A B hUl hUr hVl hVr hUd hVd
  subst V
  apply Subtype.ext
  exact hMg.trans hNg.symm

/-- Distance-preserving maps send the unique midpoint to the unique midpoint
of their image endpoints. -/
theorem maps_unique_metric_midpoint
    (F : PositiveDefinite n → PositiveDefinite n)
    (hF : PreservesDistance F)
    (A B : PositiveDefinite n) :
    ∃! M : PositiveDefinite n, IsMetricMidpoint (F A) M (F B) ∧
      ∀ N, IsMetricMidpoint A N B → F N = M := by
  obtain ⟨M, hM⟩ := metric_midpoint_exists A B
  refine ⟨F M, ⟨maps_metric_midpoint F hF hM, ?_⟩, ?_⟩
  · intro N hN
    rw [metric_midpoint_unique A B hN hM]
  · intro N hN
    exact metric_midpoint_unique (F A) (F B) hN.1
      (maps_metric_midpoint F hF hM)

#print axioms euclidean_midpoint_unique
#print axioms tr_mul_eq_of_posDef_unitary
#print axioms unique_fidelity_alignment
#print axioms unique_distance_alignment
#print axioms frobenius_parallelogram
#print axioms frobenius_midpoint_unique
#print axioms metric_midpoint_lift
#print axioms metric_midpoint_unique
end Bures

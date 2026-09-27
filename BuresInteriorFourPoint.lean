import BuresApexImageInterior
import BuresApexTangentTransfer

/-! Four-point contradiction when an isometric PSD self-embedding sends the
apex to a positive definite matrix. -/

noncomputable section
open Filter Asymptotics
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace Bures

theorem scaledImage_pair_tangent_error (E : PSD n → PSD n)
    (hE : ∀ X Y, psdDistance (E X) (E Y) = psdDistance X Y)
    (hP : (E psdZero).val.PosDef) (X Y : PSD n) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
      |distance (scaledImagePD E hP X t) (scaledImagePD E hP Y t) -
        frobeniusMagnitude (optimalDifferenceTangent
          (⟨(E psdZero).val, hP⟩ : PositiveDefinite n)
          (scaledImageHermitian E hP X t - scaledImageHermitian E hP Y t))| ≤
        η * |t| := by
  let P : PositiveDefinite n := ⟨(E psdZero).val, hP⟩
  let a : Hermitian n := psdHermitian (E psdZero)
  let x : ℝ → Hermitian n := scaledImageHermitian E hP X
  let y : ℝ → Hermitian n := scaledImageHermitian E hP Y
  obtain ⟨Cx, hCx, hx⟩ := scaledImageHermitian_norm_bigO E hE hP X
  obtain ⟨Cy, hCy, hy⟩ := scaledImageHermitian_norm_bigO E hE hP Y
  let C := Cx + Cy
  have hC : 0 < C := by dsimp [C]; linarith
  have hpair : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
      ‖(x t, y t) - (a, a)‖ ≤ C * |t| := by
    filter_upwards [hx, hy] with t hxt hyt
    rw [Prod.norm_def]
    change max ‖x t - a‖ ‖y t - a‖ ≤ C * |t|
    apply max_le
    · change ‖x t - a‖ ≤ C * |t|
      exact hxt.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (abs_nonneg t))
    · change ‖y t - a‖ ≤ C * |t|
      exact hyt.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (abs_nonneg t))
  have hlimit : Tendsto (fun t : ℝ => (x t, y t))
      (𝓝 (0 : ℝ)) (𝓝 (a, a)) :=
    (tendsto_scaledImageHermitian E hE hP X).prodMk_nhds
      (tendsto_scaledImageHermitian E hE hP Y)
  have hrem := (frobeniusDistance_tangent_littleO P).comp_tendsto hlimit
  have hsmall := hrem.bound (div_pos hη hC)
  filter_upwards [hsmall, hpair] with t ht hpt
  have hdist : distance (scaledImagePD E hP X t) (scaledImagePD E hP Y t) =
      frobeniusMagnitude (optimalDifferencePair (x t, y t)) := by
    have h := distance_eq_norm_optimalDifferencePair
      (scaledImagePD E hP X t) (scaledImagePD E hP Y t)
    rw [← frobeniusMagnitude_eq_norm] at h
    exact h
  rw [hdist]
  change |frobeniusMagnitude (optimalDifferencePair (x t, y t)) -
      frobeniusMagnitude (optimalDifferenceTangent P (x t - y t))| ≤
        η * |t|
  have ht' : |frobeniusMagnitude (optimalDifferencePair (x t, y t)) -
      frobeniusMagnitude (optimalDifferenceTangent P (x t - y t))| ≤
        (η / C) * ‖(x t, y t) - (a, a)‖ := by
    simpa only [Real.norm_eq_abs] using ht
  calc
    _ ≤ (η / C) * ‖(x t, y t) - (a, a)‖ := ht'
    _ ≤ (η / C) * (C * |t|) := mul_le_mul_of_nonneg_left hpt (div_pos hη hC).le
    _ = η * |t| := by field_simp [ne_of_gt hC]

def scaledTangentModel (E : PSD n → PSD n)
    (hP : (E psdZero).val.PosDef) (X : PSD n) (t : ℝ) :
    FrobeniusModel n :=
  opToFrobeniusCLM n
    (optimalDifferenceTangent (⟨(E psdZero).val, hP⟩ : PositiveDefinite n)
      (scaledImageHermitian E hP X t))

theorem scaledTangentModel_dist (E : PSD n → PSD n)
    (hP : (E psdZero).val.PosDef) (X Y : PSD n) (t : ℝ) :
    dist (scaledTangentModel E hP X t) (scaledTangentModel E hP Y t) =
      frobeniusMagnitude (optimalDifferenceTangent
        (⟨(E psdZero).val, hP⟩ : PositiveDefinite n)
        (scaledImageHermitian E hP X t - scaledImageHermitian E hP Y t)) := by
  rw [dist_eq_norm]
  change ‖opToFrobeniusCLM n
      (optimalDifferenceTangent (⟨(E psdZero).val, hP⟩ : PositiveDefinite n)
        (scaledImageHermitian E hP X t)) -
      opToFrobeniusCLM n
      (optimalDifferenceTangent (⟨(E psdZero).val, hP⟩ : PositiveDefinite n)
        (scaledImageHermitian E hP Y t))‖ = _
  rw [← map_sub, ← map_sub]
  rfl

private theorem scaled_square_error (t d m M η : ℝ)
    (hd : 0 ≤ d) (hm : 0 ≤ m) (hM : d ≤ M)
    (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (h : |m - |t| * d| ≤ η * |t|) :
    |m ^ 2 - (|t| * d) ^ 2| ≤ η * (2 * M + 1) * t ^ 2 := by
  have ht : 0 ≤ |t| := abs_nonneg t
  have hu : 0 ≤ |t| * d := mul_nonneg ht hd
  have hmupper : m ≤ (d + η) * |t| := by
    have := (abs_le.mp h).2
    nlinarith
  have hplus : m + |t| * d ≤ (2 * M + 1) * |t| := by
    have hdm : d * |t| ≤ M * |t| := mul_le_mul_of_nonneg_right hM ht
    have hηt : η * |t| ≤ |t| := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hη1) ht]
    nlinarith
  have hprod := mul_le_mul h hplus (add_nonneg hm hu) (mul_nonneg hη ht)
  have hfact : |m ^ 2 - (|t| * d) ^ 2| = |m - |t| * d| * (m + |t| * d) := by
    rw [show m ^ 2 - (|t| * d) ^ 2 = (m - |t| * d) * (m + |t| * d) by ring,
      abs_mul, abs_of_nonneg (add_nonneg hm hu)]
  rw [hfact]
  calc
    |m - |t| * d| * (m + |t| * d) ≤
        (η * |t|) * ((2 * M + 1) * |t|) := hprod
    _ = η * (2 * M + 1) * t ^ 2 := by rw [← sq_abs]; ring

theorem scaledTangentModel_squared_error (E : PSD n → PSD n)
    (hE : ∀ X Y, psdDistance (E X) (E Y) = psdDistance X Y)
    (hP : (E psdZero).val.PosDef) (X Y : PSD n)
    (M η : ℝ) (hM : psdDistance X Y ≤ M)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
      |psdDistance (psdScale (t ^ 2) (sq_nonneg t) X)
          (psdScale (t ^ 2) (sq_nonneg t) Y) ^ 2 -
        dist (scaledTangentModel E hP X t)
          (scaledTangentModel E hP Y t) ^ 2| ≤
          η * (2 * M + 1) * t ^ 2 := by
  filter_upwards [scaledImage_pair_tangent_error E hE hP X Y η hη,
    scaledImagePD_distance_pair_eventually E hE hP X Y] with t herror hdist
  rw [scaledTangentModel_dist]
  rw [hdist] at herror
  have hscaled := psdDistance_scale_pair X Y (sq_nonneg t)
  rw [Real.sqrt_sq_eq_abs] at hscaled
  rw [hscaled]
  have hs := scaled_square_error t (psdDistance X Y)
    (frobeniusMagnitude (optimalDifferenceTangent
      (⟨(E psdZero).val, hP⟩ : PositiveDefinite n)
      (scaledImageHermitian E hP X t - scaledImageHermitian E hP Y t)))
    M η (psdDistance_nonneg X Y) (by unfold frobeniusMagnitude; positivity)
    hM hη.le hη1
  have he : |frobeniusMagnitude (optimalDifferenceTangent
      (⟨(E psdZero).val, hP⟩ : PositiveDefinite n)
      (scaledImageHermitian E hP X t - scaledImageHermitian E hP Y t)) -
      |t| * psdDistance X Y| ≤ η * |t| := by
    simpa only [abs_sub_comm] using herror
  simpa only [abs_sub_comm] using hs he

/-- A distance-preserving embedding of the 2×2 Bures PSD cone cannot send
its apex to a positive definite matrix. This uses the explicit four-point
obstruction and the proved Euclidean tangent expansion at interior points. -/
theorem psd_isometry_apex_not_posDef (E : PSD 2 → PSD 2)
    (hE : ∀ X Y, psdDistance (E X) (E Y) = psdDistance X Y) :
    ¬ (E psdZero).val.PosDef := by
  intro hP
  obtain ⟨A, B, C, D, hbad⟩ := four_point_non_euclidean
  let defect : ℝ := psdDistance A C ^ 2 + psdDistance B D ^ 2 -
    psdDistance A B ^ 2 - psdDistance B C ^ 2 -
    psdDistance C D ^ 2 - psdDistance D A ^ 2
  let M : ℝ := psdDistance A C + psdDistance B D +
    psdDistance A B + psdDistance B C +
    psdDistance C D + psdDistance D A
  have hAC : psdDistance A C ≤ M := by
    dsimp [M]
    nlinarith [psdDistance_nonneg B D, psdDistance_nonneg A B,
      psdDistance_nonneg B C, psdDistance_nonneg C D,
      psdDistance_nonneg D A]
  have hBD : psdDistance B D ≤ M := by
    dsimp [M]
    nlinarith [psdDistance_nonneg A C, psdDistance_nonneg A B,
      psdDistance_nonneg B C, psdDistance_nonneg C D,
      psdDistance_nonneg D A]
  have hAB : psdDistance A B ≤ M := by
    dsimp [M]
    nlinarith [psdDistance_nonneg A C, psdDistance_nonneg B D,
      psdDistance_nonneg B C, psdDistance_nonneg C D,
      psdDistance_nonneg D A]
  have hBC : psdDistance B C ≤ M := by
    dsimp [M]
    nlinarith [psdDistance_nonneg A C, psdDistance_nonneg B D,
      psdDistance_nonneg A B, psdDistance_nonneg C D,
      psdDistance_nonneg D A]
  have hCD : psdDistance C D ≤ M := by
    dsimp [M]
    nlinarith [psdDistance_nonneg A C, psdDistance_nonneg B D,
      psdDistance_nonneg A B, psdDistance_nonneg B C,
      psdDistance_nonneg D A]
  have hDA : psdDistance D A ≤ M := by
    dsimp [M]
    nlinarith [psdDistance_nonneg A C, psdDistance_nonneg B D,
      psdDistance_nonneg A B, psdDistance_nonneg B C,
      psdDistance_nonneg C D]
  have hM : 0 ≤ M := le_trans (psdDistance_nonneg A C) hAC
  let η : ℝ := min 1 (defect / (12 * (2 * M + 1)))
  have hden : 0 < 12 * (2 * M + 1) := by positivity
  have hη : 0 < η := lt_min zero_lt_one (div_pos hbad hden)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηsmall : 6 * η * (2 * M + 1) < defect := by
    have hq : η ≤ defect / (12 * (2 * M + 1)) := min_le_right _ _
    have hm := (le_div_iff₀ hden).mp hq
    nlinarith
  have eAC := scaledTangentModel_squared_error E hE hP A C M η hAC hη hη1
  have eBD := scaledTangentModel_squared_error E hE hP B D M η hBD hη hη1
  have eAB := scaledTangentModel_squared_error E hE hP A B M η hAB hη hη1
  have eBC := scaledTangentModel_squared_error E hE hP B C M η hBC hη hη1
  have eCD := scaledTangentModel_squared_error E hE hP C D M η hCD hη hη1
  have eDA := scaledTangentModel_squared_error E hE hP D A M η hDA hη hη1
  have eall : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ),
      t ≠ 0 ∧
      |psdDistance (psdScale (t ^ 2) (sq_nonneg t) A)
          (psdScale (t ^ 2) (sq_nonneg t) C) ^ 2 -
        dist (scaledTangentModel E hP A t) (scaledTangentModel E hP C t) ^ 2| ≤
        η * (2 * M + 1) * t ^ 2 ∧
      |psdDistance (psdScale (t ^ 2) (sq_nonneg t) B)
          (psdScale (t ^ 2) (sq_nonneg t) D) ^ 2 -
        dist (scaledTangentModel E hP B t) (scaledTangentModel E hP D t) ^ 2| ≤
        η * (2 * M + 1) * t ^ 2 ∧
      |psdDistance (psdScale (t ^ 2) (sq_nonneg t) A)
          (psdScale (t ^ 2) (sq_nonneg t) B) ^ 2 -
        dist (scaledTangentModel E hP A t) (scaledTangentModel E hP B t) ^ 2| ≤
        η * (2 * M + 1) * t ^ 2 ∧
      |psdDistance (psdScale (t ^ 2) (sq_nonneg t) B)
          (psdScale (t ^ 2) (sq_nonneg t) C) ^ 2 -
        dist (scaledTangentModel E hP B t) (scaledTangentModel E hP C t) ^ 2| ≤
        η * (2 * M + 1) * t ^ 2 ∧
      |psdDistance (psdScale (t ^ 2) (sq_nonneg t) C)
          (psdScale (t ^ 2) (sq_nonneg t) D) ^ 2 -
        dist (scaledTangentModel E hP C t) (scaledTangentModel E hP D t) ^ 2| ≤
        η * (2 * M + 1) * t ^ 2 ∧
      |psdDistance (psdScale (t ^ 2) (sq_nonneg t) D)
          (psdScale (t ^ 2) (sq_nonneg t) A) ^ 2 -
        dist (scaledTangentModel E hP D t) (scaledTangentModel E hP A t) ^ 2| ≤
        η * (2 * M + 1) * t ^ 2 := by
    filter_upwards [self_mem_nhdsWithin,
      eAC.filter_mono nhdsWithin_le_nhds,
      eBD.filter_mono nhdsWithin_le_nhds,
      eAB.filter_mono nhdsWithin_le_nhds,
      eBC.filter_mono nhdsWithin_le_nhds,
      eCD.filter_mono nhdsWithin_le_nhds,
      eDA.filter_mono nhdsWithin_le_nhds] with t ht h1 h2 h3 h4 h5 h6
    exact ⟨ht, h1, h2, h3, h4, h5, h6⟩
  obtain ⟨t, ht, e1, e2, e3, e4, e5, e6⟩ := eall.exists
  have hfour := four_point_defect_le_six_error
    (psdScale (t ^ 2) (sq_nonneg t) A)
    (psdScale (t ^ 2) (sq_nonneg t) B)
    (psdScale (t ^ 2) (sq_nonneg t) C)
    (psdScale (t ^ 2) (sq_nonneg t) D)
    (scaledTangentModel E hP A t)
    (scaledTangentModel E hP B t)
    (scaledTangentModel E hP C t)
    (scaledTangentModel E hP D t)
    (η * (2 * M + 1) * t ^ 2) e1 e2 e3 e4 e5 e6
  have hscale : psdDistance (psdScale (t ^ 2) (sq_nonneg t) A)
          (psdScale (t ^ 2) (sq_nonneg t) C) ^ 2 +
      psdDistance (psdScale (t ^ 2) (sq_nonneg t) B)
          (psdScale (t ^ 2) (sq_nonneg t) D) ^ 2 -
      psdDistance (psdScale (t ^ 2) (sq_nonneg t) A)
          (psdScale (t ^ 2) (sq_nonneg t) B) ^ 2 -
      psdDistance (psdScale (t ^ 2) (sq_nonneg t) B)
          (psdScale (t ^ 2) (sq_nonneg t) C) ^ 2 -
      psdDistance (psdScale (t ^ 2) (sq_nonneg t) C)
          (psdScale (t ^ 2) (sq_nonneg t) D) ^ 2 -
      psdDistance (psdScale (t ^ 2) (sq_nonneg t) D)
          (psdScale (t ^ 2) (sq_nonneg t) A) ^ 2 = t ^ 2 * defect := by
    simp only [psdDistance_scale_pair (hc := sq_nonneg t),
      Real.sqrt_sq_eq_abs, mul_pow, sq_abs]
    ring
  rw [hscale] at hfour
  have htsq : 0 < t ^ 2 := sq_pos_of_ne_zero ht
  have hcontra := mul_lt_mul_of_pos_right hηsmall htsq
  nlinarith

#print axioms scaledImage_pair_tangent_error
#print axioms scaledTangentModel_squared_error
#print axioms psd_isometry_apex_not_posDef

end Bures

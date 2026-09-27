import BuresQubitTangent
import BuresQubitUnitary
import BuresInteriorFourPoint
import BuresExtension

/-! A four-point obstruction at a diagonal rank-one qubit apex. -/

noncomputable section
open Filter
open scoped Topology MatrixOrder ComplexOrder
namespace Bures

theorem psd_isometry_apex_not_diagonal_rank_one (E : PSD 2 → PSD 2)
    (hE : ∀ X Y, psdDistance (E X) (E Y) = psdDistance X Y)
    (x₀ : ℝ) (hx₀ : 0 < x₀) :
    E psdZero ≠ qubitGram x₀ 0 0 := by
  intro hP
  obtain ⟨A, B, C, D, hbad⟩ := four_point_non_euclidean
  let defect : ℝ := psdDistance A C ^ 2 + psdDistance B D ^ 2 -
    psdDistance A B ^ 2 - psdDistance B C ^ 2 -
    psdDistance C D ^ 2 - psdDistance D A ^ 2
  let R : ℝ := 1 + psdDistance psdZero A + psdDistance psdZero B +
    psdDistance psdZero C + psdDistance psdZero D
  have hRA : psdDistance psdZero A ≤ R := by
    dsimp [R]
    nlinarith [psdDistance_nonneg psdZero B,
      psdDistance_nonneg psdZero C, psdDistance_nonneg psdZero D]
  have hRB : psdDistance psdZero B ≤ R := by
    dsimp [R]
    nlinarith [psdDistance_nonneg psdZero A,
      psdDistance_nonneg psdZero C, psdDistance_nonneg psdZero D]
  have hRC : psdDistance psdZero C ≤ R := by
    dsimp [R]
    nlinarith [psdDistance_nonneg psdZero A,
      psdDistance_nonneg psdZero B, psdDistance_nonneg psdZero D]
  have hRD : psdDistance psdZero D ≤ R := by
    dsimp [R]
    nlinarith [psdDistance_nonneg psdZero A,
      psdDistance_nonneg psdZero B, psdDistance_nonneg psdZero C]
  have eAC := scaledImageQubit_pair_error E hE x₀ hx₀ hP A C R hRA hRC
  have eBD := scaledImageQubit_pair_error E hE x₀ hx₀ hP B D R hRB hRD
  have eAB := scaledImageQubit_pair_error E hE x₀ hx₀ hP A B R hRA hRB
  have eBC := scaledImageQubit_pair_error E hE x₀ hx₀ hP B C R hRB hRC
  have eCD := scaledImageQubit_pair_error E hE x₀ hx₀ hP C D R hRC hRD
  have eDA := scaledImageQubit_pair_error E hE x₀ hx₀ hP D A R hRD hRA
  let η : ℝ → ℝ := fun t => 2 * (5 * (|t| * R) ^ 4) / (x₀ ^ 2 / 8)
  let K : ℝ := 60 * R ^ 4 / (x₀ ^ 2 / 8)
  have hsmall : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), K * t ^ 2 < defect := by
    have ht : Tendsto (fun t : ℝ => K * t ^ 2) (𝓝 (0 : ℝ)) (𝓝 0) := by
      have hc : Continuous (fun t : ℝ => K * t ^ 2) :=
        continuous_const.mul (continuous_id.pow 2)
      simpa using hc.tendsto (0 : ℝ)
    exact ht.eventually (Iio_mem_nhds hbad)
  have eall : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ),
      t ≠ 0 ∧ K * t ^ 2 < defect ∧
      |psdDistance (psdScale (t ^ 2) (sq_nonneg t) A)
          (psdScale (t ^ 2) (sq_nonneg t) C) ^ 2 -
        dist (scaledImageQubitModel E A t) (scaledImageQubitModel E C t) ^ 2| ≤ η t ∧
      |psdDistance (psdScale (t ^ 2) (sq_nonneg t) B)
          (psdScale (t ^ 2) (sq_nonneg t) D) ^ 2 -
        dist (scaledImageQubitModel E B t) (scaledImageQubitModel E D t) ^ 2| ≤ η t ∧
      |psdDistance (psdScale (t ^ 2) (sq_nonneg t) A)
          (psdScale (t ^ 2) (sq_nonneg t) B) ^ 2 -
        dist (scaledImageQubitModel E A t) (scaledImageQubitModel E B t) ^ 2| ≤ η t ∧
      |psdDistance (psdScale (t ^ 2) (sq_nonneg t) B)
          (psdScale (t ^ 2) (sq_nonneg t) C) ^ 2 -
        dist (scaledImageQubitModel E B t) (scaledImageQubitModel E C t) ^ 2| ≤ η t ∧
      |psdDistance (psdScale (t ^ 2) (sq_nonneg t) C)
          (psdScale (t ^ 2) (sq_nonneg t) D) ^ 2 -
        dist (scaledImageQubitModel E C t) (scaledImageQubitModel E D t) ^ 2| ≤ η t ∧
      |psdDistance (psdScale (t ^ 2) (sq_nonneg t) D)
          (psdScale (t ^ 2) (sq_nonneg t) A) ^ 2 -
        dist (scaledImageQubitModel E D t) (scaledImageQubitModel E A t) ^ 2| ≤ η t := by
    filter_upwards [self_mem_nhdsWithin, hsmall.filter_mono nhdsWithin_le_nhds,
      eAC.filter_mono nhdsWithin_le_nhds,
      eBD.filter_mono nhdsWithin_le_nhds,
      eAB.filter_mono nhdsWithin_le_nhds,
      eBC.filter_mono nhdsWithin_le_nhds,
      eCD.filter_mono nhdsWithin_le_nhds,
      eDA.filter_mono nhdsWithin_le_nhds] with t ht hkt h1 h2 h3 h4 h5 h6
    exact ⟨ht, hkt, h1, h2, h3, h4, h5, h6⟩
  obtain ⟨t, ht, hkt, h1, h2, h3, h4, h5, h6⟩ := eall.exists
  have hfour := four_point_defect_le_six_error
    (psdScale (t ^ 2) (sq_nonneg t) A)
    (psdScale (t ^ 2) (sq_nonneg t) B)
    (psdScale (t ^ 2) (sq_nonneg t) C)
    (psdScale (t ^ 2) (sq_nonneg t) D)
    (scaledImageQubitModel E A t) (scaledImageQubitModel E B t)
    (scaledImageQubitModel E C t) (scaledImageQubitModel E D t)
    (η t) h1 h2 h3 h4 h5 h6
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
  have hη : 6 * η t = K * t ^ 4 := by
    dsimp [η, K]
    rw [mul_pow, show |t| ^ 4 = t ^ 4 by nlinarith [sq_abs t]]
    ring
  rw [hη] at hfour
  have htsq : 0 < t ^ 2 := sq_pos_of_ne_zero ht
  have hcontra := mul_lt_mul_of_pos_right hkt htsq
  nlinarith

#print axioms psd_isometry_apex_not_diagonal_rank_one

/-- An arbitrary Bures-isometric self-map of the qubit PSD cone fixes the
zero matrix. No surjectivity or trace hypothesis is assumed. -/
theorem psd_isometry_apex_eq_zero (E : PSD 2 → PSD 2)
    (hE : ∀ X Y, psdDistance (E X) (E Y) = psdDistance X Y) :
    E psdZero = psdZero := by
  by_contra hzero
  have hbdry : ¬ (E psdZero).val.PosDef :=
    psd_isometry_apex_not_posDef E hE
  obtain ⟨x₀, U, hx₀, hUl, hUr, hdiag⟩ :=
    rankOne_psd_unitary_diagonal (E psdZero) hzero hbdry
  let G : PSD 2 → PSD 2 := fun A => unitaryConjPSD U (E A)
  have hG : ∀ X Y, psdDistance (G X) (G Y) = psdDistance X Y := by
    intro X Y
    change psdDistance (unitaryConjPSD U (E X))
      (unitaryConjPSD U (E Y)) = psdDistance X Y
    rw [psdDistance_unitaryConj U (E X) (E Y) hUl hUr, hE]
  have hGzero : G psdZero = qubitGram x₀ 0 0 := hdiag
  exact (psd_isometry_apex_not_diagonal_rank_one G hG x₀ hx₀) hGzero

#print axioms psd_isometry_apex_eq_zero

/-- The literature's automatic-surjectivity question is answered in matrix
size two using the literal Bures–Wasserstein distance. -/
theorem automatic_surjectivity_two (F : PositiveDefinite 2 → PositiveDefinite 2)
    (hF : PreservesDistance F) : Function.Surjective F := by
  letI : MetricSpace (PSD 2) := psdMetricSpace 2
  obtain ⟨E, hE, hext⟩ := exists_psd_isometric_extension F hF
  have hzero : E psdZero = psdZero := psd_isometry_apex_eq_zero E hE.dist_eq
  have htraceE := preserves_trace_of_psdZero_fixed E hE.dist_eq hzero
  have htraceF : ∀ A : PositiveDefinite 2, tr (F A).val = tr A.val := by
    intro A
    have h := htraceE (pdInclusion A)
    rw [hext A] at h
    simpa [pdInclusion] using h
  exact surjective_of_preserves_trace F hF htraceF

#print axioms automatic_surjectivity_two

end Bures

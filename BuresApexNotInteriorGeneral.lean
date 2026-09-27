import BuresInteriorFourPoint
import BuresFourPointGeneral

noncomputable section
open scoped MatrixOrder ComplexOrder Topology
open Filter
namespace Bures

theorem four_point_defect_le_six_error_any_size {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A B C D : PSD n) (a b c d : E) (η : ℝ)
    (hAC : |psdDistance A C ^ 2 - dist a c ^ 2| ≤ η)
    (hBD : |psdDistance B D ^ 2 - dist b d ^ 2| ≤ η)
    (hAB : |psdDistance A B ^ 2 - dist a b ^ 2| ≤ η)
    (hBC : |psdDistance B C ^ 2 - dist b c ^ 2| ≤ η)
    (hCD : |psdDistance C D ^ 2 - dist c d ^ 2| ≤ η)
    (hDA : |psdDistance D A ^ 2 - dist d a ^ 2| ≤ η) :
    psdDistance A C ^ 2 + psdDistance B D ^ 2 -
      psdDistance A B ^ 2 - psdDistance B C ^ 2 -
      psdDistance C D ^ 2 - psdDistance D A ^ 2 ≤ 6 * η := by
  have hgood := hilbert_four_point a b c d
  have hAC' := (abs_le.mp hAC).2
  have hBD' := (abs_le.mp hBD).2
  have hAB' := (abs_le.mp hAB).1
  have hBC' := (abs_le.mp hBC).1
  have hCD' := (abs_le.mp hCD).1
  have hDA' := (abs_le.mp hDA).1
  linarith

theorem psd_isometry_apex_not_posDef_any_size (n : ℕ) (hn : 2 ≤ n)
    (E : PSD n → PSD n)
    (hE : ∀ X Y, psdDistance (E X) (E Y) = psdDistance X Y) :
    ¬ (E psdZero).val.PosDef := by
  intro hP
  obtain ⟨A, B, C, D, hbad⟩ := four_point_non_euclidean_any_size n hn
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
  have hfour := four_point_defect_le_six_error_any_size
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


#print axioms four_point_defect_le_six_error_any_size
#print axioms psd_isometry_apex_not_posDef_any_size

end Bures

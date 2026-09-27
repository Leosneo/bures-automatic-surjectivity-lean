import BuresQubitFidelity
import BuresNormComparison
import BuresApexTangentTransfer
import BuresPSDMetric

/-! Euclidean tangent coordinates at a diagonal rank-one qubit matrix. -/

noncomputable section
open Filter
open scoped MatrixOrder ComplexOrder Matrix.Norms.Frobenius Topology
namespace Bures

structure QubitChart (A : PSD 2) where
  x : ℝ
  v : ℂ
  w : ℝ
  hx : 0 < x
  hw : 0 ≤ w
  gram : A = qubitGram x v w

def qubitChart (A : PSD 2) (hA : 0 < (A.val 0 0).re) : QubitChart A := by
  apply Classical.choice
  obtain ⟨x, v, w, hx, hw, hgram⟩ := qubitGram_covers_pos_first_diag A hA
  exact ⟨⟨x, v, w, hx, hw, hgram⟩⟩

def qubitChartLift (A : PSD 2) (hA : 0 < (A.val 0 0).re) :
    FrobeniusModel 2 :=
  opToFrobeniusCLM 2
    (qubitCholesky (qubitChart A hA).x (qubitChart A hA).v (qubitChart A hA).w)

theorem qubitCholesky_frobenius_dist_sq (x y w z : ℝ) (v u : ℂ) :
    dist (opToFrobeniusCLM 2 (qubitCholesky x v w))
      (opToFrobeniusCLM 2 (qubitCholesky y u z)) ^ 2 =
      (x - y) ^ 2 + Complex.normSq (v - u) + (w - z) ^ 2 := by
  rw [dist_eq_norm, ← map_sub]
  change frobeniusMagnitude (qubitCholesky x v w - qubitCholesky y u z) ^ 2 = _
  rw [frobeniusMagnitude_eq_norm, frobenius_sq_eq_tr_gram]
  simp [tr, Matrix.trace_fin_two, Matrix.vecMul, dotProduct,
    Fin.sum_univ_two, qubitCholesky, Complex.normSq_apply, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  ring

theorem qubitLiftPairing_near_diagonal_rank_one (x₀ δ x y w z : ℝ) (v u : ℂ)
    (hx₀ : 0 < x₀) (hδ : δ ≤ x₀ / 4)
    (hx : |x - x₀| ≤ δ) (hy : |y - x₀| ≤ δ)
    (hv : Complex.normSq v ≤ δ ^ 2) (hu : Complex.normSq u ≤ δ ^ 2)
    (hw : 0 ≤ w) (hz : 0 ≤ z) :
    x₀ ^ 2 / 8 ≤ qubitLiftPairing x y w z v u := by
  have hxlow : x₀ / 2 ≤ x := by
    have h := (abs_le.mp hx).1
    linarith
  have hylow : x₀ / 2 ≤ y := by
    have h := (abs_le.mp hy).1
    linarith
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) hx
  have hδsq : δ ^ 2 ≤ x₀ ^ 2 / 16 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hδ) (add_nonneg hδ0 (by linarith : 0 ≤ x₀ / 4))]
  have hxy : x₀ ^ 2 / 4 ≤ x * y := by
    have h := mul_le_mul hxlow hylow (by linarith : 0 ≤ x₀ / 2) (by linarith : 0 ≤ x)
    nlinarith
  have hpair := qubitLiftPairing_lower x y w z v u
  have hwz : 0 ≤ w * z := mul_nonneg hw hz
  nlinarith

theorem qubitGram_pair_tangent_error (x₀ δ x y w z : ℝ) (v u : ℂ)
    (hx₀ : 0 < x₀) (hδ : δ ≤ x₀ / 4)
    (hx : |x - x₀| ≤ δ) (hy : |y - x₀| ≤ δ)
    (hv : Complex.normSq v ≤ δ ^ 2) (hu : Complex.normSq u ≤ δ ^ 2)
    (hw : 0 ≤ w) (hz : 0 ≤ z)
    (hwδ : w ^ 2 ≤ δ ^ 2) (hzδ : z ^ 2 ≤ δ ^ 2) :
    |psdDistance (qubitGram x v w) (qubitGram y u z) ^ 2 -
      dist (opToFrobeniusCLM 2 (qubitCholesky x v w))
        (opToFrobeniusCLM 2 (qubitCholesky y u z)) ^ 2| ≤
          2 * (5 * δ ^ 4) / (x₀ ^ 2 / 8) := by
  have hα := qubitLiftPairing_near_diagonal_rank_one x₀ δ x y w z v u
    hx₀ hδ hx hy hv hu hw hz
  have hden : 0 < x₀ ^ 2 / 8 := by positivity
  have hαpos : 0 < qubitLiftPairing x y w z v u := lt_of_lt_of_le hden hα
  have hxnonneg : 0 ≤ x := by
    have h := (abs_le.mp hx).1
    linarith
  have hynonneg : 0 ≤ y := by
    have h := (abs_le.mp hy).1
    linarith
  have herr := qubitGram_distance_sq_error_bound x y w z v u
    hxnonneg hynonneg hw hz hαpos
  have hβ := qubitLiftDefect_le_five_pow_four δ w z v u hv hu hwδ hzδ
  have hβ0 := qubitLiftDefect_nonneg w z v u
  have hδ4 : 0 ≤ 5 * δ ^ 4 := by positivity
  have hdiv : qubitLiftDefect w z v u / qubitLiftPairing x y w z v u ≤
      (5 * δ ^ 4) / (x₀ ^ 2 / 8) := by
    apply (div_le_div_iff₀ hαpos hden).2
    calc
      qubitLiftDefect w z v u * (x₀ ^ 2 / 8) ≤
          (5 * δ ^ 4) * (x₀ ^ 2 / 8) :=
        mul_le_mul_of_nonneg_right hβ hden.le
      _ ≤ (5 * δ ^ 4) * qubitLiftPairing x y w z v u :=
        mul_le_mul_of_nonneg_left hα hδ4
  rw [qubitCholesky_frobenius_dist_sq]
  have hsign := herr.1
  rw [abs_sub_comm, abs_of_nonneg hsign]
  calc
    _ ≤ 2 * qubitLiftDefect w z v u / qubitLiftPairing x y w z v u := herr.2
    _ = 2 * (qubitLiftDefect w z v u /
      qubitLiftPairing x y w z v u) := by ring
    _ ≤ 2 * ((5 * δ ^ 4) / (x₀ ^ 2 / 8)) :=
      mul_le_mul_of_nonneg_left hdiv (by norm_num)
    _ = _ := by ring

private theorem chart_coordinate_bounds (x₀ δ : ℝ) (A : PSD 2)
    (hx₀ : 0 ≤ x₀) (hδ : 0 ≤ δ) (hA : 0 < (A.val 0 0).re)
    (hnear : psdDistance (qubitGram x₀ 0 0) A ≤ δ) :
    |(qubitChart A hA).x - x₀| ≤ δ ∧
      Complex.normSq (qubitChart A hA).v ≤ δ ^ 2 ∧
      (qubitChart A hA).w ^ 2 ≤ δ ^ 2 := by
  let c := qubitChart A hA
  have hdist : psdDistance (qubitGram x₀ 0 0) A ^ 2 =
      (x₀ - c.x) ^ 2 + Complex.normSq c.v + c.w ^ 2 := by
    calc
      _ = psdDistance (qubitGram x₀ 0 0) (qubitGram c.x c.v c.w) ^ 2 :=
        congrArg (fun Z : PSD 2 => psdDistance (qubitGram x₀ 0 0) Z ^ 2) c.gram
      _ = _ := qubitGram_distance_sq_from_diagonal_rank_one x₀ c.x c.w c.v
        hx₀ c.hx.le c.hw
  have hnear_sq : psdDistance (qubitGram x₀ 0 0) A ^ 2 ≤ δ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hnear)
      (add_nonneg (psdDistance_nonneg (qubitGram x₀ 0 0) A) hδ)]
  have hv0 := Complex.normSq_nonneg c.v
  have hxsq : (x₀ - c.x) ^ 2 ≤ δ ^ 2 := by nlinarith [sq_nonneg c.w]
  have hvsq : Complex.normSq c.v ≤ δ ^ 2 := by
    nlinarith [sq_nonneg (x₀ - c.x), sq_nonneg c.w]
  have hwsq : c.w ^ 2 ≤ δ ^ 2 := by
    nlinarith [sq_nonneg (x₀ - c.x)]
  have hxabs : |c.x - x₀| ≤ δ := by
    have habs : |c.x - x₀| ^ 2 ≤ δ ^ 2 := by
      simpa only [sq_abs, sub_sq_comm] using hxsq
    nlinarith [abs_nonneg (c.x - x₀)]
  exact ⟨hxabs, hvsq, hwsq⟩

/-- A uniform two-point Hilbert approximation throughout a small Bures ball
around a diagonal rank-one qubit. The error is fourth order in the ball radius. -/
theorem qubit_rank_one_pair_tangent_error (x₀ δ : ℝ) (A B : PSD 2)
    (hx₀ : 0 < x₀) (hδ : 0 ≤ δ) (hsmall : δ ≤ x₀ / 4)
    (hA : 0 < (A.val 0 0).re) (hB : 0 < (B.val 0 0).re)
    (hnearA : psdDistance (qubitGram x₀ 0 0) A ≤ δ)
    (hnearB : psdDistance (qubitGram x₀ 0 0) B ≤ δ) :
    |psdDistance A B ^ 2 -
      dist (qubitChartLift A hA) (qubitChartLift B hB) ^ 2| ≤
        2 * (5 * δ ^ 4) / (x₀ ^ 2 / 8) := by
  let c := qubitChart A hA
  let d := qubitChart B hB
  obtain ⟨hcx, hcv, hcw⟩ := chart_coordinate_bounds x₀ δ A hx₀.le hδ hA hnearA
  obtain ⟨hdx, hdv, hdw⟩ := chart_coordinate_bounds x₀ δ B hx₀.le hδ hB hnearB
  change |psdDistance A B ^ 2 -
    dist (opToFrobeniusCLM 2 (qubitCholesky c.x c.v c.w))
      (opToFrobeniusCLM 2 (qubitCholesky d.x d.v d.w)) ^ 2| ≤ _
  have h := qubitGram_pair_tangent_error x₀ δ c.x d.x c.w d.w c.v d.v
    hx₀ hsmall hcx hdx hcv hdv c.hw d.hw hcw hdw
  have heqA : A = qubitGram c.x c.v c.w := c.gram
  have heqB : B = qubitGram d.x d.v d.w := d.gram
  have heqdist : psdDistance A B =
      psdDistance (qubitGram c.x c.v c.w) (qubitGram d.x d.v d.w) :=
    congrArg₂ psdDistance heqA heqB
  rw [heqdist]
  exact h

theorem diagonal_rank_one_first_diag_pos (x₀ : ℝ) (hx₀ : 0 < x₀) :
    0 < ((qubitGram x₀ 0 0).val 0 0).re := by
  rw [qubitGram_entries]
  norm_num
  exact ne_of_gt hx₀

theorem isometry_scaled_eventually_first_diag_pos (E : PSD 2 → PSD 2)
    (hE : ∀ A B, psdDistance (E A) (E B) = psdDistance A B)
    (x₀ : ℝ) (hx₀ : 0 < x₀)
    (hP : E psdZero = qubitGram x₀ 0 0) (X : PSD 2) :
    ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
      0 < ((E (psdScale (t ^ 2) (sq_nonneg t) X)).val 0 0).re := by
  letI : MetricSpace (PSD 2) := psdMetricSpace 2
  letI : PseudoMetricSpace (PSD 2) := (psdMetricSpace 2).toPseudoMetricSpace
  letI : PseudoEMetricSpace (PSD 2) :=
    (psdMetricSpace 2).toPseudoMetricSpace.toPseudoEMetricSpace
  letI : UniformSpace (PSD 2) :=
    (psdMetricSpace 2).toPseudoMetricSpace.toUniformSpace
  have hi : Isometry E := by
    apply Isometry.of_dist_eq
    intro U V
    change psdDistance (E U) (E V) = psdDistance U V
    exact hE U V
  have ht : Tendsto (fun t : ℝ => E (psdScale (t ^ 2) (sq_nonneg t) X))
      (𝓝 (0 : ℝ)) (𝓝 (qubitGram x₀ 0 0)) := by
    rw [← hP]
    exact (hi.continuous.tendsto psdZero).comp (tendsto_psdScale_sq_zero X)
  have hcont : Continuous (fun Z : PSD 2 => (Z.val 0 0).re) := by
    exact Complex.continuous_re.comp
      (((continuous_apply (0 : Fin 2)).comp
        ((continuous_apply (0 : Fin 2)).comp continuous_subtype_val)))
  exact ((hcont.tendsto _).comp ht).eventually
    (Ioi_mem_nhds (diagonal_rank_one_first_diag_pos x₀ hx₀))

def scaledImageQubitModel (E : PSD 2 → PSD 2) (X : PSD 2) (t : ℝ) :
    FrobeniusModel 2 :=
  if h : 0 < ((E (psdScale (t ^ 2) (sq_nonneg t) X)).val 0 0).re then
    qubitChartLift (E (psdScale (t ^ 2) (sq_nonneg t) X)) h
  else 0

theorem scaledImageQubit_pair_error (E : PSD 2 → PSD 2)
    (hE : ∀ A B, psdDistance (E A) (E B) = psdDistance A B)
    (x₀ : ℝ) (hx₀ : 0 < x₀)
    (hP : E psdZero = qubitGram x₀ 0 0)
    (X Y : PSD 2) (R : ℝ)
    (hRX : psdDistance psdZero X ≤ R)
    (hRY : psdDistance psdZero Y ≤ R) :
    ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
      |psdDistance (psdScale (t ^ 2) (sq_nonneg t) X)
          (psdScale (t ^ 2) (sq_nonneg t) Y) ^ 2 -
        dist (scaledImageQubitModel E X t) (scaledImageQubitModel E Y t) ^ 2| ≤
          2 * (5 * (|t| * R) ^ 4) / (x₀ ^ 2 / 8) := by
  have hR : 0 ≤ R := le_trans (psdDistance_nonneg psdZero X) hRX
  have hsmall : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), |t| * R ≤ x₀ / 4 := by
    have ht : Tendsto (fun t : ℝ => |t| * R) (𝓝 (0 : ℝ)) (𝓝 0) := by
      have hc : Continuous (fun t : ℝ => |t| * R) :=
        continuous_abs.mul continuous_const
      simpa only [abs_zero, zero_mul] using hc.tendsto (0 : ℝ)
    exact ht.eventually (Iic_mem_nhds (by linarith : (0 : ℝ) < x₀ / 4))
  filter_upwards [isometry_scaled_eventually_first_diag_pos E hE x₀ hx₀ hP X,
    isometry_scaled_eventually_first_diag_pos E hE x₀ hx₀ hP Y,
    hsmall] with t htX htY htsmall
  let A := E (psdScale (t ^ 2) (sq_nonneg t) X)
  let B := E (psdScale (t ^ 2) (sq_nonneg t) Y)
  have hdistX : psdDistance (qubitGram x₀ 0 0) A =
      |t| * psdDistance psdZero X := by
    rw [← hP, hE, psdDistance_comm, psdDistance_scale_zero,
      Real.sqrt_sq_eq_abs, psdDistance_comm]
  have hdistY : psdDistance (qubitGram x₀ 0 0) B =
      |t| * psdDistance psdZero Y := by
    rw [← hP, hE, psdDistance_comm, psdDistance_scale_zero,
      Real.sqrt_sq_eq_abs, psdDistance_comm]
  have hnearX : psdDistance (qubitGram x₀ 0 0) A ≤ |t| * R := by
    rw [hdistX]
    exact mul_le_mul_of_nonneg_left hRX (abs_nonneg t)
  have hnearY : psdDistance (qubitGram x₀ 0 0) B ≤ |t| * R := by
    rw [hdistY]
    exact mul_le_mul_of_nonneg_left hRY (abs_nonneg t)
  have hpair := qubit_rank_one_pair_tangent_error x₀ (|t| * R) A B
    hx₀ (mul_nonneg (abs_nonneg t) hR) htsmall htX htY hnearX hnearY
  have hdistance : psdDistance A B =
      psdDistance (psdScale (t ^ 2) (sq_nonneg t) X)
        (psdScale (t ^ 2) (sq_nonneg t) Y) := hE _ _
  rw [← hdistance]
  simpa [scaledImageQubitModel, htX, htY] using hpair

end Bures

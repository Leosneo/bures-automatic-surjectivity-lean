import BuresInteriorTangent
import BuresPSDMetric

/-! A PSD isometric embedding taking the apex into the positive definite
interior sends sufficiently small radial points into that interior. -/

noncomputable section
open Filter
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace Bures

def psdHermitian (X : PSD n) : Hermitian n :=
  ⟨X.val, X.property.isHermitian⟩

theorem continuous_psdHermitian : Continuous (psdHermitian (n := n)) := by
  exact continuous_subtype_val.subtype_mk _

theorem psd_posDef_mem_nhds (P : PSD n) (hP : P.val.PosDef) :
    {X : PSD n | X.val.PosDef} ∈ 𝓝 P := by
  have h := hermitianPosDef_mem_nhds (psdHermitian P) hP
  exact (continuous_psdHermitian.tendsto P).eventually h

theorem psd_isometry_scaled_eventually_posDef (E : PSD n → PSD n)
    (hE : ∀ X Y, psdDistance (E X) (E Y) = psdDistance X Y)
    (hP : (E psdZero).val.PosDef) (X : PSD n) :
    ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
      (E (psdScale (t ^ 2) (sq_nonneg t) X)).val.PosDef := by
  letI : MetricSpace (PSD n) := psdMetricSpace n
  letI : PseudoMetricSpace (PSD n) := (psdMetricSpace n).toPseudoMetricSpace
  letI : PseudoEMetricSpace (PSD n) :=
    (psdMetricSpace n).toPseudoMetricSpace.toPseudoEMetricSpace
  letI : UniformSpace (PSD n) := (psdMetricSpace n).toPseudoMetricSpace.toUniformSpace
  have hi : Isometry E := by
    apply Isometry.of_dist_eq
    intro U V
    change psdDistance (E U) (E V) = psdDistance U V
    exact hE U V
  have ht := hi.continuous.tendsto psdZero |>.comp (tendsto_psdScale_sq_zero X)
  exact ht.eventually (psd_posDef_mem_nhds (E psdZero) hP)

/-- Choose the actual image when it is positive definite, and the interior
apex image otherwise. The fallback is used only away from the limit. -/
def scaledImagePD (E : PSD n → PSD n) (hP : (E psdZero).val.PosDef)
    (X : PSD n) (t : ℝ) : PositiveDefinite n := by
  by_cases h : (E (psdScale (t ^ 2) (sq_nonneg t) X)).val.PosDef
  · exact ⟨(E (psdScale (t ^ 2) (sq_nonneg t) X)).val, h⟩
  · exact ⟨(E psdZero).val, hP⟩

def scaledImageHermitian (E : PSD n → PSD n) (hP : (E psdZero).val.PosDef)
    (X : PSD n) (t : ℝ) : Hermitian n :=
  ⟨(scaledImagePD E hP X t).val,
    (scaledImagePD E hP X t).property.isHermitian⟩

theorem scaledImagePD_eventually_exact (E : PSD n → PSD n)
    (hE : ∀ X Y, psdDistance (E X) (E Y) = psdDistance X Y)
    (hP : (E psdZero).val.PosDef) (X : PSD n) :
    ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
      (scaledImagePD E hP X t).val =
        (E (psdScale (t ^ 2) (sq_nonneg t) X)).val := by
  filter_upwards [psd_isometry_scaled_eventually_posDef E hE hP X] with t ht
  simp [scaledImagePD, ht]

theorem tendsto_scaledImageHermitian (E : PSD n → PSD n)
    (hE : ∀ X Y, psdDistance (E X) (E Y) = psdDistance X Y)
    (hP : (E psdZero).val.PosDef) (X : PSD n) :
    Tendsto (scaledImageHermitian E hP X) (𝓝 (0 : ℝ))
      (𝓝 (psdHermitian (E psdZero))) := by
  letI : MetricSpace (PSD n) := psdMetricSpace n
  letI : PseudoMetricSpace (PSD n) := (psdMetricSpace n).toPseudoMetricSpace
  letI : PseudoEMetricSpace (PSD n) :=
    (psdMetricSpace n).toPseudoMetricSpace.toPseudoEMetricSpace
  letI : UniformSpace (PSD n) := (psdMetricSpace n).toPseudoMetricSpace.toUniformSpace
  have hi : Isometry E := by
    apply Isometry.of_dist_eq
    intro U V
    change psdDistance (E U) (E V) = psdDistance U V
    exact hE U V
  have ht : Tendsto (fun t : ℝ =>
      psdHermitian (E (psdScale (t ^ 2) (sq_nonneg t) X)))
      (𝓝 (0 : ℝ)) (𝓝 (psdHermitian (E psdZero))) :=
    (continuous_psdHermitian.tendsto (E psdZero)).comp
      ((hi.continuous.tendsto psdZero).comp (tendsto_psdScale_sq_zero X))
  have heq : (scaledImageHermitian E hP X) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => psdHermitian (E (psdScale (t ^ 2) (sq_nonneg t) X))) := by
    filter_upwards [scaledImagePD_eventually_exact E hE hP X] with t ht'
    apply Subtype.ext
    exact ht'
  exact ht.congr' heq.symm

theorem scaledImagePD_distance_pair_eventually (E : PSD n → PSD n)
    (hE : ∀ X Y, psdDistance (E X) (E Y) = psdDistance X Y)
    (hP : (E psdZero).val.PosDef) (X Y : PSD n) :
    ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
      distance (scaledImagePD E hP X t) (scaledImagePD E hP Y t) =
        |t| * psdDistance X Y := by
  filter_upwards [scaledImagePD_eventually_exact E hE hP X,
    scaledImagePD_eventually_exact E hE hP Y] with t hX hY
  let U := scaledImagePD E hP X t
  let V := scaledImagePD E hP Y t
  have heU : (⟨U.val, U.property.posSemidef⟩ : PSD n) =
      E (psdScale (t ^ 2) (sq_nonneg t) X) := Subtype.ext hX
  have heV : (⟨V.val, V.property.posSemidef⟩ : PSD n) =
      E (psdScale (t ^ 2) (sq_nonneg t) Y) := Subtype.ext hY
  change psdDistance (⟨U.val, U.property.posSemidef⟩ : PSD n)
      (⟨V.val, V.property.posSemidef⟩ : PSD n) = _
  rw [heU, heV, hE, psdDistance_scale_pair, Real.sqrt_sq_eq_abs]

theorem scaledImagePD_distance_apex_eventually (E : PSD n → PSD n)
    (hE : ∀ X Y, psdDistance (E X) (E Y) = psdDistance X Y)
    (hP : (E psdZero).val.PosDef) (X : PSD n) :
    ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
      distance ⟨(E psdZero).val, hP⟩ (scaledImagePD E hP X t) =
        |t| * psdDistance psdZero X := by
  filter_upwards [scaledImagePD_eventually_exact E hE hP X] with t hX
  let V := scaledImagePD E hP X t
  have heV : (⟨V.val, V.property.posSemidef⟩ : PSD n) =
      E (psdScale (t ^ 2) (sq_nonneg t) X) := Subtype.ext hX
  change psdDistance (E psdZero)
      (⟨V.val, V.property.posSemidef⟩ : PSD n) = _
  rw [heV, hE, psdDistance_comm, psdDistance_scale_zero,
    Real.sqrt_sq_eq_abs]
  rw [psdDistance_comm X psdZero]

theorem scaledImageHermitian_norm_bigO (E : PSD n → PSD n)
    (hE : ∀ X Y, psdDistance (E X) (E Y) = psdDistance X Y)
    (hP : (E psdZero).val.PosDef) (X : PSD n) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
        ‖scaledImageHermitian E hP X t - psdHermitian (E psdZero)‖ ≤
          C * |t| := by
  let P : PositiveDefinite n := ⟨(E psdZero).val, hP⟩
  obtain ⟨C₀, hC₀, hcoord⟩ := exists_local_coordinate_le_bures P
  have hnear := (tendsto_scaledImageHermitian E hE hP X).eventually hcoord
  let r := psdDistance psdZero X
  have hr : 0 ≤ r := psdDistance_nonneg _ _
  refine ⟨C₀ * (1 + r), mul_pos hC₀ (by linarith), ?_⟩
  filter_upwards [hnear, scaledImagePD_distance_apex_eventually E hE hP X]
    with t ht hdist
  have hval := ht (scaledImagePD E hP X t).property
  change ‖scaledImageHermitian E hP X t - psdHermitian (E psdZero)‖ ≤
    C₀ * distance P (scaledImagePD E hP X t) at hval
  rw [hdist] at hval
  calc
    ‖scaledImageHermitian E hP X t - psdHermitian (E psdZero)‖ ≤
        C₀ * (|t| * r) := hval
    _ ≤ (C₀ * (1 + r)) * |t| := by
      have ht0 : 0 ≤ |t| := abs_nonneg _
      nlinarith

#print axioms scaledImagePD_distance_pair_eventually
#print axioms scaledImagePD_distance_apex_eventually
#print axioms scaledImageHermitian_norm_bigO

#print axioms tendsto_scaledImageHermitian

#print axioms psd_isometry_scaled_eventually_posDef

end Bures

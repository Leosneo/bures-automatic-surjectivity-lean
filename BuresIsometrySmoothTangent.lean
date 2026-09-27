import BuresMidpointIteration
import BuresInteriorTangent
import BuresIsometrySmoothPrelude
import BuresNormalTangent
import BuresVerticalBracket
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Tangent-speed calculation for the exact normal-coordinate midpoint curves.
The joint optimal-lift derivative is used at the diagonal pair `(A,A)`. -/

noncomputable section
open Filter Matrix
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator Matrix.Norms.Frobenius
namespace Bures

set_option maxHeartbeats 1000000

private local instance (n : ℕ) : ContinuousSMul ℝ (Hermitian n) :=
  normalHermitianContinuousSMul n

def normalGramCurve (A B : PositiveDefinite n) (t : ℝ) : Hermitian n :=
  let S := matrixSqrt A.val
  let D := optimalLift A B - S
  ⟨gram (S + t • D), Matrix.isHermitian_mul_conjTranspose_self _⟩

theorem normalGramCurve_zero (A B : PositiveDefinite n) :
    normalGramCurve A B 0 = ⟨A.val, A.property.isHermitian⟩ := by
  apply Subtype.ext
  change gram (matrixSqrt A.val + (0 : ℝ) •
    (optimalLift A B - matrixSqrt A.val)) = A.val
  have he : matrixSqrt A.val + (0 : ℝ) •
      (optimalLift A B - matrixSqrt A.val) = matrixSqrt A.val := by
    ext i j
    simp [Matrix.smul_apply]
  rw [he]
  unfold gram
  rw [(Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg A.val)).isHermitian.eq]
  exact matrixSqrt_mul_self A.property.posSemidef

theorem normalGramCurve_dyadic (A B : PositiveDefinite n) (k : ℕ) :
    normalGramCurve A B ((1 / 2 : ℝ) ^ k) =
      ⟨(midpointIteration A B k).val,
        (midpointIteration A B k).property.isHermitian⟩ := by
  apply Subtype.ext
  exact (midpointIteration_gram A B k).symm

private theorem normalGramCurve_eq_projection (A B : PositiveDefinite n) (t : ℝ) :
    normalGramCurve A B t =
      (selfAdjointPartL ℝ (Mat n))
        (gram (matrixSqrt A.val + t •
          (optimalLift A B - matrixSqrt A.val))) := by
  exact (IsSelfAdjoint.selfAdjointPart_apply ℝ
    (show IsSelfAdjoint (gram (matrixSqrt A.val + t •
      (optimalLift A B - matrixSqrt A.val))) by
        exact (Matrix.isHermitian_mul_conjTranspose_self _))).symm

theorem differentiableAt_normalGramCurve (A B : PositiveDefinite n) (t : ℝ) :
    DifferentiableAt ℝ (normalGramCurve A B) t := by
  have hline : DifferentiableAt ℝ
      (fun s : ℝ => matrixSqrt A.val + s •
        (optimalLift A B - matrixSqrt A.val)) t := by
    fun_prop
  have hgram : DifferentiableAt ℝ gram
      (matrixSqrt A.val + t • (optimalLift A B - matrixSqrt A.val)) := by
    obtain ⟨L, hL, _⟩ := gram_hasFDerivAt
      (matrixSqrt A.val + t • (optimalLift A B - matrixSqrt A.val))
    exact hL.differentiableAt
  have hc := (selfAdjointPartL ℝ (Mat n)).differentiableAt.comp t
    (hgram.comp t hline)
  simpa only [Function.comp_def, ← normalGramCurve_eq_projection] using hc

def normalGramVelocity (A B : PositiveDefinite n) : Hermitian n :=
  let S := matrixSqrt A.val
  let D := optimalLift A B - S
  (selfAdjointPartL ℝ (Mat n))
    (D * S.conjTranspose + S * D.conjTranspose)

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_normalGramCurve_zero (A B : PositiveDefinite n) :
    HasDerivAt (normalGramCurve A B) (normalGramVelocity A B) 0 := by
  let S := matrixSqrt A.val
  let D := optimalLift A B - S
  have hline : HasDerivAt (fun t : ℝ => S + t • D) D 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const D).const_add S
  have hgram := (hline.hasFDerivAt.mul' hline.hasFDerivAt.star).hasDerivAt
  have hcomp := (selfAdjointPartL ℝ (Mat n)).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) hgram
  convert hcomp using 1
  · funext t
    exact normalGramCurve_eq_projection A B t
  · simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      one_smul]
    change (selfAdjointPartL ℝ (Mat n)) (D * S.conjTranspose + S * D.conjTranspose) =
      (selfAdjointPartL ℝ (Mat n)) ((S + 0 • D) * D.conjTranspose +
        D * (S + 0 • D).conjTranspose)
    have he : S + (0 : ℝ) • D = S := by
      ext i j
      simp
    rw [he, add_comm]

theorem normalGramVelocity_eq_sylvester (A B : PositiveDefinite n) :
    (normalGramVelocity A B).val =
      (normalCoordinate A B).val * A.val +
        A.val * (normalCoordinate A B).val := by
  let S := matrixSqrt A.val
  let K := (normalCoordinate A B).val
  have hD : optimalLift A B - S = K * S := by
    change optimalLift A B - S = (normalTransport A B - 1) * S
    rw [sub_mul, one_mul, normalTransport_mul_sqrt]
  have hK : K.IsHermitian := (normalCoordinate A B).property
  have hA : gram S = A.val := by
    unfold gram S
    rw [(Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg A.val)).isHermitian.eq]
    exact matrixSqrt_mul_self A.property.posSemidef
  change ((selfAdjointPartL ℝ (Mat n))
    ((optimalLift A B - S) * S.conjTranspose +
      S * (optimalLift A B - S).conjTranspose)).val = _
  rw [hD]
  have hherm := gram_linear_isHermitian S (K * S)
  have hp : ((selfAdjointPartL ℝ (Mat n))
      ((K * S) * S.conjTranspose + S * (K * S).conjTranspose)).val =
      (K * S) * S.conjTranspose + S * (K * S).conjTranspose := by
    exact congrArg Subtype.val (IsSelfAdjoint.selfAdjointPart_apply ℝ hherm)
  rw [hp]
  rw [gram_horizontal_linear S K hK, hA]

private theorem dyadic_tendsto_nhdsGT_zero :
    Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  · exact Filter.Eventually.of_forall (fun k => by
      change (0 : ℝ) < (1 / 2 : ℝ) ^ k
      positivity)

private theorem hasDerivAt_dyadic_slope {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (v : E)
    (hf : HasDerivAt f v 0) :
    Tendsto (fun k : ℕ => ((1 / 2 : ℝ) ^ k)⁻¹ •
      (f ((1 / 2 : ℝ) ^ k) - f 0)) atTop (𝓝 v) := by
  have h := hf.tendsto_slope_zero_right.comp dyadic_tendsto_nhdsGT_zero
  simpa only [zero_add] using h

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_normalOptimalDifference (A B C : PositiveDefinite n) :
    HasDerivAt
      (fun t : ℝ => optimalDifferencePair
        (normalGramCurve A B t, normalGramCurve A C t))
      (optimalDifferenceTangent A
        (normalGramVelocity A B - normalGramVelocity A C)) 0 := by
  have hpair := HasDerivAt.prodMk
    (hasDerivAt_normalGramCurve_zero A B)
    (hasDerivAt_normalGramCurve_zero A C)
  have hbase :
      (normalGramCurve A B 0, normalGramCurve A C 0) =
        (⟨A.val, A.property.isHermitian⟩,
         ⟨A.val, A.property.isHermitian⟩) := by
    rw [normalGramCurve_zero, normalGramCurve_zero]
  have hdiff : HasFDerivAt (optimalDifferencePair (n := n))
      (fderiv ℝ (optimalDifferencePair (n := n))
        (⟨A.val, A.property.isHermitian⟩,
         ⟨A.val, A.property.isHermitian⟩))
      (normalGramCurve A B 0, normalGramCurve A C 0) := by
    rw [hbase]
    exact (differentiableAt_optimalDifferencePair A A).hasFDerivAt
  have hcomp := hdiff.comp_hasDerivAt (0 : ℝ) hpair
  simpa only [Function.comp_def,
    optimalDifferencePair_fderiv_eq_tangent A] using hcomp

theorem midpointIteration_tangent_speed (A B C : PositiveDefinite n) :
    Tendsto (fun k : ℕ => ((1 / 2 : ℝ) ^ k)⁻¹ *
      distance (midpointIteration A B k) (midpointIteration A C k))
      atTop (𝓝 (frobeniusMagnitude
        (optimalDifferenceTangent A
          (normalGramVelocity A B - normalGramVelocity A C)))) := by
  let g : ℝ → Mat n := fun t => optimalDifferencePair
    (normalGramCurve A B t, normalGramCurve A C t)
  have hg : HasDerivAt g
      (optimalDifferenceTangent A
        (normalGramVelocity A B - normalGramVelocity A C)) 0 :=
    hasDerivAt_normalOptimalDifference A B C
  have hmat := hasDerivAt_dyadic_slope g _ hg
  have hnorm := continuous_norm.continuousAt.tendsto.comp hmat
  have hzero : g 0 = 0 := by
    simp only [g, normalGramCurve_zero]
    exact optimalDifferencePair_diagonal_zero A
  have heq : ∀ k : ℕ,
      ‖((1 / 2 : ℝ) ^ k)⁻¹ • (g ((1 / 2 : ℝ) ^ k) - g 0)‖ =
        ((1 / 2 : ℝ) ^ k)⁻¹ *
          distance (midpointIteration A B k) (midpointIteration A C k) := by
    intro k
    rw [hzero, sub_zero]
    have hmap : (opToFrobeniusCLM n)
        (((1 / 2 : ℝ) ^ k)⁻¹ • g ((1 / 2 : ℝ) ^ k)) =
          ((1 / 2 : ℝ) ^ k)⁻¹ •
            (opToFrobeniusCLM n) (g ((1 / 2 : ℝ) ^ k)) := by
      ext i j
      rfl
    change ‖(opToFrobeniusCLM n)
      (((1 / 2 : ℝ) ^ k)⁻¹ • g ((1 / 2 : ℝ) ^ k))‖ = _
    rw [hmap]
    have hre : (((1 / 2 : ℝ) ^ k)⁻¹ •
        (opToFrobeniusCLM n) (g ((1 / 2 : ℝ) ^ k))) =
        (((((1 / 2 : ℝ) ^ k)⁻¹ : ℝ) : ℂ) •
          (opToFrobeniusCLM n) (g ((1 / 2 : ℝ) ^ k))) := by
      ext i j
      rfl
    rw [hre, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_inv, abs_of_pos (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ k)]
    change ((1 / 2 : ℝ) ^ k)⁻¹ * ‖optimalDifferencePair
      (normalGramCurve A B ((1 / 2 : ℝ) ^ k),
       normalGramCurve A C ((1 / 2 : ℝ) ^ k))‖ = _
    rw [normalGramCurve_dyadic, normalGramCurve_dyadic,
      ← distance_eq_norm_optimalDifferencePair]
  have hform : (fun k : ℕ =>
      ‖((1 / 2 : ℝ) ^ k)⁻¹ • (g ((1 / 2 : ℝ) ^ k) - g 0)‖) =
      (fun k : ℕ => ((1 / 2 : ℝ) ^ k)⁻¹ *
        distance (midpointIteration A B k) (midpointIteration A C k)) :=
    funext heq
  have h := hnorm
  change Tendsto (fun k : ℕ => ‖((1 / 2 : ℝ) ^ k)⁻¹ •
      (g ((1 / 2 : ℝ) ^ k) - g 0)‖) atTop
    (𝓝 ‖optimalDifferenceTangent A
      (normalGramVelocity A B - normalGramVelocity A C)‖) at h
  rw [hform] at h
  simpa only [frobeniusMagnitude_eq_norm] using h

theorem isometry_preserves_normal_tangent_distance
    (F : PositiveDefinite n → PositiveDefinite n) (hF : PreservesDistance F)
    (A B C : PositiveDefinite n) :
    frobeniusMagnitude (optimalDifferenceTangent A
      (normalGramVelocity A B - normalGramVelocity A C)) =
    frobeniusMagnitude (optimalDifferenceTangent (F A)
      (normalGramVelocity (F A) (F B) -
       normalGramVelocity (F A) (F C))) := by
  have hsource := midpointIteration_tangent_speed A B C
  have htarget := midpointIteration_tangent_speed (F A) (F B) (F C)
  have heq : (fun k : ℕ => ((1 / 2 : ℝ) ^ k)⁻¹ *
      distance (midpointIteration A B k) (midpointIteration A C k)) =
    (fun k : ℕ => ((1 / 2 : ℝ) ^ k)⁻¹ *
      distance (midpointIteration (F A) (F B) k)
        (midpointIteration (F A) (F C) k)) := by
    funext k
    rw [← map_midpointIteration F hF A B k,
      ← map_midpointIteration F hF A C k, hF]
  rw [heq] at hsource
  exact tendsto_nhds_unique hsource htarget

set_option backward.isDefEq.respectTransparency false in
theorem optimalDifferenceTangent_normalGramVelocity
    (A B : PositiveDefinite n) :
    optimalDifferenceTangent A (normalGramVelocity A B) =
      optimalLift A B - matrixSqrt A.val := by
  let f : ℝ → Mat n := fun t =>
    optimalLiftHermitian A (normalGramCurve A B t)
  have hbase : normalGramCurve A B 0 =
      ⟨A.val, A.property.isHermitian⟩ := normalGramCurve_zero A B
  have hdiff : HasFDerivAt (optimalLiftHermitian A)
      (fderiv ℝ (optimalLiftHermitian A)
        (⟨A.val, A.property.isHermitian⟩ : Hermitian n))
      (normalGramCurve A B 0) := by
    rw [hbase]
    exact (differentiableAt_optimalLiftHermitian A A).hasFDerivAt
  have hf : HasDerivAt f
      (optimalDifferenceTangent A (normalGramVelocity A B)) 0 := by
    have hc := hdiff.comp_hasDerivAt (0 : ℝ)
      (hasDerivAt_normalGramCurve_zero A B)
    simpa only [f, Function.comp_def,
      optimalDifferenceTangent_eq_fixed_fderiv A] using hc
  have hlim := hasDerivAt_dyadic_slope f _ hf
  have hzero : f 0 = matrixSqrt A.val := by
    change optimalLiftHermitian A (normalGramCurve A B 0) = _
    rw [hbase, optimalLiftHermitian_eq, optimalLift_self]
  have hvalue (k : ℕ) : f ((1 / 2 : ℝ) ^ k) =
      matrixSqrt A.val + ((1 / 2 : ℝ) ^ k) •
        (optimalLift A B - matrixSqrt A.val) := by
    change optimalLiftHermitian A (normalGramCurve A B ((1 / 2 : ℝ) ^ k)) = _
    rw [normalGramCurve_dyadic, optimalLiftHermitian_eq]
    exact optimalLift_midpointIteration A B k
  have heq : ∀ k : ℕ,
      ((1 / 2 : ℝ) ^ k)⁻¹ •
        (f ((1 / 2 : ℝ) ^ k) - f 0) =
          optimalLift A B - matrixSqrt A.val := by
    intro k
    rw [hvalue, hzero, add_sub_cancel_left]
    rw [smul_smul]
    simp only [inv_mul_cancel₀ (by positivity : (1 / 2 : ℝ) ^ k ≠ 0), one_smul]
  have hconst : Tendsto (fun k : ℕ => ((1 / 2 : ℝ) ^ k)⁻¹ •
      (f ((1 / 2 : ℝ) ^ k) - f 0)) atTop
      (𝓝 (optimalLift A B - matrixSqrt A.val)) := by
    simpa only [heq] using tendsto_const_nhds
  exact tendsto_nhds_unique hlim hconst

theorem optimalDifferenceTangent_normalGramVelocity_eq_horizontal
    (A B : PositiveDefinite n) :
    optimalDifferenceTangent A (normalGramVelocity A B) =
      (normalCoordinate A B).val * matrixSqrt A.val := by
  rw [optimalDifferenceTangent_normalGramVelocity]
  change optimalLift A B - matrixSqrt A.val =
    (normalTransport A B - 1) * matrixSqrt A.val
  rw [sub_mul, one_mul, normalTransport_mul_sqrt]

theorem isometry_preserves_normal_coordinate_distance
    (F : PositiveDefinite n → PositiveDefinite n) (hF : PreservesDistance F)
    (A B C : PositiveDefinite n) :
    frobeniusMagnitude
      (((normalCoordinate A B).val - (normalCoordinate A C).val) *
        matrixSqrt A.val) =
    frobeniusMagnitude
      (((normalCoordinate (F A) (F B)).val -
        (normalCoordinate (F A) (F C)).val) *
        matrixSqrt (F A).val) := by
  have h := isometry_preserves_normal_tangent_distance F hF A B C
  rw [map_sub, map_sub,
    optimalDifferenceTangent_normalGramVelocity_eq_horizontal,
    optimalDifferenceTangent_normalGramVelocity_eq_horizontal,
    optimalDifferenceTangent_normalGramVelocity_eq_horizontal,
    optimalDifferenceTangent_normalGramVelocity_eq_horizontal,
    ← sub_mul, ← sub_mul] at h
  exact h

theorem normalTangentEquiv_coordinate_distance
    (A B C : PositiveDefinite n) :
    ‖normalTangentEquiv A (normalCoordinate A B) -
      normalTangentEquiv A (normalCoordinate A C)‖ =
    frobeniusMagnitude
      (((normalCoordinate A B).val - (normalCoordinate A C).val) *
        matrixSqrt A.val) := by
  rw [← map_sub, normalTangentEquiv_norm]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem normalConjugate_local_norm_isometry
    (F : PositiveDefinite n → PositiveDefinite n) (hF : PreservesDistance F)
    (A : PositiveDefinite n) :
    ∃ r : ℝ, 0 < r ∧
      ∀ x : NormalTangentSpace A, ‖x‖ < r →
      ∀ y : NormalTangentSpace A, ‖y‖ < r →
        ‖normalConjugate F A x - normalConjugate F A y‖ = ‖x - y‖ := by
  obtain ⟨r, hr, hpos⟩ := normalTangent_ball_positive A
  refine ⟨r, hr, ?_⟩
  intro x hx y hy
  let Kx := (normalTangentEquiv A).symm x
  let Ky := (normalTangentEquiv A).symm y
  have hpx : (normalTransportShift Kx).val.PosDef := by
    apply hpos Kx
    simpa [Kx] using hx
  have hpy : (normalTransportShift Ky).val.PosDef := by
    apply hpos Ky
    simpa [Ky] using hy
  let B := normalChartPoint A (normalTransportShift Kx) hpx
  let C := normalChartPoint A (normalTransportShift Ky) hpy
  have hBx : normalCoordinate A B = Kx := normalCoordinate_chartPoint A Kx hpx
  have hCy : normalCoordinate A C = Ky := normalCoordinate_chartPoint A Ky hpy
  have hx' : x = normalTangentEquiv A (normalCoordinate A B) := by
    rw [hBx]
    exact ((normalTangentEquiv A).apply_symm_apply x).symm
  have hy' : y = normalTangentEquiv A (normalCoordinate A C) := by
    rw [hCy]
    exact ((normalTangentEquiv A).apply_symm_apply y).symm
  rw [hx', hy', normalConjugate_at_point, normalConjugate_at_point,
    normalTangentEquiv_coordinate_distance,
    normalTangentEquiv_coordinate_distance]
  exact (isometry_preserves_normal_coordinate_distance F hF A B C).symm

#print axioms normalGramCurve_dyadic
#print axioms midpointIteration_tangent_speed
#print axioms optimalDifferenceTangent_normalGramVelocity
#print axioms normalConjugate_local_norm_isometry
end Bures

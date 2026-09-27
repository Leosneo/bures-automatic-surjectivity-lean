import BuresOptimalLiftJointSmooth
import BuresNormComparison

/-! Quantitative Euclidean tangent behavior of the literal Bures distance
near a positive definite matrix. -/

noncomputable section
open Filter
open Asymptotics
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace Bures

local instance (n : ℕ) : FiniteDimensional ℝ (Hermitian n) :=
  FiniteDimensional.of_injective (hermitianInclusion n).toLinearMap (by
    intro X Y h
    exact Subtype.ext h)

/-- The matrix-valued first-order remainder is little-o in Frobenius
magnitude as well as operator norm. -/
theorem optimalDifferencePair_frobenius_remainder_littleO
    (A : PositiveDefinite n) :
    (fun p : Hermitian n × Hermitian n =>
      frobeniusMagnitude
        (optimalDifferencePair p - optimalDifferenceTangent A (p.1 - p.2)))
      =o[𝓝 (⟨A.val, A.property.isHermitian⟩,
              ⟨A.val, A.property.isHermitian⟩)]
        (fun p : Hermitian n × Hermitian n =>
          p - (⟨A.val, A.property.isHermitian⟩,
               ⟨A.val, A.property.isHermitian⟩)) := by
  let r : Hermitian n × Hermitian n → Mat n := fun p =>
    optimalDifferencePair p - optimalDifferenceTangent A (p.1 - p.2)
  obtain ⟨C, hC, hbound⟩ := exists_frobenius_le_operator n
  have hr := optimalDifferencePair_tangent_littleO A
  apply IsLittleO.of_bound
  intro ε hε
  have hsmall := hr.bound (div_pos hε hC)
  filter_upwards [hsmall] with p hp
  have hnonneg : 0 ≤ frobeniusMagnitude (r p) := by
    unfold frobeniusMagnitude
    exact norm_nonneg _
  have hnorm : ‖frobeniusMagnitude (r p)‖ = frobeniusMagnitude (r p) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  rw [hnorm]
  calc
    frobeniusMagnitude (r p) ≤ C * operatorMagnitude (r p) := hbound _
    _ ≤ C * ((ε / C) * ‖p -
        (⟨A.val, A.property.isHermitian⟩,
         ⟨A.val, A.property.isHermitian⟩)‖) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      simpa only [operatorMagnitude_eq_norm] using hp
    _ = ε * ‖p -
        (⟨A.val, A.property.isHermitian⟩,
         ⟨A.val, A.property.isHermitian⟩)‖ := by
      field_simp [ne_of_gt hC]

theorem abs_frobeniusMagnitude_sub_le (M N : Mat n) :
    |frobeniusMagnitude M - frobeniusMagnitude N| ≤
      frobeniusMagnitude (M - N) := by
  change |‖opToFrobeniusCLM n M‖ - ‖opToFrobeniusCLM n N‖| ≤
    ‖opToFrobeniusCLM n (M - N)‖
  rw [map_sub]
  exact abs_norm_sub_norm_le _ _

/-- The Bures distance model is approximated uniformly, to first order,
by the Frobenius norm of a fixed real-linear map applied to `X−Y`. -/
theorem frobeniusDistance_tangent_littleO (A : PositiveDefinite n) :
    (fun p : Hermitian n × Hermitian n =>
      frobeniusMagnitude (optimalDifferencePair p) -
        frobeniusMagnitude (optimalDifferenceTangent A (p.1 - p.2)))
      =o[𝓝 (⟨A.val, A.property.isHermitian⟩,
              ⟨A.val, A.property.isHermitian⟩)]
        (fun p : Hermitian n × Hermitian n =>
          p - (⟨A.val, A.property.isHermitian⟩,
               ⟨A.val, A.property.isHermitian⟩)) := by
  have hr := optimalDifferencePair_frobenius_remainder_littleO A
  apply IsLittleO.of_bound
  intro ε hε
  have hb := hr.bound hε
  filter_upwards [hb] with p hp
  have h := abs_frobeniusMagnitude_sub_le
    (optimalDifferencePair p) (optimalDifferenceTangent A (p.1 - p.2))
  rw [Real.norm_eq_abs]
  exact h.trans (by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (show
      0 ≤ frobeniusMagnitude
        (optimalDifferencePair p - optimalDifferenceTangent A (p.1 - p.2)) from
      norm_nonneg _)] using hp)

/-- Nondegeneracy of the tangent norm: the Frobenius size of the Bures
lift derivative controls the Hermitian coordinate displacement. -/
theorem exists_norm_le_optimalDifferenceTangent (A : PositiveDefinite n) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : Hermitian n,
      ‖H‖ ≤ C * frobeniusMagnitude (optimalDifferenceTangent A H) := by
  let L := optimalDifferenceTangent A
  obtain ⟨K, hK, hanti⟩ :=
    (L.toLinearMap.injective_iff_antilipschitz).mp
      (optimalDifferenceTangent_injective A)
  obtain ⟨C, hC, hbound⟩ := exists_operator_le_frobenius n
  refine ⟨(K : ℝ) * C, mul_pos (by exact_mod_cast hK) hC, ?_⟩
  intro H
  have hfirst : ‖H‖ ≤ (K : ℝ) * operatorMagnitude (L H) := by
    simpa only [operatorMagnitude_eq_norm] using
      (ZeroHomClass.bound_of_antilipschitz L.toLinearMap hanti H)
  calc
    ‖H‖ ≤ (K : ℝ) * operatorMagnitude (L H) := hfirst
    _ ≤ (K : ℝ) * (C * frobeniusMagnitude (L H)) :=
      mul_le_mul_of_nonneg_left (hbound _) (by exact_mod_cast hK.le)
    _ = ((K : ℝ) * C) * frobeniusMagnitude (L H) := by ring

/-- The nondegenerate tangent norm makes ordinary Hermitian displacement
locally bounded by literal Bures distance from a positive definite base. -/
theorem exists_local_coordinate_le_bures (A : PositiveDefinite n) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ X : Hermitian n in 𝓝 (⟨A.val, A.property.isHermitian⟩ : Hermitian n),
        ∀ hX : X.val.PosDef,
          ‖X - (⟨A.val, A.property.isHermitian⟩ : Hermitian n)‖ ≤
            C * distance A ⟨X.val, hX⟩ := by
  let a : Hermitian n := ⟨A.val, A.property.isHermitian⟩
  obtain ⟨C₀, hC₀, hbound⟩ := exists_norm_le_optimalDifferenceTangent A
  let ε := 1 / (2 * C₀)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hCε : C₀ * ε = 1 / 2 := by
    dsimp [ε]
    field_simp [ne_of_gt hC₀]
  have hrem := frobeniusDistance_tangent_littleO A
  have hnear := hrem.bound hε
  have hmap : Tendsto (fun X : Hermitian n => (a, X)) (𝓝 a) (𝓝 (a, a)) :=
    tendsto_const_nhds.prodMk_nhds tendsto_id
  have hnear' := hmap.eventually hnear
  refine ⟨2 * C₀, by positivity, ?_⟩
  filter_upwards [hnear'] with X hXnear hX
  let B : PositiveDefinite n := ⟨X.val, hX⟩
  have hnormpair : ‖(a, X) - (a, a)‖ = ‖X - a‖ := by
    simp
  have hsame : frobeniusMagnitude (optimalDifferencePair (a, X)) =
      distance A B := by
    have h := distance_eq_norm_optimalDifferencePair A B
    rw [← frobeniusMagnitude_eq_norm] at h
    exact h.symm
  have hdelta :
      |frobeniusMagnitude (optimalDifferencePair (a, X)) -
        frobeniusMagnitude (optimalDifferenceTangent A (a - X))| ≤
          ε * ‖X - a‖ := by
    change ‖frobeniusMagnitude (optimalDifferencePair (a, X)) -
      frobeniusMagnitude (optimalDifferenceTangent A (a - X))‖ ≤
        ε * ‖(a, X) - (a, a)‖ at hXnear
    simpa only [Real.norm_eq_abs, hnormpair] using hXnear
  have hlinear : ‖X - a‖ ≤ C₀ *
      frobeniusMagnitude (optimalDifferenceTangent A (a - X)) := by
    simpa only [norm_sub_rev] using hbound (a - X)
  have hupper : frobeniusMagnitude (optimalDifferenceTangent A (a - X)) ≤
      distance A B + ε * ‖X - a‖ := by
    rw [hsame] at hdelta
    linarith [(abs_le.mp hdelta).1]
  have hmul := mul_le_mul_of_nonneg_left hupper hC₀.le
  have hmulε : C₀ * (ε * ‖X - a‖) = (1 / 2) * ‖X - a‖ := by
    rw [← mul_assoc, hCε]
  rw [mul_add, hmulε] at hmul
  change ‖X - a‖ ≤ (2 * C₀) * distance A B
  linarith

#print axioms optimalDifferencePair_frobenius_remainder_littleO
#print axioms frobeniusDistance_tangent_littleO
#print axioms exists_norm_le_optimalDifferenceTangent
#print axioms exists_local_coordinate_le_bures

end Bures

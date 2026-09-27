import BuresUniqueGeodesic
import BuresOptimalLift
import BuresAnchorDerivative

/-! Canonical normal coordinates and their exact midpoint law. -/
noncomputable section
open scoped MatrixOrder ComplexOrder Matrix.Norms.Frobenius
open Matrix
namespace Bures

/-- The optimal factor with first factor fixed to the positive square root
is unique for positive definite endpoints. -/
theorem optimalLift_eq_of_realizes_distance (A B : PositiveDefinite n)
    (T : Mat n) (hT : gram T = B.val)
    (hd : distance A B = ‖matrixSqrt A.val - T‖) :
    optimalLift A B = T := by
  have hTu : IsUnit T := isUnit_of_mul_isUnit_left (hT ▸ B.property.isUnit)
  have hOu : IsUnit (optimalLift A B) :=
    isUnit_of_mul_isUnit_left ((optimalLift_gram A B) ▸ B.property.isUnit)
  obtain ⟨U, hUl, hUr, heT⟩ := invertible_factor_polar T hTu
  obtain ⟨V, hVl, hVr, heO⟩ := invertible_factor_polar (optimalLift A B) hOu
  change T = matrixSqrt (gram T) * U at heT
  change optimalLift A B = matrixSqrt (gram (optimalLift A B)) * V at heO
  rw [hT] at heT
  rw [optimalLift_gram] at heO
  have hUV : U = V := unique_distance_alignment A B hUl hUr hVl hVr
    (heT ▸ hd) (heO ▸ distance_eq_optimalLift_norm A B)
  rw [heO, ← hUV, ← heT]

/-- In canonical lift coordinates, the metric midpoint based at `A` is
exactly the arithmetic midpoint. This conclusion uses only the literal
Bures distance and holds before any smoothness claim about an isometry. -/
theorem optimalLift_metric_midpoint (A M B : PositiveDefinite n)
    (hM : IsMetricMidpoint A M B) :
    optimalLift A M = (1 / 2 : ℝ) •
      (matrixSqrt A.val + optimalLift A B) := by
  obtain ⟨U, hUl, hUr, hd, hMg⟩ := metric_midpoint_lift A M B hM
  have hGram : gram (matrixSqrt B.val * U) = B.val := by
    simp only [gram, Matrix.conjTranspose_mul,
      (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg B.val)).isHermitian.eq]
    calc
      _ = matrixSqrt B.val * (U * Uᴴ) * matrixSqrt B.val := by noncomm_ring
      _ = B.val := by rw [hUr, mul_one, matrixSqrt_mul_self B.property.posSemidef]
  have hOpt := optimalLift_eq_of_realizes_distance A B _ hGram hd
  rw [← hOpt] at hMg
  apply optimalLift_eq_of_positive_overlap A M _ hMg.symm
  have he : matrixSqrt A.val * ((1 / 2 : ℝ) •
      (matrixSqrt A.val + optimalLift A B)) =
      (1 / 2 : ℝ) • (A.val +
        matrixSqrt (matrixSqrt A.val * B.val * matrixSqrt A.val)) := by
    rw [mul_smul_comm, mul_add, matrixSqrt_mul_self A.property.posSemidef,
      optimalLift_overlap]
  rw [he]
  have hsm (X : Mat n) : (1 / 2 : ℝ) • X = (1 / 2 : ℂ) • X := by
    ext i j
    simp [Matrix.smul_apply, Complex.real_smul]
  rw [hsm]
  exact (A.property.posSemidef.add
    (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg _))).smul (by
      norm_num [Complex.le_def, Complex.div_re, Complex.div_im])

/-- Positive transport from `A` to `B`; its deviation from identity is the
normal coordinate used in the midpoint argument. -/
def normalTransport (A B : PositiveDefinite n) : Mat n :=
  optimalLift A B * (matrixSqrt A.val)⁻¹

theorem normalTransport_posDef (A B : PositiveDefinite n) :
    (normalTransport A B).PosDef := by
  let S := matrixSqrt A.val
  let R := matrixSqrt (S * B.val * S)
  have hS : S.IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg _)).isHermitian
  have hSu : IsUnit S := matrixSqrt_isUnit A
  have hRu : IsUnit R := by
    apply isUnit_of_mul_isUnit_left (y := R)
    rw [show R * R = S * B.val * S from
      matrixSqrt_mul_self (sandwich_posSemidef A B)]
    exact (hSu.mul B.property.isUnit).mul hSu
  have hR : R.PosDef :=
    (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg _)).posDef_iff_isUnit.mpr hRu
  have hSi : IsUnit S⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hSu
  have hp := hR.mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit hSi)
  rw [hS.inv.eq] at hp
  exact hp

theorem normalTransport_mul_sqrt (A B : PositiveDefinite n) :
    normalTransport A B * matrixSqrt A.val = optimalLift A B := by
  rw [normalTransport, mul_assoc, Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).mp (matrixSqrt_isUnit A)), mul_one]

theorem normalTransport_congruence (A B : PositiveDefinite n) :
    normalTransport A B * A.val * normalTransport A B = B.val := by
  have hT := (normalTransport_posDef A B).isHermitian
  have hS := (Matrix.nonneg_iff_posSemidef.mp
    (matrixSqrt_nonneg A.val)).isHermitian
  have hg := optimalLift_gram A B
  rw [← normalTransport_mul_sqrt A B] at hg
  simp only [gram, Matrix.conjTranspose_mul, hT.eq, hS.eq] at hg
  calc
    _ = normalTransport A B *
      (matrixSqrt A.val * matrixSqrt A.val) * normalTransport A B := by
        rw [matrixSqrt_mul_self A.property.posSemidef]
    _ = B.val := by simpa only [mul_assoc] using hg

theorem normalTransport_self (A : PositiveDefinite n) :
    normalTransport A A = 1 := by
  rw [normalTransport, optimalLift_self, Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp (matrixSqrt_isUnit A))]

theorem normalTransport_metric_midpoint (A M B : PositiveDefinite n)
    (hM : IsMetricMidpoint A M B) :
    normalTransport A M = (1 / 2 : ℝ) • (1 + normalTransport A B) := by
  rw [normalTransport, optimalLift_metric_midpoint A M B hM,
    smul_mul_assoc, add_mul, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp (matrixSqrt_isUnit A))]
  rfl

/-- Centered real Hermitian normal coordinates. -/
def normalCoordinate (A B : PositiveDefinite n) : Hermitian n :=
  ⟨normalTransport A B - 1,
    (normalTransport_posDef A B).isHermitian.sub Matrix.isHermitian_one⟩

theorem normalCoordinate_self (A : PositiveDefinite n) : normalCoordinate A A = 0 := by
  apply Subtype.ext
  simp [normalCoordinate, normalTransport_self]

theorem normalCoordinate_midpoint (A M B : PositiveDefinite n)
    (hM : IsMetricMidpoint A M B) :
    normalCoordinate A M = (1 / 2 : ℝ) • normalCoordinate A B := by
  apply Subtype.ext
  change normalTransport A M - 1 = (1 / 2 : ℝ) • (normalTransport A B - 1)
  rw [normalTransport_metric_midpoint A M B hM]
  module

/-- Congruence is the inverse normal chart on the positive transport cone. -/
def normalChartPoint (A : PositiveDefinite n) (T : Hermitian n)
    (hT : T.val.PosDef) : PositiveDefinite n :=
  ⟨(congruenceAnchor ⟨A.val, A.property.isHermitian⟩ T).val,
    congruenceAnchor_posDef _ T A.property hT⟩

theorem normalTransport_chartPoint (A : PositiveDefinite n) (T : Hermitian n)
    (hT : T.val.PosDef) : normalTransport A (normalChartPoint A T hT) = T.val := by
  exact transport_eq_of_congruence
    (congruenceAnchor ⟨A.val, A.property.isHermitian⟩ T)
    ⟨A.val, A.property.isHermitian⟩ T A.property hT rfl

theorem normalChartPoint_transport (A B : PositiveDefinite n) :
    normalChartPoint A
      ⟨normalTransport A B, (normalTransport_posDef A B).isHermitian⟩
      (normalTransport_posDef A B) = B :=
  Subtype.ext (normalTransport_congruence A B)

theorem normalTransport_injective (A : PositiveDefinite n) :
    Function.Injective (normalTransport A) := by
  intro B D h
  apply Subtype.ext
  rw [← normalTransport_congruence A B, h, normalTransport_congruence A D]

theorem normalCoordinate_injective (A : PositiveDefinite n) :
    Function.Injective (normalCoordinate A) := by
  intro B D h
  apply normalTransport_injective A
  have hm := congrArg Subtype.val h
  exact sub_left_injective hm

def transportHalf (T : Hermitian n) : Hermitian n :=
  (1 / 2 : ℝ) • ((⟨1, Matrix.isHermitian_one⟩ : Hermitian n) + T)

theorem transportHalf_posDef (T : Hermitian n) (hT : T.val.PosDef) :
    (transportHalf T).val.PosDef := by
  exact ((Matrix.PosDef.one : (1 : Mat n).PosDef).add hT).smul (by norm_num : (0 : ℝ) < 1 / 2)

/-- The explicit half-normal-coordinate point is the unique metric midpoint. -/
theorem normalChartPoint_midpoint (A : PositiveDefinite n) (T : Hermitian n)
    (hT : T.val.PosDef) :
    IsMetricMidpoint A
      (normalChartPoint A (transportHalf T) (transportHalf_posDef T hT))
      (normalChartPoint A T hT) := by
  obtain ⟨M, hM⟩ := metric_midpoint_exists A (normalChartPoint A T hT)
  have he : M = normalChartPoint A (transportHalf T) (transportHalf_posDef T hT) := by
    apply normalTransport_injective A
    rw [normalTransport_metric_midpoint A M _ hM,
      normalTransport_chartPoint, normalTransport_chartPoint]
    rfl
  exact he ▸ hM

#print axioms normalCoordinate_midpoint
#print axioms normalChartPoint_midpoint
#print axioms normalChartPoint_transport
#print axioms normalTransport_chartPoint
#print axioms optimalLift_eq_of_realizes_distance
#print axioms optimalLift_metric_midpoint
end Bures

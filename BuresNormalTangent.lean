import BuresNormalChart
import BuresNormComparison
import HermitianFiniteDimension

/-! Hilbert-space models for Hermitian Bures normal coordinates. -/
noncomputable section
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open scoped Topology
namespace Bures

abbrev normalHermitianContinuousSMul (n : ℕ) : ContinuousSMul ℝ (Hermitian n) where
  continuous_smul := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun p : ℝ × Hermitian n => (p.1 : ℂ) * p.2.val i j)
    exact (Complex.continuous_ofReal.comp continuous_fst).mul
      ((continuous_apply j).comp ((continuous_apply i).comp
        (continuous_subtype_val.comp continuous_snd)))

/-- The horizontal lift embeds transport directions in a genuine real
Hilbert space carrying the Frobenius norm. -/
def normalTangentEmbedding (A : PositiveDefinite n) :
    Hermitian n →ₗ[ℝ] FrobeniusModel n where
  toFun K := opToFrobeniusLinear n (K.val * matrixSqrt A.val)
  map_add' := by
    intro K L
    ext i j
    change ((K.val + L.val) * matrixSqrt A.val) i j =
      (K.val * matrixSqrt A.val + L.val * matrixSqrt A.val) i j
    rw [add_mul]
  map_smul' := by
    intro r K
    ext i j
    change ((r • K.val) * matrixSqrt A.val) i j =
      (r • (K.val * matrixSqrt A.val)) i j
    rw [smul_mul_assoc]

theorem normalTangentEmbedding_injective (A : PositiveDefinite n) :
    Function.Injective (normalTangentEmbedding A) := by
  intro K L h
  have hm : K.val * matrixSqrt A.val = L.val * matrixSqrt A.val := by
    ext i j
    exact congrArg (fun x : FrobeniusModel n => x i j) h
  exact Subtype.ext ((matrixSqrt_isUnit A).mul_right_cancel hm)

abbrev NormalTangentSpace (A : PositiveDefinite n) :=
  LinearMap.range (normalTangentEmbedding A)

/-- No metric is installed on the original Hermitian type: the different
base-point norms live on these separate horizontal subspaces. -/
def normalTangentEquiv (A : PositiveDefinite n) :
    Hermitian n ≃ₗ[ℝ] NormalTangentSpace A :=
  LinearEquiv.ofInjective (normalTangentEmbedding A) (normalTangentEmbedding_injective A)

theorem normalTangentEquiv_norm (A : PositiveDefinite n) (K : Hermitian n) :
    ‖normalTangentEquiv A K‖ = frobeniusMagnitude (K.val * matrixSqrt A.val) := rfl

set_option backward.isDefEq.respectTransparency false in
def normalTangentContinuousEquiv (A : PositiveDefinite n) :
    Hermitian n ≃L[ℝ] NormalTangentSpace A := by
  letI : ContinuousSMul ℝ (Hermitian n) := normalHermitianContinuousSMul n
  exact (normalTangentEquiv A).toContinuousLinearEquiv

set_option backward.isDefEq.respectTransparency false in
theorem normalTangent_ball_positive (A : PositiveDefinite n) :
    ∃ r : ℝ, 0 < r ∧ ∀ K : Hermitian n,
      ‖normalTangentEquiv A K‖ < r → (1 + K.val).PosDef := by
  let e := normalTangentContinuousEquiv A
  let f : NormalTangentSpace A → Hermitian n := fun x =>
    (⟨1, Matrix.isHermitian_one⟩ : Hermitian n) + e.symm x
  have hf : Continuous f := continuous_const.add e.symm.continuous
  have hf0 : f 0 = ⟨1, Matrix.isHermitian_one⟩ := by
    simp [f]
  have hN : {x : NormalTangentSpace A | (f x).val.PosDef} ∈ 𝓝 0 := by
    have hp : ∀ᶠ Y in 𝓝 (f 0), Y.val.PosDef := by
      rw [hf0]
      exact hermitianPosDef_mem_nhds _ Matrix.PosDef.one
    exact hf.continuousAt.tendsto.eventually hp
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hN
  refine ⟨r, hr, ?_⟩
  intro K hK
  have h := hball (show normalTangentEquiv A K ∈ Metric.ball 0 r by
    simpa only [Metric.mem_ball, dist_zero_right] using hK)
  change (f (e K)).val.PosDef at h
  simpa only [f, e.symm_apply_apply] using h

/-- The identity transport plus a centered Hermitian coordinate. -/
def normalTransportShift (K : Hermitian n) : Hermitian n :=
  (⟨1, Matrix.isHermitian_one⟩ : Hermitian n) + K

/-- The conjugated map between Hilbert normal-coordinate spaces, extended
by zero outside the source positive-transport chart. -/
def normalConjugate (F : PositiveDefinite n → PositiveDefinite n)
    (A : PositiveDefinite n) (x : NormalTangentSpace A) : NormalTangentSpace (F A) := by
  classical
  let K := (normalTangentEquiv A).symm x
  let T := normalTransportShift K
  exact if hT : T.val.PosDef then
    normalTangentEquiv (F A)
      (normalCoordinate (F A) (F (normalChartPoint A T hT)))
  else 0

theorem normalChartPoint_identity (A : PositiveDefinite n) :
    normalChartPoint A ⟨1, Matrix.isHermitian_one⟩ Matrix.PosDef.one = A := by
  apply Subtype.ext
  change 1 * A.val * 1 = A.val
  simp

set_option backward.isDefEq.respectTransparency false in
theorem normalConjugate_zero (F : PositiveDefinite n → PositiveDefinite n)
    (A : PositiveDefinite n) : normalConjugate F A 0 = 0 := by
  unfold normalConjugate
  simp only [map_zero]
  have hshift : normalTransportShift (0 : Hermitian n) =
      ⟨1, Matrix.isHermitian_one⟩ := by
    simp [normalTransportShift]
  simp only [hshift, normalChartPoint_identity,
    normalCoordinate_self, map_zero]
  split <;> rfl

theorem normalCoordinate_chartPoint (A : PositiveDefinite n) (K : Hermitian n)
    (hT : (normalTransportShift K).val.PosDef) :
    normalCoordinate A (normalChartPoint A (normalTransportShift K) hT) = K := by
  apply Subtype.ext
  change normalTransport A (normalChartPoint A (normalTransportShift K) hT) - 1 = K.val
  rw [normalTransport_chartPoint]
  change 1 + K.val - 1 = K.val
  abel

set_option backward.isDefEq.respectTransparency false in
theorem normalConjugate_valid (F : PositiveDefinite n → PositiveDefinite n)
    (A : PositiveDefinite n) (K : Hermitian n)
    (hT : (normalTransportShift K).val.PosDef) :
    normalConjugate F A (normalTangentEquiv A K) =
      normalTangentEquiv (F A) (normalCoordinate (F A)
        (F (normalChartPoint A (normalTransportShift K) hT))) := by
  unfold normalConjugate
  dsimp only
  split_ifs with h
  · simp only [LinearEquiv.symm_apply_apply]
  · exact False.elim (h (by simpa only [LinearEquiv.symm_apply_apply] using hT))

set_option backward.isDefEq.respectTransparency false in
theorem normalConjugate_at_point (F : PositiveDefinite n → PositiveDefinite n)
    (A B : PositiveDefinite n) :
    normalConjugate F A (normalTangentEquiv A (normalCoordinate A B)) =
      normalTangentEquiv (F A) (normalCoordinate (F A) (F B)) := by
  have hT : normalTransportShift (normalCoordinate A B) =
      ⟨normalTransport A B, (normalTransport_posDef A B).isHermitian⟩ := by
    apply Subtype.ext
    change 1 + (normalTransport A B - 1) = normalTransport A B
    abel
  have hp : (normalTransportShift (normalCoordinate A B)).val.PosDef := by
    rw [hT]
    exact normalTransport_posDef A B
  have hpoint : normalChartPoint A (normalTransportShift (normalCoordinate A B)) hp = B := by
    apply normalTransport_injective A
    rw [normalTransport_chartPoint]
    exact congrArg Subtype.val hT
  rw [normalConjugate_valid F A _ hp, hpoint]

#print axioms normalTangentContinuousEquiv
#print axioms normalTangent_ball_positive
#print axioms normalConjugate_zero
#print axioms normalConjugate_at_point
#print axioms normalTangentEmbedding_injective
end Bures

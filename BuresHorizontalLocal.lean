import BuresOptimalLift
import HermitianSquareSmooth

/-! Exact local metric behavior of horizontal Gram curves. -/

noncomputable section
open scoped MatrixOrder ComplexOrder Matrix.Norms.Frobenius Topology
namespace Bures

private def horizontalOverlapPath (A : PositiveDefinite n)
    (K : Mat n) (hK : K.IsHermitian) (t : ℝ) : Hermitian n := by
  let S := matrixSqrt A.val
  have hS : S.IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg A.val)).isHermitian
  have hSS : (S * S).IsHermitian := by
    change (S * S).conjTranspose = S * S
    rw [Matrix.conjTranspose_mul, hS.eq]
  have hSKS : (S * K * S).IsHermitian := by
    change (S * K * S).conjTranspose = S * K * S
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hS.eq, hK.eq]
    simp only [mul_assoc]
  have heq : S * (S + (t : ℂ) • (K * S)) =
      S * S + (t : ℂ) • (S * K * S) := by
    simp only [mul_add, mul_smul_comm, mul_assoc]
  refine ⟨S * (S + (t : ℂ) • (K * S)), ?_⟩
  rw [heq]
  exact hSS.add (hSKS.smul (by simp [IsSelfAdjoint]))

private theorem horizontalOverlapPath_continuous (A : PositiveDefinite n)
    (K : Mat n) (hK : K.IsHermitian) :
    Continuous (horizontalOverlapPath A K hK) := by
  have hraw : Continuous (fun t : ℝ =>
      matrixSqrt A.val * (matrixSqrt A.val +
        (t : ℂ) • (K * matrixSqrt A.val))) :=
    continuous_const.mul
      (continuous_const.add (Complex.continuous_ofReal.smul continuous_const))
  have hval : Continuous (fun t : ℝ => (horizontalOverlapPath A K hK t).val) := by
    change Continuous (fun t : ℝ => matrixSqrt A.val *
      (matrixSqrt A.val + (t : ℂ) • (K * matrixSqrt A.val)))
    exact hraw
  exact hval.subtype_mk _

private theorem horizontalOverlapPath_zero (A : PositiveDefinite n)
    (K : Mat n) (hK : K.IsHermitian) :
    (horizontalOverlapPath A K hK 0).val = A.val := by
  dsimp [horizontalOverlapPath]
  change matrixSqrt A.val *
    (matrixSqrt A.val + ((0 : ℝ) : ℂ) • (K * matrixSqrt A.val)) = A.val
  simp only [Complex.ofReal_zero, zero_smul, add_zero]
  exact matrixSqrt_mul_self A.property.posSemidef

theorem horizontal_overlap_eventually_posDef (A : PositiveDefinite n)
    (K : Mat n) (hK : K.IsHermitian) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      (matrixSqrt A.val *
        (matrixSqrt A.val + t • (K * matrixSqrt A.val))).PosDef := by
  have hbase : (horizontalOverlapPath A K hK 0).val.PosDef := by
    rw [horizontalOverlapPath_zero]
    exact A.property
  have hnear := (horizontalOverlapPath_continuous A K hK).continuousAt.tendsto.eventually
    (hermitianPosDef_mem_nhds (horizontalOverlapPath A K hK 0) hbase)
  filter_upwards [hnear] with t ht
  have hsm : (t • (K * matrixSqrt A.val) : Mat n) =
      (t : ℂ) • (K * matrixSqrt A.val) := by
    ext i j
    simp [Matrix.smul_apply, Complex.real_smul]
  rw [hsm]
  exact ht

/-- The projected horizontal Gram curve, extended by `A` outside its local
positive region so it is a total Lean function. -/
def horizontalGramPoint (A : PositiveDefinite n) (K : Mat n) (t : ℝ) :
    PositiveDefinite n := by
  let T := matrixSqrt A.val + t • (K * matrixSqrt A.val)
  by_cases h : (matrixSqrt A.val * T).PosDef
  · have hTunit : IsUnit T := isUnit_of_mul_isUnit_right h.isUnit
    exact ⟨gram T, Matrix.PosDef.mul_conjTranspose_self T
      (Matrix.vecMul_injective_of_isUnit hTunit)⟩
  · exact A

theorem horizontalGramPoint_eventually_exact (A : PositiveDefinite n)
    (K : Mat n) (hK : K.IsHermitian) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      distance A (horizontalGramPoint A K t) =
        |t| * ‖K * matrixSqrt A.val‖ := by
  filter_upwards [horizontal_overlap_eventually_posDef A K hK] with t ht
  unfold horizontalGramPoint
  simp only [dif_pos ht]
  exact distance_horizontal_gram_curve A K t _ ht.posSemidef

theorem horizontalGramPoint_squared_speed (A : PositiveDefinite n)
    (K : Mat n) (hK : K.IsHermitian) :
    Filter.Tendsto (fun t : ℝ =>
      distance A (horizontalGramPoint A K t) ^ 2 / t ^ 2)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (tr ((K * A.val + A.val * K) * K) / 2)) := by
  have hnear := horizontalGramPoint_eventually_exact A K hK
  have hnear' : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      distance A (horizontalGramPoint A K t) =
        |t| * ‖K * matrixSqrt A.val‖ :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hnear
  have hA : gram (matrixSqrt A.val) = A.val := by
    rw [gram, (Matrix.nonneg_iff_posSemidef.mp
      (matrixSqrt_nonneg A.val)).isHermitian.eq]
    exact matrixSqrt_mul_self A.property.posSemidef
  have henergy := horizontal_energy_eq_sylvester (matrixSqrt A.val) K hK
  rw [hA] at henergy
  have hnorm : tr ((K * matrixSqrt A.val).conjTranspose *
      (K * matrixSqrt A.val)) = ‖K * matrixSqrt A.val‖ ^ 2 := by
    rw [tr_mul_comm, ← frobenius_sq_eq_tr_gram]
  have htarget : tr ((K * A.val + A.val * K) * K) / 2 =
      ‖K * matrixSqrt A.val‖ ^ 2 := (henergy.symm.trans hnorm)
  rw [htarget]
  apply Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [hnear', self_mem_nhdsWithin] with t hdist ht
  have ht0 : t ≠ 0 := ht
  rw [hdist, mul_pow, sq_abs]
  field_simp [ht0]

#print axioms horizontal_overlap_eventually_posDef
#print axioms horizontalGramPoint_squared_speed

end Bures

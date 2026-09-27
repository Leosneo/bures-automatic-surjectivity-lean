import BuresNormalChart
import BuresInteriorTangent
import BuresCommutingProduct
import Mathlib.Topology.Order.DenselyOrdered

/-! Equality and asymptotic rigidity of square-root translations. -/
noncomputable section
open Filter
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.Frobenius
namespace Bures

/-- The positive-definite point with matrix square root `T`. -/
def squarePoint (T : Mat n) (hT : T.PosDef) : PositiveDefinite n := by
  refine ⟨T * T, ?_⟩
  have h := Matrix.PosDef.mul_conjTranspose_self T
    (Matrix.vecMul_injective_of_isUnit hT.isUnit)
  rw [hT.isHermitian.eq] at h
  exact h

@[simp] theorem squarePoint_val (T : Mat n) (hT : T.PosDef) :
    (squarePoint T hT).val = T * T := rfl

@[simp] theorem matrixSqrt_squarePoint (T : Mat n) (hT : T.PosDef) :
    matrixSqrt (squarePoint T hT).val = T := by
  exact matrixSqrt_unique hT.posSemidef rfl

/-- Equality between Bures distance and the Frobenius distance of positive
square roots forces the square roots to commute. -/
theorem commute_of_distance_eq_sqrt_norm (T S : Mat n)
    (hT : T.PosDef) (hS : S.PosDef)
    (hd : distance (squarePoint T hT) (squarePoint S hS) = ‖T - S‖) :
    Commute T S := by
  let A := squarePoint T hT
  let B := squarePoint S hS
  have hGram : gram S = B.val := by
    simp [gram, B, squarePoint, hS.isHermitian.eq]
  have hOpt : optimalLift A B = S := by
    apply optimalLift_eq_of_realizes_distance A B S hGram
    simpa only [A, matrixSqrt_squarePoint] using hd
  have hOverlap := optimalLift_overlap A B
  rw [hOpt, matrixSqrt_squarePoint] at hOverlap
  have hHerm : (T * S).IsHermitian := by
    rw [hOverlap]
    exact (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg _)).isHermitian
  have hTS : S * T = T * S := by
    have hh := hHerm.eq
    rw [Matrix.conjTranspose_mul, hT.isHermitian.eq, hS.isHermitian.eq] at hh
    exact hh
  exact hTS.symm

/-- Equality with the Frobenius separation of canonical positive square
roots forces the roots to commute. -/
theorem commute_sqrts_of_distance_eq_norm (A B : PositiveDefinite n)
    (hd : distance A B = ‖matrixSqrt A.val - matrixSqrt B.val‖) :
    Commute (matrixSqrt A.val) (matrixSqrt B.val) := by
  have hA : (matrixSqrt A.val).PosDef :=
    (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg A.val)).posDef_iff_isUnit.mpr
      (A.property.isStrictlyPositive.sqrt).2
  have hB : (matrixSqrt B.val).PosDef :=
    (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg B.val)).posDef_iff_isUnit.mpr
      (B.property.isStrictlyPositive.sqrt).2
  have hAeq : squarePoint (matrixSqrt A.val) hA = A := by
    apply Subtype.ext
    exact matrixSqrt_mul_self A.property.posSemidef
  have hBeq : squarePoint (matrixSqrt B.val) hB = B := by
    apply Subtype.ext
    exact matrixSqrt_mul_self B.property.posSemidef
  apply commute_of_distance_eq_sqrt_norm _ _ hA hB
  simpa only [hAeq, hBeq] using hd

/-- Commuting positive roots realize Bures distance by their plain
Frobenius separation. -/
theorem distance_eq_sqrt_norm_of_commute (T S : Mat n)
    (hT : T.PosDef) (hS : S.PosDef) (hc : Commute T S) :
    distance (squarePoint T hT) (squarePoint S hS) = ‖T - S‖ := by
  let A := squarePoint T hT
  let B := squarePoint S hS
  have hGram : gram S = B.val := by
    simp [gram, B, squarePoint, hS.isHermitian.eq]
  have hOverlap : (matrixSqrt A.val * S).PosSemidef := by
    rw [show matrixSqrt A.val = T from matrixSqrt_squarePoint T hT]
    exact posSemidef_mul_of_commute hT.posSemidef hS.posSemidef hc
  have hd := distance_eq_positive_overlap_factor A B S hGram hOverlap
  simpa only [A, matrixSqrt_squarePoint] using hd

/-- Add a fixed positive-semidefinite Hermitian matrix to the positive
square root, then square. -/
def squareTranslation (D : Hermitian n) (hD : D.val.PosSemidef)
    (A : PositiveDefinite n) : PositiveDefinite n := by
  let T := matrixSqrt A.val + D.val
  have hS : (matrixSqrt A.val).PosDef :=
    (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg A.val)).posDef_iff_isUnit.mpr
      (A.property.isStrictlyPositive.sqrt).2
  exact squarePoint T (hS.add_posSemidef hD)

@[simp] theorem matrixSqrt_squareTranslation (D : Hermitian n)
    (hD : D.val.PosSemidef) (A : PositiveDefinite n) :
    matrixSqrt (squareTranslation D hD A).val =
      matrixSqrt A.val + D.val := by
  unfold squareTranslation
  exact matrixSqrt_squarePoint _ _

/-- A distance-preserving square-root translation has displacement commuting
with every positive definite Hermitian matrix. -/
theorem squareTranslation_commute_posDef (D : Hermitian n)
    (hD : D.val.PosSemidef) (hF : PreservesDistance (squareTranslation D hD))
    (T : Mat n) (hT : T.PosDef) : Commute T D.val := by
  have hOne : (1 : Mat n).PosDef := Matrix.PosDef.one
  have hbase : Commute T (1 : Mat n) := Commute.one_right T
  have hdBase := distance_eq_sqrt_norm_of_commute T 1 hT hOne hbase
  let A := squarePoint T hT
  let B := squarePoint 1 hOne
  have hdist : distance (squareTranslation D hD A)
      (squareTranslation D hD B) =
      ‖matrixSqrt (squareTranslation D hD A).val -
        matrixSqrt (squareTranslation D hD B).val‖ := by
    rw [matrixSqrt_squareTranslation, matrixSqrt_squareTranslation,
      show matrixSqrt A.val = T from matrixSqrt_squarePoint T hT,
      show matrixSqrt B.val = 1 from matrixSqrt_squarePoint 1 hOne,
      hF A B, hdBase]
    congr 1
    abel
  have hc := commute_sqrts_of_distance_eq_norm _ _ hdist
  rw [matrixSqrt_squareTranslation, matrixSqrt_squareTranslation,
    show matrixSqrt A.val = T from matrixSqrt_squarePoint T hT,
    show matrixSqrt B.val = 1 from matrixSqrt_squarePoint 1 hOne] at hc
  have hh := hc.eq
  have heq : T * D.val = D.val * T := by
    calc
      T * D.val = (T + D.val) * (1 + D.val) -
          (1 + D.val) * (T + D.val) + D.val * T := by noncomm_ring
      _ = D.val * T := by rw [hh]; simp
  exact heq

/-- Any distance-preserving square-root translation has central displacement.
The remaining step is to show the scalar displacement is zero. -/
theorem squareTranslation_displacement_scalar (D : Hermitian n)
    (hD : D.val.PosSemidef) (hF : PreservesDistance (squareTranslation D hD)) :
    ∃ c : ℝ, D.val = c • (1 : Mat n) := by
  apply (hermitian_common_commutant_iff D.property).mp
  intro L hL
  let U : Hermitian n := ⟨L, hL⟩
  let I : Hermitian n := ⟨1, Matrix.isHermitian_one⟩
  have hI : I.val.PosDef := Matrix.PosDef.one
  have hnear := hermitianPosDef_mem_nhds I hI
  have hcont : Filter.Tendsto (fun t : ℝ => I + t • U) (𝓝 (0 : ℝ)) (𝓝 I) := by
    have hc : Continuous (fun t : ℝ => I + t • U) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hz : (0 : ℝ) • U = 0 := by
      apply Subtype.ext
      ext i j
      simp [Matrix.smul_apply, Complex.real_smul]
    simpa only [hz, add_zero] using (hc.continuousAt (x := (0 : ℝ))).tendsto
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (I + t • U).val.PosDef :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (hcont.eventually hnear)
  haveI : NeBot (𝓝[>] (0 : ℝ)) := nhdsGT_neBot 0
  have hboth : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ (I + t • U).val.PosDef := by
    filter_upwards [self_mem_nhdsWithin, hev] with t ht hp
    exact ⟨ht, hp⟩
  obtain ⟨t, htpos, hT⟩ := hboth.exists
  have ht : 0 < t := htpos
  let T : Mat n := (I + t • U).val
  have hcomm := squareTranslation_commute_posDef D hD hF T hT
  have hscalar : t • (L * D.val - D.val * L) = T * D.val - D.val * T := by
    have he : T = 1 + t • L := rfl
    rw [he]
    have hs : t • (L * D.val - D.val * L) =
        (t • L) * D.val - D.val * (t • L) := by
      calc
        t • (L * D.val - D.val * L) =
            t • (L * D.val) - t • (D.val * L) := smul_sub t _ _
        _ = (t • L) * D.val - D.val * (t • L) := by
          rw [smul_mul_assoc, mul_smul_comm]
    rw [hs]
    noncomm_ring
  have hzero : t • (L * D.val - D.val * L) = 0 := by
    rw [hscalar]
    exact sub_eq_zero.mpr hcomm.eq
  have hLD : L * D.val = D.val * L :=
    sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_left ht.ne')
  exact hLD.symm

#print axioms squareTranslation_displacement_scalar
#print axioms commute_of_distance_eq_sqrt_norm
#print axioms distance_eq_sqrt_norm_of_commute
end Bures

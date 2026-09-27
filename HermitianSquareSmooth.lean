import BuresSquareDerivative
import BuresTopology
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

noncomputable section
open Filter
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContinuousLinearMap RightActions
namespace Bures
local instance (n : ℕ) : CStarAlgebra (Mat n) where

private theorem hermitian_closed (n : ℕ) : IsClosed (selfAdjoint (Mat n) : Set (Mat n)) := by
  change IsClosed {x : Mat n | star x = x}
  exact isClosed_eq continuous_star continuous_id

local instance (n : ℕ) : CompleteSpace (selfAdjoint (Mat n)) :=
  (hermitian_closed n).completeSpace_coe

abbrev Hermitian (n : ℕ) := selfAdjoint (Mat n)

/-- The Hermitian matrices embed continuously and real-linearly in all matrices. -/
def hermitianInclusion (n : ℕ) : Hermitian n →L[ℝ] Mat n where
  toFun := Subtype.val
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
  cont := continuous_subtype_val

/-- The Sylvester operator acts continuously on the real space of Hermitian matrices. -/
def hermitianSylvester (A : Hermitian n) : Hermitian n →L[ℝ] Hermitian n where
  toFun H := ⟨H.val * A.val + A.val * H.val, by
    change star (H.val * A.val + A.val * H.val) = _
    simp [star_add, star_mul, add_comm]⟩
  map_add' := by
    intro H K
    apply Subtype.ext
    change (H.val + K.val) * A.val + A.val * (H.val + K.val) =
      (H.val * A.val + A.val * H.val) + (K.val * A.val + A.val * K.val)
    noncomm_ring
  map_smul' := by
    intro r H
    apply Subtype.ext
    change (r • H.val) * A.val + A.val * (r • H.val) =
      r • (H.val * A.val + A.val * H.val)
    simpa only [smul_mul_assoc, mul_smul_comm] using
      (smul_add r (H.val * A.val) (A.val * H.val)).symm
  cont := by
    exact (((continuous_subtype_val.mul continuous_const).add
      (continuous_const.mul continuous_subtype_val)).subtype_mk _)

/-- On a positive Hermitian matrix, the Hermitian Sylvester operator is bijective. -/
theorem hermitianSylvester_bijective (A : Hermitian n)
    (hA : A.val.PosDef) : Function.Bijective (hermitianSylvester A) := by
  constructor
  · intro H K hHK
    have ht : H.val * A.val + A.val * H.val =
        K.val * A.val + A.val * K.val := congrArg Subtype.val hHK
    obtain ⟨L, hL, hu⟩ := posDef_sylvester_existsUnique hA
      (H.val * A.val + A.val * H.val)
    apply Subtype.ext
    exact (hu H.val rfl).trans (hu K.val ht.symm).symm
  · intro X
    obtain ⟨K, ⟨hK, hEq⟩, _⟩ :=
      posDef_hermitian_sylvester_existsUnique hA X.property
    exact ⟨⟨K, hK⟩, Subtype.ext hEq⟩

/-- The inverse of the positive Hermitian Sylvester operator is continuous. -/
noncomputable def hermitianSylvesterEquiv (A : Hermitian n)
    (hA : A.val.PosDef) : Hermitian n ≃L[ℝ] Hermitian n := by
  letI : CompleteSpace (Hermitian n) := (hermitian_closed n).completeSpace_coe
  have hi : CompleteSpace (Hermitian n) := inferInstance
  exact @ContinuousLinearEquiv.ofBijective ℝ ℝ _ _ (RingHom.id ℝ)
    (Hermitian n) _ _ (Hermitian n) _ _ (RingHom.id ℝ) _ _ _ hi hi _
    (hermitianSylvester A)
    (LinearMap.ker_eq_bot.mpr (hermitianSylvester_bijective A hA).injective)
    (LinearMap.range_eq_top.mpr (hermitianSylvester_bijective A hA).surjective)

/-- Matrix squaring regarded as a map of the real Hermitian space. -/
def hermitianSquare (X : Hermitian n) : Hermitian n :=
  ⟨X.val * X.val, by
    change star (X.val * X.val) = _
    simp [star_mul]⟩

private theorem hermitianSquare_eq_projection (X : Hermitian n) :
    hermitianSquare X = (selfAdjointPartL ℝ (Mat n)) (X.val * X.val) := by
  exact (IsSelfAdjoint.selfAdjointPart_apply ℝ
    (show IsSelfAdjoint (X.val * X.val) by
      simpa only [X.property.star_eq] using IsSelfAdjoint.star_mul_self X.val)).symm

/-- The actual derivative of Hermitian matrix squaring is its Sylvester map. -/
theorem hasFDerivAt_hermitianSquare (X : Hermitian n) :
    HasFDerivAt (hermitianSquare (n := n)) (hermitianSylvester X) X := by
  have hinc : HasFDerivAt (hermitianInclusion n) (hermitianInclusion n) X :=
    (hermitianInclusion n).hasFDerivAt
  have hs := hinc.mul' hinc
  have hp := (selfAdjointPartL ℝ (Mat n)).hasFDerivAt.comp X hs
  have hfun : (fun Y : Hermitian n =>
      (selfAdjointPartL ℝ (Mat n)) (Y.val * Y.val)) = hermitianSquare := by
    funext Y
    exact (hermitianSquare_eq_projection Y).symm
  change HasFDerivAt (fun Y : Hermitian n =>
    (selfAdjointPartL ℝ (Mat n)) (Y.val * Y.val)) _ X at hp
  rw [hfun] at hp
  have hder : hermitianSylvester X =
      (selfAdjointPartL ℝ (Mat n)).comp
        ((X.val •> hermitianInclusion n) + (hermitianInclusion n <• X.val)) := by
    apply ContinuousLinearMap.ext
    intro H
    apply Subtype.ext
    change H.val * X.val + X.val * H.val =
      ((selfAdjointPartL ℝ (Mat n)).comp
        ((X.val •> hermitianInclusion n) + (hermitianInclusion n <• X.val)) H).val
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply]
    have hself : IsSelfAdjoint (X.val * H.val + H.val * X.val) := by
      change star (X.val * H.val + H.val * X.val) = _
      simp [star_add, star_mul, add_comm]
    have hp' := IsSelfAdjoint.coe_selfAdjointPart_apply ℝ hself
    calc
      H.val * X.val + X.val * H.val =
          ((selfAdjointPartL ℝ (Mat n)) (X.val * H.val + H.val * X.val)).val := by
            rw [add_comm]
            exact hp'.symm
      _ = _ := by
        rw [map_add]
        simp [hermitianInclusion, ContinuousLinearMap.smul_apply]
  exact hder ▸ hp

theorem hasStrictFDerivAt_hermitianSquare (X : Hermitian n) :
    HasStrictFDerivAt (hermitianSquare (n := n)) (hermitianSylvester X) X := by
  have hinc : HasStrictFDerivAt (hermitianInclusion n) (hermitianInclusion n) X :=
    (hermitianInclusion n).hasStrictFDerivAt
  have hs := hinc.mul' hinc
  have hp := (selfAdjointPartL ℝ (Mat n)).hasStrictFDerivAt.comp X hs
  have hfun : (fun Y : Hermitian n =>
      (selfAdjointPartL ℝ (Mat n)) (Y.val * Y.val)) = hermitianSquare := by
    funext Y
    exact (hermitianSquare_eq_projection Y).symm
  change HasStrictFDerivAt (fun Y : Hermitian n =>
    (selfAdjointPartL ℝ (Mat n)) (Y.val * Y.val)) _ X at hp
  rw [hfun] at hp
  have hder : hermitianSylvester X =
      (selfAdjointPartL ℝ (Mat n)).comp
        ((X.val •> hermitianInclusion n) + (hermitianInclusion n <• X.val)) := by
    apply ContinuousLinearMap.ext
    intro H
    apply Subtype.ext
    change H.val * X.val + X.val * H.val =
      ((selfAdjointPartL ℝ (Mat n)).comp
        ((X.val •> hermitianInclusion n) + (hermitianInclusion n <• X.val)) H).val
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply]
    have hself : IsSelfAdjoint (X.val * H.val + H.val * X.val) := by
      change star (X.val * H.val + H.val * X.val) = _
      simp [star_add, star_mul, add_comm]
    have hp' := IsSelfAdjoint.coe_selfAdjointPart_apply ℝ hself
    calc
      H.val * X.val + X.val * H.val =
          ((selfAdjointPartL ℝ (Mat n)) (X.val * H.val + H.val * X.val)).val := by
            rw [add_comm]
            exact hp'.symm
      _ = _ := by
        rw [map_add]
        simp [hermitianInclusion, ContinuousLinearMap.smul_apply]
  exact hder ▸ hp


/-- Hermitian square root from the literal CFC square root. -/
def hermitianSqrt (X : Hermitian n) : Hermitian n :=
  ⟨matrixSqrt X.val, by
    change star (matrixSqrt X.val) = _
    exact (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg X.val)).isHermitian.eq⟩

def hermitianPSD (n : ℕ) : Set (Hermitian n) :=
  {X | X.val.PosSemidef}

theorem continuousOn_hermitianSqrt (n : ℕ) :
    ContinuousOn (hermitianSqrt (n := n)) (hermitianPSD n) := by
  have h : ContinuousOn (fun X : Hermitian n => matrixSqrt X.val) (hermitianPSD n) :=
    continuousOn_matrixSqrt.comp continuous_subtype_val.continuousOn (by
      intro X hX
      exact hX)
  intro X hX
  exact tendsto_subtype_rng.mpr (h X hX)

theorem hermitianSquare_sqrt (X : Hermitian n)
    (hX : X ∈ hermitianPSD n) :
    hermitianSquare (hermitianSqrt X) = X := by
  apply Subtype.ext
  exact matrixSqrt_mul_self hX

/-- Derivative of the actual CFC square root along the positive semidefinite cone. -/
theorem hasFDerivWithinAt_hermitianSqrt (A : Hermitian n)
    (hA : A.val.PosDef) :
    HasFDerivWithinAt (hermitianSqrt (n := n))
      ((hermitianSylvesterEquiv (hermitianSqrt A) (by
        exact (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg A.val)).posDef_iff_isUnit.mpr
          (hA.isStrictlyPositive.sqrt).2)).symm : Hermitian n →L[ℝ] Hermitian n)
      (hermitianPSD n) A := by
  let S := hermitianSqrt A
  have hS : S.val.PosDef :=
    (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg A.val)).posDef_iff_isUnit.mpr
      (hA.isStrictlyPositive.sqrt).2
  have hApsd : A ∈ hermitianPSD n := hA.posSemidef
  have hSA : hermitianSquare S = A := hermitianSquare_sqrt A hApsd
  have hcont : Tendsto hermitianSqrt (𝓝[hermitianPSD n] A) (𝓝 S) := by
    simpa only [S] using (continuousOn_hermitianSqrt n A hApsd).tendsto
  have hder := (hasFDerivAt_hermitianSquare S).hasFDerivWithinAt (s := Set.univ)
  have hleft : ∀ᶠ X in 𝓝[hermitianPSD n] A,
      hermitianSquare (hermitianSqrt X) = X := by
    filter_upwards [self_mem_nhdsWithin] with X hX
    exact hermitianSquare_sqrt X hX
  have heq : ((hermitianSylvesterEquiv S hS : Hermitian n ≃L[ℝ] Hermitian n) :
      Hermitian n →L[ℝ] Hermitian n) = hermitianSylvester S := by
    apply ContinuousLinearMap.ext
    intro H
    rfl
  have hcont' : Tendsto hermitianSqrt (𝓝[hermitianPSD n] A)
      (𝓝[Set.univ] (hermitianSqrt A)) := by
    simpa only [nhdsWithin_univ] using hcont
  have hcomp := (hder.congr_fderiv heq.symm).of_local_left_inverse
    hcont' hApsd hleft
  simpa only [S] using hcomp

/-- Positive semidefinite Hermitian matrices contain a neighborhood of every
positive definite matrix. This follows from local openness of the square map. -/
theorem hermitianPSD_mem_nhds (A : Hermitian n) (hA : A.val.PosDef) :
    hermitianPSD n ∈ 𝓝 A := by
  letI : CompleteSpace (Hermitian n) := (hermitian_closed n).completeSpace_coe
  let S := hermitianSqrt A
  have hS : S.val.PosDef :=
    (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg A.val)).posDef_iff_isUnit.mpr
      (hA.isStrictlyPositive.sqrt).2
  let e := hermitianSylvesterEquiv S hS
  have heq : (e : Hermitian n →L[ℝ] Hermitian n) = hermitianSylvester S := by
    apply ContinuousLinearMap.ext
    intro H
    rfl
  have hstrict : HasStrictFDerivAt hermitianSquare
      (e : Hermitian n →L[ℝ] Hermitian n) S := by
    simpa only [heq] using hasStrictFDerivAt_hermitianSquare S
  have hi : CompleteSpace (Hermitian n) := (hermitian_closed n).completeSpace_coe
  have hmap := @HasStrictFDerivAt.map_nhds_eq_of_equiv ℝ _
    (Hermitian n) _ _ (Hermitian n) _ _ hermitianSquare e S hi hstrict
  have hall : ∀ X : Hermitian n, hermitianSquare X ∈ hermitianPSD n := by
    intro X
    exact Matrix.nonneg_iff_posSemidef.mp (IsSelfAdjoint.mul_self_nonneg X.property)
  have hev : hermitianPSD n ∈ Filter.map hermitianSquare (𝓝 S) := by
    change (fun X : Hermitian n => hermitianSquare X ∈ hermitianPSD n) ∈ 𝓝 S
    exact Filter.Eventually.of_forall hall
  have hSA : hermitianSquare S = A := hermitianSquare_sqrt A hA.posSemidef
  have hmap' : Filter.map hermitianSquare (𝓝 S) = 𝓝 A := by
    simpa only [hSA] using hmap
  exact hmap' ▸ hev

/-- Ordinary real Fréchet derivative of the literal CFC matrix square root at
a positive definite Hermitian matrix. -/
theorem hasFDerivAt_hermitianSqrt (A : Hermitian n) (hA : A.val.PosDef) :
    HasFDerivAt (hermitianSqrt (n := n))
      ((hermitianSylvesterEquiv (hermitianSqrt A) (by
        exact (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg A.val)).posDef_iff_isUnit.mpr
          (hA.isStrictlyPositive.sqrt).2)).symm : Hermitian n →L[ℝ] Hermitian n) A :=
  (hasFDerivWithinAt_hermitianSqrt A hA).hasFDerivAt
    (hermitianPSD_mem_nhds A hA)

/-- Positive definiteness is an open neighborhood condition on Hermitian matrices. -/
theorem hermitianPosDef_mem_nhds (A : Hermitian n) (hA : A.val.PosDef) :
    {X : Hermitian n | X.val.PosDef} ∈ 𝓝 A := by
  have hunit : {X : Hermitian n | IsUnit X.val} ∈ 𝓝 A :=
    (Units.isOpen.preimage continuous_subtype_val).mem_nhds hA.isUnit
  have hpsd := hermitianPSD_mem_nhds A hA
  have heq : {X : Hermitian n | X.val.PosDef} =
      hermitianPSD n ∩ {X : Hermitian n | IsUnit X.val} := by
    ext X
    constructor
    · intro hX
      exact ⟨hX.posSemidef, hX.isUnit⟩
    · rintro ⟨hX, hu⟩
      exact hX.posDef_iff_isUnit.mpr hu
  rw [heq]
  exact Filter.inter_mem hpsd hunit

end Bures

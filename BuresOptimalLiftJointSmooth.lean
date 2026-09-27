import BuresOptimalLiftSmooth
import BuresSquaredSmooth

/-! Joint real Fréchet differentiability of the literal optimal-lift formula
near a pair of positive definite matrices. -/

noncomputable section
open Filter
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContinuousLinearMap
namespace Bures
local instance (n : ℕ) : CStarAlgebra (Mat n) where

private local instance (n : ℕ) : ContinuousSMul ℝ (Mat n) where
  continuous_smul := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    have h : Continuous (fun p : ℝ × Mat n => (p.1 : ℂ) * p.2 i j) :=
      (Complex.continuous_ofReal.comp continuous_fst).mul
        ((continuous_apply j).comp ((continuous_apply i).comp continuous_snd))
    simpa only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul] using h

private local instance (n : ℕ) : ContinuousSMul ℝ (Hermitian n) where
  continuous_smul := by
    have h : Continuous (fun p : ℝ × Hermitian n =>
        (p.1 • p.2.val : Mat n)) := by
      exact continuous_fst.smul (continuous_subtype_val.comp continuous_snd)
    exact h.subtype_mk _


private def sandwichPair (p : Hermitian n × Hermitian n) : Hermitian n :=
  ⟨(hermitianSqrt p.1).val * p.2.val * (hermitianSqrt p.1).val, by
    change star ((hermitianSqrt p.1).val * p.2.val *
      (hermitianSqrt p.1).val) = _
    simp [star_mul, mul_assoc]⟩

private theorem sandwichPair_eq_projection (p : Hermitian n × Hermitian n) :
    sandwichPair p = (selfAdjointPartL ℝ (Mat n))
      ((hermitianSqrt p.1).val * p.2.val * (hermitianSqrt p.1).val) := by
  exact (IsSelfAdjoint.selfAdjointPart_apply ℝ
    (show IsSelfAdjoint ((hermitianSqrt p.1).val * p.2.val *
      (hermitianSqrt p.1).val) by
      change star ((hermitianSqrt p.1).val * p.2.val *
        (hermitianSqrt p.1).val) = _
      simp [star_mul, mul_assoc])).symm

private theorem differentiableAt_sandwichPair (A B : Hermitian n)
    (hA : A.val.PosDef) : DifferentiableAt ℝ (sandwichPair (n := n)) (A, B) := by
  have hfst : DifferentiableAt ℝ (fun p : Hermitian n × Hermitian n => p.1) (A, B) :=
    differentiableAt_fst
  have hsnd : DifferentiableAt ℝ (fun p : Hermitian n × Hermitian n => p.2) (A, B) :=
    differentiableAt_snd
  have hs : DifferentiableAt ℝ
      (fun p : Hermitian n × Hermitian n => (hermitianSqrt p.1).val) (A, B) := by
    have h := (hasFDerivAt_hermitianSqrt A hA).differentiableAt.comp (A, B) hfst
    simpa only [Function.comp_def] using
      (hermitianInclusion n).differentiableAt.comp (A, B) h
  have hy : DifferentiableAt ℝ
      (fun p : Hermitian n × Hermitian n => p.2.val) (A, B) := by
    simpa only [Function.comp_def] using
      (hermitianInclusion n).differentiableAt.comp (A, B) hsnd
  have hm := (hs.mul hy).mul hs
  have hp := (selfAdjointPartL ℝ (Mat n)).differentiableAt.comp (A, B) hm
  change DifferentiableAt ℝ (fun p : Hermitian n × Hermitian n =>
    (selfAdjointPartL ℝ (Mat n))
      ((hermitianSqrt p.1).val * p.2.val * (hermitianSqrt p.1).val)) (A, B) at hp
  simpa only [← sandwichPair_eq_projection] using hp

/-- The optimal lift formula on arbitrary Hermitian pairs. It agrees with
the literal Bures optimal lift when both arguments are positive definite. -/
def optimalLiftPair (p : Hermitian n × Hermitian n) : Mat n :=
  (hermitianSqrt p.1).val⁻¹ * (hermitianSqrt (sandwichPair p)).val

theorem optimalLiftPair_eq (A B : PositiveDefinite n) :
    optimalLiftPair
      (⟨A.val, A.property.isHermitian⟩,
       ⟨B.val, B.property.isHermitian⟩) = optimalLift A B := rfl

theorem differentiableAt_optimalLiftPair (A B : PositiveDefinite n) :
    DifferentiableAt ℝ (optimalLiftPair (n := n))
      (⟨A.val, A.property.isHermitian⟩,
       ⟨B.val, B.property.isHermitian⟩) := by
  let a : Hermitian n := ⟨A.val, A.property.isHermitian⟩
  let b : Hermitian n := ⟨B.val, B.property.isHermitian⟩
  have hfst : DifferentiableAt ℝ (fun p : Hermitian n × Hermitian n => p.1) (a, b) :=
    differentiableAt_fst
  have hs : DifferentiableAt ℝ
      (fun p : Hermitian n × Hermitian n => (hermitianSqrt p.1).val) (a, b) := by
    have h := (hasFDerivAt_hermitianSqrt a A.property).differentiableAt.comp (a, b) hfst
    simpa only [Function.comp_def] using
      (hermitianInclusion n).differentiableAt.comp (a, b) h
  have hi : DifferentiableAt ℝ
      (fun p : Hermitian n × Hermitian n => (hermitianSqrt p.1).val⁻¹) (a, b) := by
    simpa only [Matrix.nonsing_inv_eq_ringInverse] using
      hs.inverse (matrixSqrt_isUnit A)
  have hsp : DifferentiableAt ℝ
      (fun p : Hermitian n × Hermitian n => sandwichPair p) (a, b) :=
    differentiableAt_sandwichPair a b A.property
  have hP : (sandwichPair (a, b)).val.PosDef := by
    have hinj : Function.Injective (matrixSqrt A.val).vecMul :=
      Matrix.vecMul_injective_iff_isUnit.mpr (matrixSqrt_isUnit A)
    have hp := B.property.mul_mul_conjTranspose_same hinj
    change (matrixSqrt A.val * B.val * matrixSqrt A.val).PosDef
    rw [(Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg A.val)).isHermitian.eq] at hp
    exact hp
  have hr : DifferentiableAt ℝ
      (fun p : Hermitian n × Hermitian n => (hermitianSqrt (sandwichPair p)).val)
      (a, b) := by
    have h := (hasFDerivAt_hermitianSqrt (sandwichPair (a, b)) hP).differentiableAt.comp
      (a, b) hsp
    simpa only [Function.comp_def] using
      (hermitianInclusion n).differentiableAt.comp (a, b) h
  simpa only [optimalLiftPair, a, b] using hi.mul hr

/-- The difference of a canonical square-root representative and the
optimal lift of the second endpoint. Its norm is exactly Bures distance
on positive definite pairs. -/
def optimalDifferencePair (p : Hermitian n × Hermitian n) : Mat n :=
  (hermitianSqrt p.1).val - optimalLiftPair p

theorem differentiableAt_optimalDifferencePair (A B : PositiveDefinite n) :
    DifferentiableAt ℝ (optimalDifferencePair (n := n))
      (⟨A.val, A.property.isHermitian⟩,
       ⟨B.val, B.property.isHermitian⟩) := by
  let a : Hermitian n := ⟨A.val, A.property.isHermitian⟩
  let b : Hermitian n := ⟨B.val, B.property.isHermitian⟩
  have hfst : DifferentiableAt ℝ (fun p : Hermitian n × Hermitian n => p.1) (a, b) :=
    differentiableAt_fst
  have hs : DifferentiableAt ℝ
      (fun p : Hermitian n × Hermitian n => (hermitianSqrt p.1).val) (a, b) := by
    have h := (hasFDerivAt_hermitianSqrt a A.property).differentiableAt.comp
      (a, b) hfst
    simpa only [Function.comp_def] using
      (hermitianInclusion n).differentiableAt.comp (a, b) h
  exact hs.sub (differentiableAt_optimalLiftPair A B)

open scoped Matrix.Norms.Frobenius in
theorem distance_eq_norm_optimalDifferencePair (A B : PositiveDefinite n) :
    distance A B = ‖optimalDifferencePair
      (⟨A.val, A.property.isHermitian⟩,
       ⟨B.val, B.property.isHermitian⟩)‖ := by
  simpa only [optimalDifferencePair, optimalLiftPair_eq] using
    distance_eq_optimalLift_norm A B

theorem optimalDifferencePair_diagonal_zero (A : PositiveDefinite n) :
    optimalDifferencePair
      (⟨A.val, A.property.isHermitian⟩,
       ⟨A.val, A.property.isHermitian⟩) = 0 := by
  simp only [optimalDifferencePair, optimalLiftPair_eq, optimalLift_self]
  change matrixSqrt A.val - matrixSqrt A.val = 0
  exact sub_self _

/-- The first-order difference lift annihilates simultaneous motion of both
endpoints. Hence its derivative at the diagonal depends only on their
relative displacement. -/
theorem optimalDifferencePair_fderiv_diagonal_zero (A : PositiveDefinite n)
    (H : Hermitian n) :
    (fderiv ℝ (optimalDifferencePair (n := n))
      (⟨A.val, A.property.isHermitian⟩,
       ⟨A.val, A.property.isHermitian⟩)) (H, H) = 0 := by
  let a : Hermitian n := ⟨A.val, A.property.isHermitian⟩
  let f := optimalDifferencePair (n := n)
  let D := fderiv ℝ f (a, a)
  have hf : HasFDerivAt f D (a, a) :=
    (differentiableAt_optimalDifferencePair A A).hasFDerivAt
  have hd : HasFDerivAt (fun X : Hermitian n => (X, X))
      ((ContinuousLinearMap.id ℝ (Hermitian n)).prod
        (ContinuousLinearMap.id ℝ (Hermitian n))) a :=
    (hasFDerivAt_id a).prodMk (hasFDerivAt_id a)
  have hcomp : HasFDerivAt (fun X : Hermitian n => f (X, X))
      (D.comp ((ContinuousLinearMap.id ℝ (Hermitian n)).prod
        (ContinuousLinearMap.id ℝ (Hermitian n)))) a := by
    simpa only [Function.comp_def] using
      (HasFDerivAt.comp (f := fun X : Hermitian n => (X, X)) a hf hd)
  have hpd := hermitianPosDef_mem_nhds a A.property
  have hev : (fun X : Hermitian n => (0 : Mat n)) =ᶠ[𝓝 a]
      (fun X => f (X, X)) := by
    filter_upwards [hpd] with X hX
    let P : PositiveDefinite n := ⟨X.val, hX⟩
    exact (optimalDifferencePair_diagonal_zero P).symm
  have hconst : HasFDerivAt (fun X : Hermitian n => (0 : Mat n)) 0 a :=
    hasFDerivAt_const (𝕜 := ℝ) (0 : Mat n) a
  have hcomp0 : HasFDerivAt (fun X : Hermitian n => f (X, X)) 0 a :=
    hconst.congr_of_eventuallyEq hev.symm
  have hsmul : ContinuousSMul ℝ (Hermitian n) := inferInstance
  have hsmulMat : ContinuousSMul ℝ (Mat n) := inferInstance
  letI : ContinuousSMul ℝ (Hermitian n) := hsmul
  letI : ContinuousSMul ℝ (Mat n) := hsmulMat
  have hD : D.comp ((ContinuousLinearMap.id ℝ (Hermitian n)).prod
        (ContinuousLinearMap.id ℝ (Hermitian n))) = 0 :=
    @HasFDerivAt.unique ℝ _ (Hermitian n) _ _ _ _ hsmul
      (Mat n) _ _ _ _ hsmulMat _ _ _ _ _ hcomp hcomp0
  have := congrArg (fun L : Hermitian n →L[ℝ] Mat n => L H) hD
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply] using this

/-- Linear part of the literal Bures lift difference at the diagonal. -/
def optimalDifferenceTangent (A : PositiveDefinite n) : Hermitian n →L[ℝ] Mat n :=
  (fderiv ℝ (optimalDifferencePair (n := n))
    (⟨A.val, A.property.isHermitian⟩,
     ⟨A.val, A.property.isHermitian⟩)).comp
    (ContinuousLinearMap.inl ℝ (Hermitian n) (Hermitian n))

theorem optimalDifferencePair_fderiv_eq_tangent (A : PositiveDefinite n)
    (H K : Hermitian n) :
    (fderiv ℝ (optimalDifferencePair (n := n))
      (⟨A.val, A.property.isHermitian⟩,
       ⟨A.val, A.property.isHermitian⟩)) (H, K) =
      optimalDifferenceTangent A (H - K) := by
  let D := fderiv ℝ (optimalDifferencePair (n := n))
    (⟨A.val, A.property.isHermitian⟩,
     ⟨A.val, A.property.isHermitian⟩)
  have hdecomp : (H, K) = (H - K, 0) + (K, K) := by
    ext <;> simp
  calc
    D (H, K) = D ((H - K, 0) + (K, K)) := by rw [hdecomp]
    _ = D (H - K, 0) + D (K, K) := map_add D _ _
    _ = D (H - K, 0) := by
      rw [optimalDifferencePair_fderiv_diagonal_zero A K, add_zero]
    _ = optimalDifferenceTangent A (H - K) := rfl

/-- Uniform first-order two-point expansion of the exact optimal-lift
difference, in the real normed space of matrix pairs. The error is little-o
of the distance of the pair to the diagonal base point. -/
theorem optimalDifferencePair_tangent_littleO (A : PositiveDefinite n) :
    (fun p : Hermitian n × Hermitian n =>
      optimalDifferencePair p - optimalDifferenceTangent A (p.1 - p.2))
      =o[𝓝 (⟨A.val, A.property.isHermitian⟩,
              ⟨A.val, A.property.isHermitian⟩)]
        (fun p : Hermitian n × Hermitian n =>
          p - (⟨A.val, A.property.isHermitian⟩,
               ⟨A.val, A.property.isHermitian⟩)) := by
  let a : Hermitian n := ⟨A.val, A.property.isHermitian⟩
  let D := fderiv ℝ (optimalDifferencePair (n := n)) (a, a)
  have hf := (differentiableAt_optimalDifferencePair A A).hasFDerivAt
  have hl := hf.isLittleO
  have hfun : (fun p : Hermitian n × Hermitian n =>
      optimalDifferencePair p - optimalDifferenceTangent A (p.1 - p.2)) =
      (fun p => optimalDifferencePair p - optimalDifferencePair (a, a) -
        D (p - (a, a))) := by
    funext p
    rw [show optimalDifferencePair (a, a) = 0 from
      optimalDifferencePair_diagonal_zero A]
    simp only [sub_zero]
    have hd := optimalDifferencePair_fderiv_eq_tangent A (p.1 - a) (p.2 - a)
    have he : p - (a, a) = (p.1 - a, p.2 - a) := rfl
    rw [he, hd]
    congr 1
    abel_nf
  rw [hfun]
  exact hl

/-- At a positive definite base point, the derivative of the fixed-base
optimal lift is injective. The Gram map is a local left inverse. -/
theorem optimalLiftHermitian_fderiv_injective (A : PositiveDefinite n) :
    Function.Injective
      (fderiv ℝ (optimalLiftHermitian A)
        (⟨A.val, A.property.isHermitian⟩ : Hermitian n)) := by
  let a : Hermitian n := ⟨A.val, A.property.isHermitian⟩
  let T := optimalLiftHermitian A
  let L := fderiv ℝ T a
  have hT : HasFDerivAt T L a :=
    (differentiableAt_optimalLiftHermitian A A).hasFDerivAt
  have hG : DifferentiableAt ℝ gram (T a) := by
    have h₁ : DifferentiableAt ℝ (fun S : Mat n => S) (T a) :=
      differentiableAt_id
    simpa only [gram] using h₁.mul h₁.star
  have hcomp : HasFDerivAt (fun X : Hermitian n => gram (T X))
      ((fderiv ℝ gram (T a)).comp L) a := by
    simpa only [Function.comp_def] using
      (HasFDerivAt.comp (f := T) a hG.hasFDerivAt hT)
  have hpd := hermitianPosDef_mem_nhds a A.property
  have hev : (fun X : Hermitian n => gram (T X)) =ᶠ[𝓝 a]
      (fun X : Hermitian n => X.val) := by
    filter_upwards [hpd] with X hX
    let P : PositiveDefinite n := ⟨X.val, hX⟩
    change gram (optimalLift A P) = P.val
    exact optimalLift_gram A P
  have hinc : HasFDerivAt (fun X : Hermitian n => X.val)
      (hermitianInclusion n) a := (hermitianInclusion n).hasFDerivAt
  have hcomp' : HasFDerivAt (fun X : Hermitian n => X.val)
      ((fderiv ℝ gram (T a)).comp L) a :=
    hcomp.congr_of_eventuallyEq hev.symm
  have hsmul : ContinuousSMul ℝ (Hermitian n) := inferInstance
  have hsmulMat : ContinuousSMul ℝ (Mat n) := inferInstance
  have heq : (fderiv ℝ gram (T a)).comp L = hermitianInclusion n :=
    @HasFDerivAt.unique ℝ _ (Hermitian n) _ _ _ _ hsmul
      (Mat n) _ _ _ _ hsmulMat _ _ _ _ _ hcomp' hinc
  intro H K hHK
  have h := congrArg (fun M : Hermitian n →L[ℝ] Mat n => M (H - K)) heq
  have hz : L (H - K) = 0 := by
    rw [map_sub, hHK, sub_self]
  simp only [ContinuousLinearMap.comp_apply, hz, map_zero] at h
  have hv : (H - K).val = 0 := by
    simpa only [hermitianInclusion] using h.symm
  exact sub_eq_zero.mp (Subtype.ext hv)

/-- The tangent map from the two-point expansion equals the derivative of
the fixed-base optimal lift. -/
theorem optimalDifferenceTangent_eq_fixed_fderiv (A : PositiveDefinite n) :
    optimalDifferenceTangent A =
      fderiv ℝ (optimalLiftHermitian A)
        (⟨A.val, A.property.isHermitian⟩ : Hermitian n) := by
  let a : Hermitian n := ⟨A.val, A.property.isHermitian⟩
  let S := matrixSqrt A.val
  let T := optimalLiftHermitian A
  let D := fderiv ℝ (optimalDifferencePair (n := n)) (a, a)
  let L := fderiv ℝ T a
  have hf : HasFDerivAt (optimalDifferencePair (n := n)) D (a, a) :=
    (differentiableAt_optimalDifferencePair A A).hasFDerivAt
  have hi : HasFDerivAt (fun X : Hermitian n => (a, X))
      ((0 : Hermitian n →L[ℝ] Hermitian n).prod
        (ContinuousLinearMap.id ℝ (Hermitian n))) a :=
    (hasFDerivAt_const (𝕜 := ℝ) a a).prodMk (hasFDerivAt_id a)
  have hcomp : HasFDerivAt (fun X : Hermitian n => optimalDifferencePair (a, X))
      (D.comp ((0 : Hermitian n →L[ℝ] Hermitian n).prod
        (ContinuousLinearMap.id ℝ (Hermitian n)))) a := by
    simpa only [Function.comp_def] using
      (HasFDerivAt.comp (f := fun X : Hermitian n => (a, X)) a hf hi)
  have hT : HasFDerivAt T L a :=
    (differentiableAt_optimalLiftHermitian A A).hasFDerivAt
  have hright : HasFDerivAt (fun X : Hermitian n => S - T X)
      ((0 : Hermitian n →L[ℝ] Mat n) - L) a := by
    have ht := (hasFDerivAt_const (𝕜 := ℝ) S a).sub hT
    have hfun : ((fun _ : Hermitian n => S) - T) =
        (fun X : Hermitian n => S - T X) := by
      funext X
      rfl
    rw [hfun] at ht
    exact ht
  have hfun : (fun X : Hermitian n => optimalDifferencePair (a, X)) =
      (fun X : Hermitian n => S - T X) := rfl
  rw [hfun] at hcomp
  have hsmul : ContinuousSMul ℝ (Hermitian n) := inferInstance
  have hsmulMat : ContinuousSMul ℝ (Mat n) := inferInstance
  have heq : D.comp ((0 : Hermitian n →L[ℝ] Hermitian n).prod
        (ContinuousLinearMap.id ℝ (Hermitian n))) =
        (0 : Hermitian n →L[ℝ] Mat n) - L :=
    @HasFDerivAt.unique ℝ _ (Hermitian n) _ _ _ _ hsmul
      (Mat n) _ _ _ _ hsmulMat _ _ _ _ _ hcomp hright
  apply ContinuousLinearMap.ext
  intro H
  have h := congrArg (fun M : Hermitian n →L[ℝ] Mat n => M H) heq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.sub_apply] at h
  rw [optimalDifferencePair_fderiv_eq_tangent A 0 H] at h
  have h' : (optimalDifferenceTangent A) H = L H := by
    exact neg_inj.mp (by simpa only [zero_sub, map_neg] using h)
  exact h'

theorem optimalDifferenceTangent_injective (A : PositiveDefinite n) :
    Function.Injective (optimalDifferenceTangent A) := by
  rw [optimalDifferenceTangent_eq_fixed_fderiv]
  exact optimalLiftHermitian_fderiv_injective A

#print axioms differentiableAt_optimalDifferencePair
#print axioms distance_eq_norm_optimalDifferencePair
#print axioms optimalDifferencePair_fderiv_diagonal_zero
#print axioms optimalDifferencePair_tangent_littleO
#print axioms optimalLiftHermitian_fderiv_injective
#print axioms optimalDifferenceTangent_injective

end Bures

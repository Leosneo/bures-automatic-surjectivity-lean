import BuresCoordinatesCriterion
import HermitianFiniteDimension
import HermitianSylvesterSmooth
import BuresFrobenius
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The first variation of the literal squared Bures distance in Hermitian
coordinates, expressed solely using the two Sylvester inverses arising from
the matrix square roots. -/

noncomputable section
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContinuousLinearMap RightActions
namespace Bures

local instance (n : ℕ) : CStarAlgebra (Mat n) where

/-- The derivative of the Hermitian sandwich `X ↦ √X B √X`. -/
def sandwichDerivative (B A : Hermitian n) (hA : A.val.PosDef) :
    Hermitian n →L[ℝ] Hermitian n :=
  let S := hermitianSqrt A
  let dS := ((hermitianSylvesterEquiv S (by
    exact (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg A.val)).posDef_iff_isUnit.mpr
      (hA.isStrictlyPositive.sqrt).2)).symm : Hermitian n →L[ℝ] Hermitian n)
  (selfAdjointPartL ℝ (Mat n)).comp
    (((S.val * B.val) •> (hermitianInclusion n).comp dS) +
      (((hermitianInclusion n).comp dS) <• (B.val * S.val)))

/-- Real trace of a Hermitian matrix, as a continuous linear map. -/
def hermitianTrace (n : ℕ) : Hermitian n →L[ℝ] ℝ :=
  (traceRealCLM n).comp (hermitianInclusion n)

/-- A closed-form continuous-linear first variation of squared Bures distance.
It applies at any pair of positive definite matrices. -/
def squaredBuresDerivative (B A : Hermitian n) (hB : B.val.PosDef)
    (hA : A.val.PosDef) : Hermitian n →L[ℝ] ℝ :=
  let P := hermitianSandwich B A
  let dRoot := ((hermitianSylvesterEquiv (hermitianSqrt P)
    (by
      exact (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg P.val)).posDef_iff_isUnit.mpr
        ((hermitianSandwich_posDef B A hB hA).isStrictlyPositive.sqrt).2)).symm :
      Hermitian n →L[ℝ] Hermitian n)
  hermitianTrace n - (2 : ℝ) •> ((hermitianTrace n).comp
    (dRoot.comp (sandwichDerivative B A hA)))

theorem hasFDerivAt_hermitianSandwich (B A : Hermitian n)
    (hA : A.val.PosDef) :
    HasFDerivAt (hermitianSandwich B) (sandwichDerivative B A hA) A := by
  let S := hermitianSqrt A
  let dS := ((hermitianSylvesterEquiv S (by
    exact (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg A.val)).posDef_iff_isUnit.mpr
      (hA.isStrictlyPositive.sqrt).2)).symm : Hermitian n →L[ℝ] Hermitian n)
  have hs : HasFDerivAt (hermitianSqrt (n := n)) dS A :=
    hasFDerivAt_hermitianSqrt A hA
  have hv : HasFDerivAt
      (fun X : Hermitian n => (hermitianSqrt X).val)
      ((hermitianInclusion n).comp dS) A :=
    (hermitianInclusion n).hasFDerivAt.comp A hs
  have hm := (hv.mul_const' B.val).mul' hv
  have hp := (selfAdjointPartL ℝ (Mat n)).hasFDerivAt.comp A hm
  change HasFDerivAt (fun X : Hermitian n =>
    (selfAdjointPartL ℝ (Mat n))
      ((hermitianSqrt X).val * B.val * (hermitianSqrt X).val)) _ A at hp
  have hfun : (fun X : Hermitian n =>
    (selfAdjointPartL ℝ (Mat n))
      ((hermitianSqrt X).val * B.val * (hermitianSqrt X).val)) =
      hermitianSandwich B := by
    funext X
    exact (IsSelfAdjoint.selfAdjointPart_apply ℝ
      (show IsSelfAdjoint
        ((hermitianSqrt X).val * B.val * (hermitianSqrt X).val) by
        change star ((hermitianSqrt X).val * B.val * (hermitianSqrt X).val) = _
        simp [star_mul, mul_assoc]))
  rw [hfun] at hp
  have hright : ((hermitianInclusion n).comp dS) <• B.val <• S.val =
      ((hermitianInclusion n).comp dS) <• (B.val * S.val) := by
    ext H i j
    change (((dS H).val * B.val) * S.val) i j =
      ((dS H).val * (B.val * S.val)) i j
    rw [mul_assoc]
  change HasFDerivAt (hermitianSandwich B)
    ((selfAdjointPartL ℝ (Mat n)).comp
      (((S.val * B.val) •> (hermitianInclusion n).comp dS) +
        (((hermitianInclusion n).comp dS) <• (B.val * S.val)))) A
  rw [← hright]
  exact hp

/-- The displayed continuous linear map is the actual Fréchet derivative. -/
theorem hasFDerivAt_squaredBuresHermitian (B A : Hermitian n)
    (hB : B.val.PosDef) (hA : A.val.PosDef) :
    HasFDerivAt (squaredBuresHermitian B)
      (squaredBuresDerivative B A hB hA) A := by
  let P := hermitianSandwich B A
  have hP : P.val.PosDef := hermitianSandwich_posDef B A hB hA
  let dRoot := ((hermitianSylvesterEquiv (hermitianSqrt P)
    (by
      exact (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg P.val)).posDef_iff_isUnit.mpr
        (hP.isStrictlyPositive.sqrt).2)).symm : Hermitian n →L[ℝ] Hermitian n)
  have hr : HasFDerivAt (hermitianSqrt (n := n)) dRoot P :=
    hasFDerivAt_hermitianSqrt P hP
  have hs : HasFDerivAt (hermitianSandwich B)
      (sandwichDerivative B A hA) A := hasFDerivAt_hermitianSandwich B A hA
  have ht : HasFDerivAt (fun X : Hermitian n => tr X.val)
      (hermitianTrace n) A := (hermitianTrace n).hasFDerivAt
  have houter : HasFDerivAt
      (fun X : Hermitian n => tr (hermitianSqrt (hermitianSandwich B X)).val)
      ((hermitianTrace n).comp (dRoot.comp (sandwichDerivative B A hA))) A := by
    exact (hermitianTrace n).hasFDerivAt.comp A (hr.comp A hs)
  have hall := (ht.add_const (tr B.val)).sub (houter.const_mul 2)
  change HasFDerivAt (squaredBuresHermitian B) _ A at hall
  change HasFDerivAt (squaredBuresHermitian B)
    (hermitianTrace n - (2 : ℝ) •> ((hermitianTrace n).comp
      (dRoot.comp (sandwichDerivative B A hA)))) A
  exact hall

/-- The trace of the inverse Sylvester derivative of `S²` is half the
inverse-weighted trace. This is the matrix-sqrt trace variation used by
distance coordinates. -/
theorem trace_hermitianSylvester_inverse (S H : Hermitian n)
    (hS : S.val.PosDef) :
    2 * tr ((hermitianSylvesterEquiv S hS).symm H).val =
      tr (S.val⁻¹ * H.val) := by
  let Q := (hermitianSylvesterEquiv S hS).symm H
  have hQ : Q.val * S.val + S.val * Q.val = H.val := by
    have h := (hermitianSylvesterEquiv S hS).apply_symm_apply H
    exact congrArg Subtype.val h
  have hdS := (Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit
  have hSi := Matrix.mul_nonsing_inv S.val hdS
  have hiS := Matrix.nonsing_inv_mul S.val hdS
  have h1 : tr (S.val⁻¹ * (Q.val * S.val)) = tr Q.val := by
    rw [← mul_assoc, tr_mul_comm (S.val⁻¹ * Q.val) S.val,
      ← mul_assoc, hSi, one_mul]
  have h2 : tr (S.val⁻¹ * (S.val * Q.val)) = tr Q.val := by
    rw [← mul_assoc, hiS, one_mul]
  calc
    2 * tr Q.val = tr Q.val + tr Q.val := by ring
    _ = tr (S.val⁻¹ * (Q.val * S.val)) +
          tr (S.val⁻¹ * (S.val * Q.val)) := by
      rw [h1, h2]
    _ = tr (S.val⁻¹ * H.val) := by rw [← tr_add, ← mul_add, hQ]

/-- Algebraic form of the sandwich derivative in matrix entries. -/
theorem sandwichDerivative_val (B A H : Hermitian n)
    (hA : A.val.PosDef) :
    let S := hermitianSqrt A
    let D := (hermitianSylvesterEquiv S (by
      exact (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg A.val)).posDef_iff_isUnit.mpr
        (hA.isStrictlyPositive.sqrt).2)).symm H
    (sandwichDerivative B A hA H).val =
      D.val * B.val * S.val + S.val * B.val * D.val := by
  dsimp only
  let S := hermitianSqrt A
  let D := (hermitianSylvesterEquiv S (by
    exact (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg A.val)).posDef_iff_isUnit.mpr
      (hA.isStrictlyPositive.sqrt).2)).symm H
  have hHerm : IsSelfAdjoint
      (D.val * B.val * S.val + S.val * B.val * D.val) := by
    change star (D.val * B.val * S.val + S.val * B.val * D.val) = _
    simp [star_add, star_mul, mul_assoc, add_comm]
  have hp := IsSelfAdjoint.selfAdjointPart_apply ℝ hHerm
  calc
    (sandwichDerivative B A hA H).val =
        ((selfAdjointPartL ℝ (Mat n))
          (D.val * B.val * S.val + S.val * B.val * D.val)).val := by
      simp only [sandwichDerivative, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
      change ((selfAdjointPartL ℝ (Mat n))
        (S.val * B.val * D.val + D.val * (B.val * S.val))).val =
        ((selfAdjointPartL ℝ (Mat n))
          (D.val * B.val * S.val + S.val * B.val * D.val)).val
      rw [← mul_assoc, add_comm]
    _ = _ := congrArg Subtype.val hp

/-- Matrix algebra underlying the Bures first-variation formula. -/
theorem trace_transport_algebra (S R B D H : Mat n)
    (hSu : IsUnit S) (hRu : IsUnit R)
    (hR2 : R * R = S * B * S)
    (hH : D * S + S * D = H) :
    tr (R⁻¹ * (D * B * S + S * B * D)) =
      tr ((S⁻¹ * R * S⁻¹) * H) := by
  have hdS := (Matrix.isUnit_iff_isUnit_det _).mp hSu
  have hdR := (Matrix.isUnit_iff_isUnit_det _).mp hRu
  have hSi := Matrix.mul_nonsing_inv S hdS
  have hiS := Matrix.nonsing_inv_mul S hdS
  have hRi := Matrix.mul_nonsing_inv R hdR
  have hiR := Matrix.nonsing_inv_mul R hdR
  have hBS : B * S = S⁻¹ * (R * R) := by
    calc
      B * S = (S⁻¹ * S) * (B * S) := by rw [hiS, one_mul]
      _ = S⁻¹ * (S * B * S) := by noncomm_ring
      _ = S⁻¹ * (R * R) := by rw [← hR2]
  have hSB : S * B = (R * R) * S⁻¹ := by
    calc
      S * B = (S * B) * (S * S⁻¹) := by rw [hSi, mul_one]
      _ = (S * B * S) * S⁻¹ := by noncomm_ring
      _ = (R * R) * S⁻¹ := by rw [← hR2]
  have hL1 : tr (R⁻¹ * (D * B * S)) = tr (R * D * S⁻¹) := by
    calc
      tr (R⁻¹ * (D * B * S)) = tr (R⁻¹ * D * S⁻¹ * (R * R)) := by
        rw [mul_assoc D B S, hBS]
        congr 1
        noncomm_ring
      _ = tr ((R * R) * (R⁻¹ * D * S⁻¹)) := tr_mul_comm _ _
      _ = tr (R * D * S⁻¹) := by
        congr 1
        calc
          (R * R) * (R⁻¹ * D * S⁻¹) = R * (R * R⁻¹) * D * S⁻¹ := by noncomm_ring
          _ = R * D * S⁻¹ := by rw [hRi, mul_one]
  have hL2 : tr (R⁻¹ * (S * B * D)) = tr (R * S⁻¹ * D) := by
    rw [hSB]
    congr 1
    calc
      R⁻¹ * ((R * R) * S⁻¹ * D) = (R⁻¹ * R) * R * S⁻¹ * D := by noncomm_ring
      _ = R * S⁻¹ * D := by rw [hiR, one_mul]
  have hT1 : tr ((S⁻¹ * R * S⁻¹) * (D * S)) = tr (R * S⁻¹ * D) := by
    calc
      tr ((S⁻¹ * R * S⁻¹) * (D * S)) =
          tr ((S⁻¹ * R * S⁻¹ * D) * S) := by congr 1; noncomm_ring
      _ = tr (S * (S⁻¹ * R * S⁻¹ * D)) := tr_mul_comm _ _
      _ = tr (R * S⁻¹ * D) := by
        congr 1
        calc
          S * (S⁻¹ * R * S⁻¹ * D) = (S * S⁻¹) * R * S⁻¹ * D := by noncomm_ring
          _ = R * S⁻¹ * D := by rw [hSi, one_mul]
  have hT2 : tr ((S⁻¹ * R * S⁻¹) * (S * D)) = tr (R * D * S⁻¹) := by
    calc
      tr ((S⁻¹ * R * S⁻¹) * (S * D)) = tr (S⁻¹ * (R * D)) := by
        congr 1
        calc
          (S⁻¹ * R * S⁻¹) * (S * D) = S⁻¹ * R * (S⁻¹ * S) * D := by noncomm_ring
          _ = S⁻¹ * (R * D) := by rw [hiS]; noncomm_ring
      _ = tr (R * D * S⁻¹) := by rw [tr_mul_comm]
  rw [← hH, mul_add, tr_add, hL1, hL2, mul_add, tr_add, hT1, hT2]
  exact add_comm _ _

/-- The familiar first variation `Tr((I-T)H)` follows from the literal
fidelity formula. No metric or quotient geometry is assumed here. -/
theorem squaredBuresDerivative_apply (B A H : Hermitian n)
    (hB : B.val.PosDef) (hA : A.val.PosDef) :
    (squaredBuresDerivative B A hB hA) H =
      tr H.val - tr (((hermitianSqrt A).val⁻¹ *
        (hermitianSqrt (hermitianSandwich B A)).val *
        (hermitianSqrt A).val⁻¹) * H.val) := by
  let S := hermitianSqrt A
  let P := hermitianSandwich B A
  let R := hermitianSqrt P
  let D := (hermitianSylvesterEquiv S (by
    exact (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg A.val)).posDef_iff_isUnit.mpr
      (hA.isStrictlyPositive.sqrt).2)).symm H
  have hS : S.val.PosDef :=
    (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg A.val)).posDef_iff_isUnit.mpr
      (hA.isStrictlyPositive.sqrt).2
  have hP : P.val.PosDef := hermitianSandwich_posDef B A hB hA
  have hR : R.val.PosDef :=
    (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg P.val)).posDef_iff_isUnit.mpr
      (hP.isStrictlyPositive.sqrt).2
  have hR2 : R.val * R.val = S.val * B.val * S.val :=
    matrixSqrt_mul_self hP.posSemidef
  have hH : D.val * S.val + S.val * D.val = H.val := by
    have h := (hermitianSylvesterEquiv S hS).apply_symm_apply H
    exact congrArg Subtype.val h
  have hder : (sandwichDerivative B A hA H).val =
      D.val * B.val * S.val + S.val * B.val * D.val :=
    sandwichDerivative_val B A H hA
  have htrace : 2 * tr ((hermitianSylvesterEquiv R hR).symm
      (sandwichDerivative B A hA H)).val =
      tr ((S.val⁻¹ * R.val * S.val⁻¹) * H.val) := by
    calc
      _ = tr (R.val⁻¹ * (sandwichDerivative B A hA H).val) :=
        trace_hermitianSylvester_inverse R _ hR
      _ = tr (R.val⁻¹ *
          (D.val * B.val * S.val + S.val * B.val * D.val)) := by rw [hder]
      _ = tr ((S.val⁻¹ * R.val * S.val⁻¹) * H.val) :=
        trace_transport_algebra S.val R.val B.val D.val H.val
          hS.isUnit hR.isUnit hR2 hH
  change tr H.val - 2 * tr ((hermitianSylvesterEquiv R hR).symm
      (sandwichDerivative B A hA H)).val =
    tr H.val - tr ((S.val⁻¹ * R.val * S.val⁻¹) * H.val)
  rw [htrace]

/-- For a congruence anchor `B = T A T`, the optimal-transport matrix in the
first-variation formula is exactly `T`. -/
theorem transport_eq_of_congruence (B A T : Hermitian n)
    (hA : A.val.PosDef) (hT : T.val.PosDef)
    (hB : B.val = T.val * A.val * T.val) :
    (hermitianSqrt A).val⁻¹ *
      (hermitianSqrt (hermitianSandwich B A)).val *
      (hermitianSqrt A).val⁻¹ = T.val := by
  let S := hermitianSqrt A
  let C := hermitianSandwich T A
  have hC : C.val.PosDef := hermitianSandwich_posDef T A hT hA
  have hSS : S.val * S.val = A.val := matrixSqrt_mul_self hA.posSemidef
  have hsq : C.val * C.val = S.val * B.val * S.val := by
    calc
      C.val * C.val = (S.val * T.val * S.val) *
          (S.val * T.val * S.val) := rfl
      _ = S.val * (T.val * (S.val * S.val) * T.val) * S.val := by
        noncomm_ring
      _ = S.val * (T.val * A.val * T.val) * S.val := by rw [hSS]
      _ = S.val * B.val * S.val := by rw [← hB]
  have hroot : (hermitianSqrt (hermitianSandwich B A)).val = C.val := by
    change matrixSqrt (S.val * B.val * S.val) = C.val
    rw [← hsq]
    exact matrixSqrt_unique hC.posSemidef rfl
  have hdS := (Matrix.isUnit_iff_isUnit_det _).mp
    ((Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg A.val)).posDef_iff_isUnit.mpr
      (hA.isStrictlyPositive.sqrt).2).isUnit
  have hSi := Matrix.mul_nonsing_inv S.val hdS
  have hiS := Matrix.nonsing_inv_mul S.val hdS
  rw [hroot]
  change S.val⁻¹ * (S.val * T.val * S.val) * S.val⁻¹ = T.val
  calc
    _ = (S.val⁻¹ * S.val) * T.val * (S.val * S.val⁻¹) := by
      noncomm_ring
    _ = T.val := by rw [hiS, hSi, one_mul, mul_one]

theorem squaredBuresDerivative_congruence (B A T H : Hermitian n)
    (hB : B.val.PosDef) (hA : A.val.PosDef) (hT : T.val.PosDef)
    (hBA : B.val = T.val * A.val * T.val) :
    (squaredBuresDerivative B A hB hA) H =
      tr H.val - tr (T.val * H.val) := by
  rw [squaredBuresDerivative_apply B A H hB hA,
    transport_eq_of_congruence B A T hA hT hBA]

section FrobeniusPairing
open scoped Matrix.Norms.Frobenius

/-- The real trace pairing on Hermitian matrices is nondegenerate. -/
theorem trace_pairing_nondegenerate (H : Hermitian n)
    (h : ∀ K : Hermitian n, tr (K.val * H.val) = 0) : H = 0 := by
  have hh : H.val.conjTranspose = H.val := by
    simpa only [Matrix.star_eq_conjTranspose] using H.property
  have hnorm : ‖H.val‖ ^ 2 = 0 := by
    rw [frobenius_sq_eq_tr_gram, hh]
    exact h H
  have hz : H.val = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg H.val])
  exact Subtype.ext hz

end FrobeniusPairing

/-- The trace pairing, continuous and real-linear in the first argument. -/
def tracePairingCLM (H : Hermitian n) : Hermitian n →L[ℝ] ℝ :=
  (traceRealCLM n).comp (H.val •> hermitianInclusion n)

@[simp] theorem tracePairingCLM_apply (K H : Hermitian n) :
    tracePairingCLM H K = tr (K.val * H.val) := by
  change tr (H.val * K.val) = tr (K.val * H.val)
  exact tr_mul_comm _ _

/-- Trace pairing against a basis gives injective coordinates. -/
theorem trace_basis_coordinates_injective {ι : Type*}
    (b : Module.Basis ι ℝ (Hermitian n)) (H : Hermitian n)
    (h : ∀ i, tr ((b i).val * H.val) = 0) : H = 0 := by
  have hz : (tracePairingCLM H).toLinearMap = 0 := by
    apply b.ext
    intro i
    simpa only [ContinuousLinearMap.coe_coe, tracePairingCLM_apply,
      LinearMap.zero_apply] using h i
  apply trace_pairing_nondegenerate H
  intro K
  have hK := congrArg (fun f : Hermitian n →ₗ[ℝ] ℝ => f K) hz
  simpa only [ContinuousLinearMap.coe_coe, tracePairingCLM_apply,
    LinearMap.zero_apply] using hK

/-- A Hermitian perturbation of the identity through a matrix scalar action. -/
def transportShift (K : Hermitian n) (t : ℝ) : Hermitian n :=
  (⟨1, IsSelfAdjoint.one (Mat n)⟩ : Hermitian n) + t • K

theorem continuous_transportShift (K : Hermitian n) :
    Continuous (transportShift K) := by
  exact continuous_const.add (continuous_id.smul continuous_const)

/-- A small positive perturbation of identity in any Hermitian direction. -/
theorem exists_posDef_transport_shift (K : Hermitian n) :
    ∃ t : ℝ, 0 < t ∧ (transportShift K t).val.PosDef := by
  have h0 : transportShift K 0 = ⟨1, IsSelfAdjoint.one (Mat n)⟩ := by
    change (⟨1, IsSelfAdjoint.one (Mat n)⟩ : Hermitian n) + (0 : ℝ) • K = _
    have hz : (0 : ℝ) • K = 0 := by
      apply Subtype.ext
      change (0 : ℝ) • K.val = 0
      exact zero_smul ℝ K.val
    rw [hz, add_zero]
  have hmem : {t : ℝ | (transportShift K t).val.PosDef} ∈ nhds (0 : ℝ) := by
    have hI : {X : Hermitian n | X.val.PosDef} ∈
        nhds (transportShift K 0) := by
      rw [h0]
      exact hermitianPosDef_mem_nhds _ Matrix.PosDef.one
    exact (continuous_transportShift K).continuousAt.eventually hI
  have hevent : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      0 < t ∧ (transportShift K t).val.PosDef := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hmem]
      with t ht hp
    exact ⟨ht, hp⟩
  obtain ⟨t, ht, hp⟩ := hevent.exists
  exact ⟨t, ht, hp⟩

/-- Congruence anchors preserve Hermitian symmetry and, for positive T,
positive definiteness. -/
def congruenceAnchor (A T : Hermitian n) : Hermitian n :=
  ⟨T.val * A.val * T.val, by
    change star (T.val * A.val * T.val) = _
    simp [star_mul, mul_assoc]⟩

theorem congruenceAnchor_posDef (A T : Hermitian n)
    (hA : A.val.PosDef) (hT : T.val.PosDef) :
    (congruenceAnchor A T).val.PosDef := by
  have hinj : Function.Injective T.val.vecMul :=
    Matrix.vecMul_injective_iff_isUnit.mpr hT.isUnit
  have hp := hA.mul_mul_conjTranspose_same hinj
  change (T.val * A.val * T.val).PosDef
  rw [hT.isHermitian.eq] at hp
  exact hp

/-- Each shifted-congruence anchor has a scalar multiple of a trace-basis
functional as its exact squared-distance derivative. -/
theorem squaredBuresDerivative_shift (A K H : Hermitian n)
    (hA : A.val.PosDef) (t : ℝ)
    (hT : (transportShift K t).val.PosDef) :
    let T := transportShift K t
    let B := congruenceAnchor A T
    (squaredBuresDerivative B A
      (congruenceAnchor_posDef A T hA hT) hA) H =
      -t * tr (K.val * H.val) := by
  dsimp only
  let T := transportShift K t
  let B := congruenceAnchor A T
  have hB : B.val.PosDef := congruenceAnchor_posDef A T hA hT
  rw [squaredBuresDerivative_congruence B A T H hB hA hT rfl]
  change tr H.val - tr (((1 : Mat n) + t • K.val) * H.val) = _
  rw [add_mul, one_mul, tr_add]
  have hs : (t • K.val) * H.val = t • (K.val * H.val) := by
    rw [smul_mul_assoc]
  rw [hs, tr_smul]
  ring

/-- Jacobian of finitely many literal squared-distance functions at `A`,
whose anchors are congruence shifts along a real Hermitian basis. -/
def shiftedAnchorJacobian {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ (Hermitian n)) (A : Hermitian n)
    (hA : A.val.PosDef) (t : ι → ℝ)
    (hT : ∀ i, (transportShift (b i) (t i)).val.PosDef) :
    Hermitian n →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi (fun i =>
    let T := transportShift (b i) (t i)
    let B := congruenceAnchor A T
    squaredBuresDerivative B A
      (congruenceAnchor_posDef A T hA (hT i)) hA)

/-- The distance-coordinate Jacobian is injective for every choice of
nonzero positive shifts along a Hermitian basis. -/
theorem shiftedAnchorJacobian_injective {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ (Hermitian n)) (A : Hermitian n)
    (hA : A.val.PosDef) (t : ι → ℝ)
    (ht : ∀ i, 0 < t i)
    (hT : ∀ i, (transportShift (b i) (t i)).val.PosDef) :
    Function.Injective (shiftedAnchorJacobian b A hA t hT) := by
  have hzero : ∀ H : Hermitian n,
      shiftedAnchorJacobian b A hA t hT H = 0 → H = 0 := by
    intro H hH
    apply trace_basis_coordinates_injective b H
    intro i
    have hi := congrFun hH i
    change (squaredBuresDerivative
      (congruenceAnchor A (transportShift (b i) (t i))) A
      (congruenceAnchor_posDef A (transportShift (b i) (t i)) hA (hT i)) hA) H = 0 at hi
    rw [squaredBuresDerivative_shift A (b i) H hA (t i) (hT i)] at hi
    have hne : -(t i) ≠ 0 := neg_ne_zero.mpr (ne_of_gt (ht i))
    exact (mul_eq_zero.mp hi).resolve_left hne
  intro X Y hXY
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub, hXY, sub_self]

/-- At every positive definite point, a finite basis-indexed collection of
positive congruence anchors has an injective literal distance-coordinate
Jacobian. -/
theorem exists_injective_anchor_jacobian {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ (Hermitian n)) (A : Hermitian n)
    (hA : A.val.PosDef) :
    ∃ (t : ι → ℝ) (hT : ∀ i,
        (transportShift (b i) (t i)).val.PosDef),
      (∀ i, 0 < t i) ∧
      Function.Injective (shiftedAnchorJacobian b A hA t hT) := by
  classical
  choose t ht hT using fun i => exists_posDef_transport_shift (b i)
  exact ⟨t, hT, ht, shiftedAnchorJacobian_injective b A hA t ht hT⟩

/-- The displayed Jacobian differentiates the actual finite family of
literal squared Bures distance functions. -/
theorem hasFDerivAt_shifted_anchor_coordinates {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ (Hermitian n)) (A : Hermitian n)
    (hA : A.val.PosDef) (t : ι → ℝ)
    (hT : ∀ i, (transportShift (b i) (t i)).val.PosDef) :
    HasFDerivAt
      (anchoredSquaredDistances (fun i =>
        congruenceAnchor A (transportShift (b i) (t i))))
      (shiftedAnchorJacobian b A hA t hT) A := by
  apply hasFDerivAt_pi.mpr
  intro i
  exact hasFDerivAt_squaredBuresHermitian
    (congruenceAnchor A (transportShift (b i) (t i))) A
    (congruenceAnchor_posDef A _ hA (hT i)) hA

/-- The finite literal distance-coordinate Jacobian is a linear bijection. -/
theorem shiftedAnchorJacobian_bijective {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ (Hermitian n)) (A : Hermitian n)
    (hA : A.val.PosDef) (t : ι → ℝ)
    (ht : ∀ i, 0 < t i)
    (hT : ∀ i, (transportShift (b i) (t i)).val.PosDef) :
    Function.Bijective (shiftedAnchorJacobian b A hA t hT) := by
  have hdim : Module.finrank ℝ (Hermitian n) = Module.finrank ℝ (ι → ℝ) := by
    rw [Module.finrank_eq_card_basis b, Module.finrank_fintype_fun_eq_card]
  have hinj := shiftedAnchorJacobian_injective b A hA t ht hT
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩

/-- Every positive definite Hermitian point admits finitely many
positive-definite Bures anchors whose actual squared-distance coordinate map
has a bijective Fréchet derivative there. -/
theorem exists_bijective_anchor_jacobian {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ (Hermitian n)) (A : Hermitian n)
    (hA : A.val.PosDef) :
    ∃ (t : ι → ℝ) (hT : ∀ i,
        (transportShift (b i) (t i)).val.PosDef),
      Function.Bijective (shiftedAnchorJacobian b A hA t hT) ∧
      HasFDerivAt
        (anchoredSquaredDistances (fun i =>
          congruenceAnchor A (transportShift (b i) (t i))))
        (shiftedAnchorJacobian b A hA t hT) A := by
  classical
  choose t ht hT using fun i => exists_posDef_transport_shift (b i)
  exact ⟨t, hT, shiftedAnchorJacobian_bijective b A hA t ht hT,
    hasFDerivAt_shifted_anchor_coordinates b A hA t hT⟩

#print axioms hasFDerivAt_hermitianSandwich
#print axioms hasFDerivAt_squaredBuresHermitian
#print axioms squaredBuresDerivative_apply
#print axioms exists_bijective_anchor_jacobian

end Bures

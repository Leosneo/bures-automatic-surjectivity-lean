import Bures

/-! Algebraic replacement for the final invariance-of-domain argument.
These results concern the literal fidelity formula on positive semidefinite matrices.
They do not assume or prove trace preservation for a Bures isometric embedding. -/
noncomputable section
open scoped MatrixOrder ComplexOrder
open Matrix
namespace Bures

local instance (n : ℕ) :
    NonUnitalContinuousFunctionalCalculus ℝ (Mat n) IsSelfAdjoint :=
  ContinuousFunctionalCalculus.toNonUnital
local instance (n : ℕ) : NonnegSpectrumClass ℝ (Mat n) :=
  Matrix.instNonnegSpectrumClass

theorem tr_eq_zero_iff {A : Mat n} (hA : A.PosSemidef) : tr A = 0 ↔ A = 0 := by
  have him : (Matrix.trace A).im = 0 := (Complex.nonneg_iff.mp hA.trace_nonneg).2.symm
  rw [← hA.trace_eq_zero_iff]
  constructor
  · intro h
    exact Complex.ext h him
  · intro h
    simp [tr, h]

theorem matrixSqrt_eq_zero_iff {A : Mat n} (hA : A.PosSemidef) :
    matrixSqrt A = 0 ↔ A = 0 := by
  constructor
  · intro h
    simpa [h] using (matrixSqrt_mul_self hA).symm
  · intro h
    simp [matrixSqrt, h]

theorem fidelityRoot_eq_zero_iff_sandwich {A B : Mat n} (hB : B.PosSemidef) :
    fidelityRoot A B = 0 ↔ matrixSqrt A * B * matrixSqrt A = 0 := by
  have hS : (matrixSqrt A).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg A)
  have hM : (matrixSqrt A * B * matrixSqrt A).PosSemidef := by
    simpa only [hS.isHermitian.eq] using hB.mul_mul_conjTranspose_same (matrixSqrt A)
  exact (tr_eq_zero_iff (Matrix.nonneg_iff_posSemidef.mp
    (matrixSqrt_nonneg _))).trans (matrixSqrt_eq_zero_iff hM)

/-- The positive definite stratum is determined by absence of nonzero
positive semidefinite matrices having zero fidelity with the point. -/
theorem posDef_iff_fidelity_separates {A : Mat n} (hA : A.PosSemidef) :
    A.PosDef ↔ ∀ B : Mat n, B.PosSemidef → fidelityRoot A B = 0 → B = 0 := by
  constructor
  · intro hp B hB hf
    have hz := (fidelityRoot_eq_zero_iff_sandwich hB).mp hf
    have hu : IsUnit (matrixSqrt A) := (hp.isStrictlyPositive.sqrt).isUnit
    have h1 : matrixSqrt A * B = 0 := hu.mul_right_cancel (by simpa using hz)
    exact hu.mul_left_cancel (by simpa using h1)
  · intro h
    apply hA.posDef_iff_isUnit.mpr
    by_contra hu
    have hsu : ¬ IsUnit (matrixSqrt A) := by
      intro hs
      exact hu (matrixSqrt_mul_self hA ▸ hs.mul hs)
    obtain ⟨v, hv, hz⟩ : ∃ v : Fin n → ℂ, v ≠ 0 ∧ matrixSqrt A *ᵥ v = 0 := by
      obtain ⟨a, b, heq, hne⟩ := Function.not_injective_iff.mp
        (Matrix.mulVec_injective_iff_isUnit.not.mpr hsu)
      exact ⟨a - b, sub_ne_zero.mpr hne, by rw [Matrix.mulVec_sub, heq, sub_self]⟩
    have hB := Matrix.posSemidef_vecMulVec_self_star v
    have he := h (Matrix.vecMulVec v (star v)) hB
      ((fidelityRoot_eq_zero_iff_sandwich hB).mpr (by
        rw [Matrix.mul_vecMulVec, hz]
        simp))
    have hv0 : v = 0 := by simpa using he
    exact hv hv0

/-- A bijection of the semidefinite cone preserving zero and fidelity preserves
its positive definite stratum, without any topological argument. -/
theorem posDef_image_iff_of_fidelity_bijection
    (F : {A : Mat n // A.PosSemidef} → {A : Mat n // A.PosSemidef})
    (hF : Function.Bijective F)
    (hzero : F ⟨0, Matrix.PosSemidef.zero⟩ = ⟨0, Matrix.PosSemidef.zero⟩)
    (hf : ∀ A B, fidelityRoot (F A).val (F B).val = fidelityRoot A.val B.val)
    (A : {A : Mat n // A.PosSemidef}) : (F A).val.PosDef ↔ A.val.PosDef := by
  constructor
  · intro hFA
    apply (posDef_iff_fidelity_separates A.property).mpr
    intro B hB hAB
    have hFB : (F ⟨B, hB⟩).val = 0 :=
      (posDef_iff_fidelity_separates (F A).property).mp hFA _ (F ⟨B, hB⟩).property
        (by rw [hf]; exact hAB)
    have he : F ⟨B, hB⟩ = F ⟨0, Matrix.PosSemidef.zero⟩ := by
      rw [hzero]
      exact Subtype.ext hFB
    exact congrArg Subtype.val (hF.injective he)
  · intro hA
    apply (posDef_iff_fidelity_separates (F A).property).mpr
    intro B hB hAB
    obtain ⟨C, hC⟩ := hF.surjective ⟨B, hB⟩
    have hz : C.val = 0 := (posDef_iff_fidelity_separates A.property).mp hA _ C.property
      (by rw [← hf, hC]; exact hAB)
    have hC0 : C = ⟨0, Matrix.PosSemidef.zero⟩ := Subtype.ext hz
    have he := congrArg Subtype.val hC
    rw [hC0, hzero] at he
    exact he.symm

/-- Once a bijective fidelity-preserving semidefinite extension has been
constructed, its original positive-definite restriction is automatically onto. -/
theorem surjective_of_semidefinite_extension
    (F : PositiveDefinite n → PositiveDefinite n)
    (E : {A : Mat n // A.PosSemidef} → {A : Mat n // A.PosSemidef})
    (hE : Function.Bijective E)
    (hzero : E ⟨0, Matrix.PosSemidef.zero⟩ = ⟨0, Matrix.PosSemidef.zero⟩)
    (hf : ∀ A B, fidelityRoot (E A).val (E B).val = fidelityRoot A.val B.val)
    (hext : ∀ A : PositiveDefinite n,
      (E ⟨A.val, A.property.posSemidef⟩).val = (F A).val) :
    Function.Surjective F := by
  intro B
  obtain ⟨A, hA⟩ := hE.surjective ⟨B.val, B.property.posSemidef⟩
  have hp : A.val.PosDef :=
    (posDef_image_iff_of_fidelity_bijection E hE hzero hf A).mp (by
      rw [hA]
      exact B.property)
  refine ⟨⟨A.val, hp⟩, Subtype.ext ?_⟩
  rw [← hext]
  exact congrArg Subtype.val hA

#print axioms surjective_of_semidefinite_extension
#print axioms posDef_iff_fidelity_separates
#print axioms posDef_image_iff_of_fidelity_bijection
end Bures

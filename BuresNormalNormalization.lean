import BuresNormalForm
import BuresNormalBlowdown

/-! Normalize an affine Bures normal form by its homogeneous part. -/
noncomputable section
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator Topology
open Filter Matrix
namespace Bures
set_option backward.isDefEq.respectTransparency false

def normalDisplacement (Q : Hermitian n ≃ₗ[ℝ] Hermitian n) : Hermitian n :=
  Q.symm (⟨1, Matrix.isHermitian_one⟩ : Hermitian n) -
    (⟨1, Matrix.isHermitian_one⟩ : Hermitian n)

theorem normalDisplacement_factor (Q : Hermitian n ≃ₗ[ℝ] Hermitian n)
    (T : Hermitian n) :
    Q (T + normalDisplacement Q) =
      (⟨1, Matrix.isHermitian_one⟩ : Hermitian n) +
        Q (T - (⟨1, Matrix.isHermitian_one⟩ : Hermitian n)) := by
  simp only [normalDisplacement, map_add, map_sub, LinearEquiv.apply_symm_apply]
  abel

/-- Positivity of the affine chart and positivity of the inverse linear
part imply that the residual square-root translation is positive. -/
theorem normalDisplacement_posSemidef
    (Q : Hermitian n ≃ₗ[ℝ] Hermitian n)
    (hchart : ∀ T : Hermitian n, T.val.PosDef →
      ((⟨1, Matrix.isHermitian_one⟩ : Hermitian n) +
        Q (T - (⟨1, Matrix.isHermitian_one⟩ : Hermitian n))).val.PosDef)
    (honto : ∀ Y : Hermitian n, Y.val.PosDef →
      ∃ T : Hermitian n, T.val.PosDef ∧ Q T = Y) :
    (normalDisplacement Q).val.PosSemidef := by
  let I : Hermitian n := ⟨1, Matrix.isHermitian_one⟩
  let D := normalDisplacement Q
  have hpositive (T : Hermitian n) (hT : T.val.PosDef) : (T + D).val.PosDef := by
    obtain ⟨U, hU, he⟩ := honto (I + Q (T - I)) (hchart T hT)
    have hu : U = T + D := by
      apply Q.injective
      rw [normalDisplacement_factor]
      exact he
    exact hu ▸ hU
  have hk (k : ℕ) : (0 : ℝ) < (↑(k + 1) : ℝ)⁻¹ :=
    inv_pos.mpr (by exact_mod_cast Nat.succ_pos k)
  have hp (k : ℕ) : (((↑(k + 1) : ℝ)⁻¹) • I + D).val.PosDef :=
    hpositive _ ((Matrix.PosDef.one : I.val.PosDef).smul (hk k))
  have ht : Tendsto (fun k : ℕ => (↑(k + 1) : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hm : Tendsto (fun k : ℕ => ((↑(k + 1) : ℝ)⁻¹) • (1 : Mat n) + D.val)
      atTop (𝓝 D.val) := by
    simpa using (ht.smul_const (1 : Mat n)).add tendsto_const_nhds
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg D.property
  intro x
  have hc : Continuous (fun M : Mat n => star x ⬝ᵥ (M *ᵥ x)) := by fun_prop
  have hq := (hc.tendsto D.val).comp hm
  exact isClosed_Ici.mem_of_tendsto hq
    (Filter.Eventually.of_forall (fun k => (hp k).posSemidef.dotProduct_mulVec_nonneg x))

theorem normalBlowdown_translation_eq
    (F : PositiveDefinite n → PositiveDefinite n)
    (Q : Hermitian n ≃ₗ[ℝ] Hermitian n)
    (hrep : ∀ B : PositiveDefinite n,
      normalCoordinate (F (pdIdentity n)) (F B) =
        Q (normalCoordinate (pdIdentity n) B))
    (hD : (normalDisplacement Q).val.PosSemidef) (A : PositiveDefinite n) :
    normalBlowdownModel Q.toLinearMap (F (pdIdentity n))
      (pdInclusion (squareTranslation (normalDisplacement Q) hD A)) =
        pdInclusion (F A) := by
  let T : Hermitian n := ⟨matrixSqrt A.val,
    (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg A.val)).isHermitian⟩
  have hT : T.val.PosDef :=
    (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg A.val)).posDef_iff_isUnit.mpr
      (A.property.isStrictlyPositive.sqrt).2
  have hsq : squarePoint T.val hT = A :=
    Subtype.ext (matrixSqrt_mul_self A.property.posSemidef)
  have hf := affine_normal_congruence_form F Q.toLinearMap hrep T hT
  rw [hsq] at hf
  have hroot : (⟨matrixSqrt (squareTranslation (normalDisplacement Q) hD A).val,
      (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg _)).isHermitian⟩ :
      Hermitian n) = T + normalDisplacement Q := by
    apply Subtype.ext
    exact matrixSqrt_squareTranslation _ _ _
  apply Subtype.ext
  change (Q (⟨matrixSqrt (squareTranslation (normalDisplacement Q) hD A).val, _⟩ :
    Hermitian n)).val * (F (pdIdentity n)).val *
    (Q (⟨matrixSqrt (squareTranslation (normalDisplacement Q) hD A).val, _⟩ :
    Hermitian n)).val = (F A).val
  rw [hroot, normalDisplacement_factor]
  exact hf.symm

theorem squareTranslation_preserves_of_normal_form
    (F : PositiveDefinite n → PositiveDefinite n) (hF : PreservesDistance F)
    (Q : Hermitian n ≃ₗ[ℝ] Hermitian n)
    (hrep : ∀ B : PositiveDefinite n,
      normalCoordinate (F (pdIdentity n)) (F B) =
        Q (normalCoordinate (pdIdentity n) B))
    (hIso : ∀ X Y, psdDistance (normalBlowdownModel Q.toLinearMap (F (pdIdentity n)) X)
      (normalBlowdownModel Q.toLinearMap (F (pdIdentity n)) Y) = psdDistance X Y)
    (hD : (normalDisplacement Q).val.PosSemidef) :
    PreservesDistance (squareTranslation (normalDisplacement Q) hD) := by
  intro A B
  have h := hIso (pdInclusion (squareTranslation (normalDisplacement Q) hD A))
    (pdInclusion (squareTranslation (normalDisplacement Q) hD B))
  rw [normalBlowdown_translation_eq F Q hrep hD A,
    normalBlowdown_translation_eq F Q hrep hD B] at h
  change distance (F A) (F B) =
    distance (squareTranslation (normalDisplacement Q) hD A)
      (squareTranslation (normalDisplacement Q) hD B) at h
  rw [hF] at h
  exact h.symm

theorem surjective_of_zero_normal_displacement
    (F : PositiveDefinite n → PositiveDefinite n) (hF : PreservesDistance F)
    (Q : Hermitian n ≃ₗ[ℝ] Hermitian n)
    (hrep : ∀ B : PositiveDefinite n,
      normalCoordinate (F (pdIdentity n)) (F B) =
        Q (normalCoordinate (pdIdentity n) B))
    (hIso : ∀ X Y, psdDistance (normalBlowdownModel Q.toLinearMap (F (pdIdentity n)) X)
      (normalBlowdownModel Q.toLinearMap (F (pdIdentity n)) Y) = psdDistance X Y)
    (hzero : normalDisplacement Q = 0) : Function.Surjective F := by
  have hD : (normalDisplacement Q).val.PosSemidef := by
    rw [hzero]
    exact Matrix.PosSemidef.zero
  apply surjective_of_preserves_trace F hF
  intro A
  have htranslation : squareTranslation (normalDisplacement Q) hD A = A := by
    apply Subtype.ext
    change (matrixSqrt A.val + (normalDisplacement Q).val) *
      (matrixSqrt A.val + (normalDisplacement Q).val) = A.val
    rw [hzero]
    simp only [ZeroMemClass.coe_zero, add_zero]
    exact matrixSqrt_mul_self A.property.posSemidef
  have hmodel := normalBlowdown_translation_eq F Q hrep hD A
  rw [htranslation] at hmodel
  have htr := preserves_trace_of_psdZero_fixed
    (normalBlowdownModel Q.toLinearMap (F (pdIdentity n))) hIso
    (normalBlowdownModel_zero Q.toLinearMap (F (pdIdentity n))) (pdInclusion A)
  rw [hmodel] at htr
  exact htr

#print axioms normalDisplacement_posSemidef
#print axioms squareTranslation_preserves_of_normal_form
#print axioms surjective_of_zero_normal_displacement
end Bures

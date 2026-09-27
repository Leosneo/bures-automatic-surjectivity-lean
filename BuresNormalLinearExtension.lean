import BuresNormalTangent
import BuresMidpointIteration
import BuresIsometrySmoothPrelude

/-! A local linear normal-coordinate formula extends to the whole positive
cone, by the exact metric midpoint contraction. -/
noncomputable section
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace Bures
set_option backward.isDefEq.respectTransparency false

theorem normal_representation_of_local_linear
    (F : PositiveDefinite n → PositiveDefinite n) (hF : PreservesDistance F)
    (A : PositiveDefinite n)
    (L : NormalTangentSpace A →ₗ[ℝ] NormalTangentSpace (F A))
    (r : ℝ) (hr : 0 < r)
    (hL : ∀ x, ‖x‖ < r → normalConjugate F A x = L x)
    (B : PositiveDefinite n) :
    normalTangentEquiv (F A) (normalCoordinate (F A) (F B)) =
      L (normalTangentEquiv A (normalCoordinate A B)) := by
  obtain ⟨k, hk⟩ := exists_dyadic_scale_mem_ball r hr
    (normalTangentEquiv A (normalCoordinate A B))
  have hx : normalTangentEquiv A (normalCoordinate A (midpointIteration A B k)) =
      ((1 / 2 : ℝ) ^ k) • normalTangentEquiv A (normalCoordinate A B) := by
    rw [normalCoordinate_midpointIteration, map_smul]
  have hlocal := hL
    (normalTangentEquiv A (normalCoordinate A (midpointIteration A B k)))
    (by rw [hx]; exact hk)
  rw [normalConjugate_at_point, map_midpointIteration F hF,
    normalCoordinate_midpointIteration, map_smul, hx, map_smul] at hlocal
  have hq : (1 / 2 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have h := congrArg (fun v : NormalTangentSpace (F A) =>
    (((1 / 2 : ℝ) ^ k)⁻¹) • v) hlocal
  simpa only [smul_smul, inv_mul_cancel₀ hq, one_smul] using h

/-- The remaining analytic input is exact norm preservation in a small
normal-coordinate ball. Once supplied, the resulting linear equivalence
describes the original isometry globally. -/
theorem normal_representation_of_local_norm_isometry
    (F : PositiveDefinite n → PositiveDefinite n) (hF : PreservesDistance F)
    (A : PositiveDefinite n) (r : ℝ) (hr : 0 < r)
    (hmetric : ∀ x : NormalTangentSpace A, ‖x‖ < r →
      ∀ y : NormalTangentSpace A, ‖y‖ < r →
        ‖normalConjugate F A x - normalConjugate F A y‖ = ‖x - y‖) :
    ∃ Q : Hermitian n ≃ₗ[ℝ] Hermitian n,
      ∀ B : PositiveDefinite n,
        normalCoordinate (F A) (F B) = Q (normalCoordinate A B) := by
  obtain ⟨L, hL⟩ := local_hilbert_isometry_linear
    (normalConjugate F A) r hr (normalConjugate_zero F A) hmetric
  let Q : Hermitian n →ₗ[ℝ] Hermitian n :=
    (normalTangentEquiv (F A)).symm.toLinearMap.comp
      (L.toLinearMap.comp (normalTangentEquiv A).toLinearMap)
  have hQi : Function.Injective Q :=
    (normalTangentEquiv (F A)).symm.injective.comp
      (L.injective.comp (normalTangentEquiv A).injective)
  have hQb : Function.Bijective Q :=
    ⟨hQi, (LinearMap.injective_iff_surjective).mp hQi⟩
  refine ⟨LinearEquiv.ofBijective Q hQb, ?_⟩
  intro B
  have h := normal_representation_of_local_linear F hF A L.toLinearMap r hr
    (fun x hx => hL x hx) B
  apply (normalTangentEquiv (F A)).injective
  change normalTangentEquiv (F A) (normalCoordinate (F A) (F B)) =
    normalTangentEquiv (F A)
      ((normalTangentEquiv (F A)).symm
        (L (normalTangentEquiv A (normalCoordinate A B))))
  rw [LinearEquiv.apply_symm_apply]
  exact h

#print axioms normal_representation_of_local_linear
#print axioms normal_representation_of_local_norm_isometry
end Bures

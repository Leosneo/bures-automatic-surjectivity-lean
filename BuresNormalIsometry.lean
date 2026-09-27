import BuresNormalLinearExtension
import BuresIsometrySmoothTangent

/-! Unconditional global linearity in Bures normal coordinates. -/
noncomputable section
namespace Bures
set_option backward.isDefEq.respectTransparency false

/-- Every self-map preserving the literal Bures distance is represented,
at every positive base point, by a real linear equivalence in centered
positive-transport coordinates. No regularity or surjectivity is assumed. -/
theorem isometry_global_normal_representation
    (F : PositiveDefinite n → PositiveDefinite n) (hF : PreservesDistance F)
    (A : PositiveDefinite n) :
    ∃ Q : Hermitian n ≃ₗ[ℝ] Hermitian n,
      ∀ B : PositiveDefinite n,
        normalCoordinate (F A) (F B) = Q (normalCoordinate A B) := by
  obtain ⟨r, hr, hmetric⟩ := normalConjugate_local_norm_isometry F hF A
  exact normal_representation_of_local_norm_isometry F hF A r hr hmetric

#print axioms isometry_global_normal_representation
end Bures

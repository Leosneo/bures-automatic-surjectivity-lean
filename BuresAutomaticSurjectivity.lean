import BuresNormalIsometry
import BuresNormalNormalization
import BuresTranslationRigidity

/-! Assembly of the normal-coordinate rigidity proof for the literal
finite-dimensional Bures automatic-surjectivity problem. -/
noncomputable section
namespace Bures
set_option backward.isDefEq.respectTransparency false

theorem surjective_of_normal_representation_and_blowdown
    (n : ℕ) (hn : 2 ≤ n)
    (F : PositiveDefinite n → PositiveDefinite n) (hF : PreservesDistance F)
    (Q : Hermitian n ≃ₗ[ℝ] Hermitian n)
    (hrep : ∀ B : PositiveDefinite n,
      normalCoordinate (F (pdIdentity n)) (F B) =
        Q (normalCoordinate (pdIdentity n) B))
    (hIso : ∀ X Y, psdDistance (normalBlowdownModel Q.toLinearMap (F (pdIdentity n)) X)
      (normalBlowdownModel Q.toLinearMap (F (pdIdentity n)) Y) = psdDistance X Y) :
    Function.Surjective F := by
  have hchart := affine_normal_chart_positive F Q.toLinearMap hrep
  have honto := psd_isometry_surjective_of_zero_fixed _ hIso
    (normalBlowdownModel_zero Q.toLinearMap (F (pdIdentity n)))
  have hcone := normalBlowdown_linear_surjective_on_posDef Q.toLinearMap
    (F (pdIdentity n)) hchart hIso honto
  have hD := normalDisplacement_posSemidef Q hchart hcone
  have htranslation := squareTranslation_preserves_of_normal_form F hF Q hrep hIso hD
  have hzero := squareTranslation_displacement_zero n hn (normalDisplacement Q) hD htranslation
  exact surjective_of_zero_normal_displacement F hF Q hrep hIso hzero

#print axioms surjective_of_normal_representation_and_blowdown
theorem automaticSurjectivity : AutomaticSurjectivity := by
  intro n hn F hF
  obtain ⟨Q, hrep⟩ := isometry_global_normal_representation F hF (pdIdentity n)
  have hIso := normalBlowdown_isometry_of_normal_form F hF Q.toLinearMap hrep
  exact surjective_of_normal_representation_and_blowdown n hn F hF Q hrep hIso

theorem literatureProblem : LiteratureProblem :=
  exact_problem_equivalence.mp automaticSurjectivity

#print axioms automaticSurjectivity
#print axioms literatureProblem
end Bures

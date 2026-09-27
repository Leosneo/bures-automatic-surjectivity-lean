import BuresOptimalLiftJointSmooth
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-! A metric-simplex algebra lemma for comparing source and image tangent
frames. It does not assume openness of an isometry's image. -/

noncomputable section
open scoped InnerProductSpace
namespace Bures

/-- Exact pairwise Euclidean distances, including distances to the origin,
determine linear independence even when the two frames live in different
real inner-product spaces. -/
theorem linearIndependent_of_pairwise_norm_eq
    {ι E F : Type*} [Finite ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (v : ι → E) (w : ι → F)
    (hv : LinearIndependent ℝ v)
    (hzero : ∀ i, ‖v i‖ = ‖w i‖)
    (hpair : ∀ i j, ‖v i - v j‖ = ‖w i - w j‖) :
    LinearIndependent ℝ w := by
  have hinner : ∀ i j, ⟪v i, v j⟫_ℝ = ⟪w i, w j⟫_ℝ := by
    intro i j
    have hvij := norm_sub_sq_real (v i) (v j)
    have hwij := norm_sub_sq_real (w i) (w j)
    rw [← hzero i, ← hzero j, ← hpair i j] at hwij
    linarith
  have hgram : Matrix.gram ℝ v = Matrix.gram ℝ w := by
    ext i j
    exact hinner i j
  apply Matrix.linearIndependent_of_posDef_gram
  rw [← hgram]
  exact Matrix.posDef_gram_of_linearIndependent hv

#print axioms linearIndependent_of_pairwise_norm_eq

end Bures

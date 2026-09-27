import BuresImageSimplex
import Mathlib.Topology.Algebra.Group.Matrix

/-! Finite-dimensional simplex stability from approximate Gram data. This
lemma is independent of Bures matrices and can be applied to rescaled image
directions once the required metric tangent convergence is established. -/

noncomputable section
open Filter Topology
open scoped InnerProductSpace
namespace Bures

/-- If the Gram matrices of a moving finite family converge to the Gram
matrix of a linearly independent family, then the moving families are
eventually linearly independent. This allows Gram convergence without
choosing a common orientation for the two frames. -/
theorem eventually_linearIndependent_of_gram_tendsto
    {α ι E F : Type*} [TopologicalSpace α] [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {l : Filter α} (v : ι → E) (w : α → ι → F)
    (hv : LinearIndependent ℝ v)
    (hgram : Tendsto (fun t => Matrix.gram ℝ (w t)) l
      (𝓝 (Matrix.gram ℝ v))) :
    ∀ᶠ t in l, LinearIndependent ℝ (w t) := by
  have hvpd : (Matrix.gram ℝ v).PosDef :=
    Matrix.posDef_gram_of_linearIndependent hv
  have hdet : (Matrix.gram ℝ v).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hvpd.isUnit)
  have hc : Continuous (fun M : Matrix ι ι ℝ => M.det) := by fun_prop
  have hdetlim : Tendsto (fun t => (Matrix.gram ℝ (w t)).det) l
      (𝓝 (Matrix.gram ℝ v).det) :=
    hc.continuousAt.tendsto.comp hgram
  have hne : ∀ᶠ t in l, (Matrix.gram ℝ (w t)).det ≠ 0 :=
    hdetlim.eventually (isOpen_ne.mem_nhds hdet)
  filter_upwards [hne] with t ht
  apply Matrix.linearIndependent_of_posDef_gram
  apply (Matrix.posSemidef_gram ℝ (w t)).posDef_iff_isUnit.mpr
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr ht)

/-- Convergence of the norms and all pairwise distances of a finite frame
implies convergence of its Gram matrix. This is the finite metric-simplex
form needed in a tangent blow-up proof. -/
theorem gram_tendsto_of_pairwise_norm_tendsto
    {α ι E F : Type*} [Fintype ι] [TopologicalSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {l : Filter α} (v : ι → E) (w : α → ι → F)
    (hzero : ∀ i, Tendsto (fun t => ‖w t i‖) l (𝓝 ‖v i‖))
    (hpair : ∀ i j, Tendsto (fun t => ‖w t i - w t j‖) l
      (𝓝 ‖v i - v j‖)) :
    Tendsto (fun t => Matrix.gram ℝ (w t)) l (𝓝 (Matrix.gram ℝ v)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have hsq := (((hzero i).pow 2).add ((hzero j).pow 2)).sub ((hpair i j).pow 2)
  have hinner (x y : F) : 2 * ⟪x, y⟫_ℝ = ‖x‖ ^ 2 + ‖y‖ ^ 2 - ‖x - y‖ ^ 2 := by
    have h := norm_sub_sq_real x y
    linarith
  have hinner' (x y : E) : 2 * ⟪x, y⟫_ℝ = ‖x‖ ^ 2 + ‖y‖ ^ 2 - ‖x - y‖ ^ 2 := by
    have h := norm_sub_sq_real x y
    linarith
  change Tendsto (fun t => ⟪w t i, w t j⟫_ℝ) l (𝓝 ⟪v i, v j⟫_ℝ)
  have hfun : (fun t => ‖w t i‖ ^ 2 + ‖w t j‖ ^ 2 -
      ‖w t i - w t j‖ ^ 2) =
      (fun t => 2 * ⟪w t i, w t j⟫_ℝ) := by
    funext t
    exact (hinner (w t i) (w t j)).symm
  have hval : ‖v i‖ ^ 2 + ‖v j‖ ^ 2 - ‖v i - v j‖ ^ 2 =
      2 * ⟪v i, v j⟫_ℝ := (hinner' (v i) (v j)).symm
  rw [hfun, hval] at hsq
  have hhalf := (tendsto_const_nhds (x := (1 / 2 : ℝ))).mul hsq
  convert hhalf using 1 <;> simp

theorem eventually_linearIndependent_of_pairwise_norm_tendsto
    {α ι E F : Type*} [Fintype ι] [DecidableEq ι] [TopologicalSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {l : Filter α} (v : ι → E) (w : α → ι → F)
    (hv : LinearIndependent ℝ v)
    (hzero : ∀ i, Tendsto (fun t => ‖w t i‖) l (𝓝 ‖v i‖))
    (hpair : ∀ i j, Tendsto (fun t => ‖w t i - w t j‖) l
      (𝓝 ‖v i - v j‖)) :
    ∀ᶠ t in l, LinearIndependent ℝ (w t) :=
  eventually_linearIndependent_of_gram_tendsto v w hv
    (gram_tendsto_of_pairwise_norm_tendsto v w hzero hpair)

#print axioms eventually_linearIndependent_of_gram_tendsto
#print axioms gram_tendsto_of_pairwise_norm_tendsto
#print axioms eventually_linearIndependent_of_pairwise_norm_tendsto
end Bures

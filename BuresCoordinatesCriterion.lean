import BuresSquaredSmooth
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! A coordinate criterion for regularity of a metric-preserving map. The
concrete Bures distance-coordinate Jacobian must still be shown invertible. -/
noncomputable section
open Filter
open scoped Topology ContinuousLinearMap MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace Bures

/-- If a map preserves differentiable coordinates, and the target coordinates
have an invertible strict derivative, then the map is differentiable. -/
theorem differentiableAt_of_preserves_coordinates
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F Csrc Cdst : E → E} {a : E} {e : E ≃L[ℝ] E}
    (hF : ContinuousAt F a)
    (hcoord : ∀ x, Cdst (F x) = Csrc x)
    (hsrc : DifferentiableAt ℝ Csrc a)
    (hdst : HasStrictFDerivAt Cdst (e : E →L[ℝ] E) (F a)) :
    DifferentiableAt ℝ F a := by
  let g := hdst.localInverse Cdst e (F a)
  have hglocal : ∀ᶠ x in 𝓝 a, g (Cdst (F x)) = F x :=
    hF.eventually_mem hdst.eventually_left_inverse
  have hnear : F =ᶠ[𝓝 a] fun x => g (Csrc x) := by
    filter_upwards [hglocal] with x hx
    rw [← hcoord x]
    exact hx.symm
  have hginv : DifferentiableAt ℝ g (Csrc a) := by
    rw [← hcoord a]
    exact hdst.to_localInverse.hasFDerivAt.differentiableAt
  have hcomp : DifferentiableAt ℝ (fun x => g (Csrc x)) a := by
    simpa only [Function.comp_def] using hginv.comp a hsrc
  exact hcomp.congr_of_eventuallyEq hnear

/-- A C¹ coordinate version. The pending concrete obligation is to show that
some finite family of Bures squared-distance coordinates has an invertible
Jacobian and itself is C¹. -/
theorem contDiffAt_one_of_preserves_coordinates
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F Csrc Cdst : E → E} {a : E} {e : E ≃L[ℝ] E}
    (hF : ContinuousAt F a)
    (hcoord : ∀ x, Cdst (F x) = Csrc x)
    (hsrc : ContDiffAt ℝ 1 Csrc a)
    (hdst : ContDiffAt ℝ 1 Cdst (F a))
    (hder : HasFDerivAt Cdst (e : E →L[ℝ] E) (F a)) :
    ContDiffAt ℝ 1 F a := by
  have hn : (1 : WithTop ℕ∞) ≠ 0 := by norm_num
  let hstrict := hdst.hasStrictFDerivAt' hder hn
  let g := hdst.localInverse hder hn
  have hglocal : ∀ᶠ x in 𝓝 a, g (Cdst (F x)) = F x :=
    hF.eventually_mem hstrict.eventually_left_inverse
  have hnear : F =ᶠ[𝓝 a] fun x => g (Csrc x) := by
    filter_upwards [hglocal] with x hx
    rw [← hcoord x]
    exact hx.symm
  have hginv : ContDiffAt ℝ 1 g (Csrc a) := by
    rw [← hcoord a]
    exact hdst.to_localInverse hder hn
  have hcomp : ContDiffAt ℝ 1 (fun x => g (Csrc x)) a := by
    simpa only [Function.comp_def] using hginv.comp a hsrc
  exact hcomp.congr_of_eventuallyEq hnear

/-- Finite or infinite families of literal squared Bures distance coordinates. -/
def anchoredSquaredDistances {ι : Type*} (anchors : ι → Hermitian n)
    (X : Hermitian n) : ι → ℝ :=
  fun i => squaredBuresHermitian (anchors i) X

/-- Every coordinate is differentiable at a positive definite base point when
its anchor is positive definite. -/
theorem differentiableAt_anchoredSquaredDistances {ι : Type*} [Fintype ι]
    (anchors : ι → Hermitian n) (hanchors : ∀ i, (anchors i).val.PosDef)
    (A : Hermitian n) (hA : A.val.PosDef) :
    DifferentiableAt ℝ (anchoredSquaredDistances anchors) A := by
  exact differentiableAt_pi.mpr (fun i =>
    differentiableAt_squaredBuresHermitian (anchors i) A (hanchors i) hA)

#print axioms differentiableAt_of_preserves_coordinates
#print axioms contDiffAt_one_of_preserves_coordinates
#print axioms differentiableAt_anchoredSquaredDistances

end Bures

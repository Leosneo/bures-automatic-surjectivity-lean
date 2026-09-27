import BuresMetricSimplexStability
import BuresNormComparison
import BuresUniqueGeodesic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Convex.StrictConvexBetween

noncomputable section
open Filter
namespace Bures

/-- A map preserving Euclidean distances on a region sends any included
midpoint to the Euclidean midpoint. Surjectivity is not needed. -/
theorem local_hilbert_isometry_midpoint
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (f : E → F) (s : Set E)
    (hmetric : ∀ x ∈ s, ∀ y ∈ s, ‖f x - f y‖ = ‖x - y‖)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s)
    (hm : (1 / 2 : ℝ) • (x + y) ∈ s) :
    f ((1 / 2 : ℝ) • (x + y)) =
      (1 / 2 : ℝ) • (f x + f y) := by
  let m := (1 / 2 : ℝ) • (x + y)
  have hxm : ‖x - m‖ = ‖x - y‖ / 2 := by
    dsimp [m]
    have he : x - (1 / 2 : ℝ) • (x + y) = (1 / 2 : ℝ) • (x - y) := by module
    rw [he, norm_smul]
    norm_num
    ring
  have hmy : ‖m - y‖ = ‖x - y‖ / 2 := by
    dsimp [m]
    have he : (1 / 2 : ℝ) • (x + y) - y = (1 / 2 : ℝ) • (x - y) := by module
    rw [he, norm_smul]
    norm_num
    ring
  apply euclidean_midpoint_unique
  · rw [hmetric x hx m hm, hmetric x hx y hy]
    exact hxm
  · rw [hmetric m hm y hy, hmetric x hx y hy]
    exact hmy

#print axioms local_hilbert_isometry_midpoint

/-- A local isometry fixing the origin is additive whenever the three
arguments and the required midpoints remain in its Euclidean domain. -/
theorem local_hilbert_isometry_add
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (f : E → F) (s : Set E) (hf0 : f 0 = 0)
    (hmetric : ∀ x ∈ s, ∀ y ∈ s, ‖f x - f y‖ = ‖x - y‖)
    {x y : E} (h0 : (0 : E) ∈ s)
    (hx : x ∈ s) (hy : y ∈ s) (hsum : x + y ∈ s)
    (hmid : (1 / 2 : ℝ) • (x + y) ∈ s) :
    f (x + y) = f x + f y := by
  have hxy := local_hilbert_isometry_midpoint f s hmetric hx hy hmid
  have hsum0 := local_hilbert_isometry_midpoint f s hmetric hsum h0 (by
    simpa only [add_zero] using hmid)
  rw [add_zero, hf0, add_zero] at hsum0
  have heq : (1 / 2 : ℝ) • f (x + y) =
      (1 / 2 : ℝ) • (f x + f y) := hsum0.symm.trans hxy
  have h := congrArg (fun z : F => (2 : ℝ) • z) heq
  simpa only [smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul] using h

#print axioms local_hilbert_isometry_add

/-- Every vector can be scaled into an arbitrary positive ball by a dyadic
factor. This will let a local norm isometry be extended to a global one. -/
theorem exists_dyadic_scale_mem_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (hr : 0 < r) (x : E) :
    ∃ k : ℕ, ‖((1 / 2 : ℝ) ^ k) • x‖ < r := by
  have hp : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hs : Tendsto (fun k : ℕ => ((1 / 2 : ℝ) ^ k) • x)
      Filter.atTop (nhds (0 : E)) := by
    simpa using hp.smul_const x
  have hball : Metric.ball (0 : E) r ∈ nhds 0 := Metric.ball_mem_nhds 0 hr
  have hev : ∀ᶠ k : ℕ in Filter.atTop,
      ‖((1 / 2 : ℝ) ^ k) • x‖ < r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hs.eventually hball
  exact hev.exists

#print axioms exists_dyadic_scale_mem_ball

private def dyadicDown (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ k
private def dyadicUp (k : ℕ) : ℝ := (2 : ℝ) ^ k

private theorem dyadicDown_pos (k : ℕ) : 0 < dyadicDown k := by
  unfold dyadicDown
  positivity

private theorem dyadicUp_pos (k : ℕ) : 0 < dyadicUp k := by
  unfold dyadicUp
  positivity

private theorem dyadic_cancel (k : ℕ) : dyadicUp k * dyadicDown k = 1 := by
  unfold dyadicUp dyadicDown
  rw [← mul_pow]
  norm_num

private noncomputable def dyadicIndex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (hr : 0 < r) (x : E) : ℕ :=
  Nat.find (exists_dyadic_scale_mem_ball r hr x)

private theorem dyadicIndex_good
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (hr : 0 < r) (x : E) :
    ‖dyadicDown (dyadicIndex r hr x) • x‖ < r :=
  Nat.find_spec (exists_dyadic_scale_mem_ball r hr x)

private theorem dyadic_good_succ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℝ} {x : E} {k : ℕ}
    (h : ‖dyadicDown k • x‖ < r) :
    ‖dyadicDown (k + 1) • x‖ < r := by
  have he : dyadicDown (k + 1) • x =
      (1 / 2 : ℝ) • (dyadicDown k • x) := by
    simp [dyadicDown, pow_succ, smul_smul, mul_comm]
  rw [he, norm_smul]
  norm_num
  linarith [norm_nonneg (dyadicDown k • x)]

private theorem dyadic_good_mono
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℝ} {x : E} {k l : ℕ}
    (hkl : k ≤ l) (h : ‖dyadicDown k • x‖ < r) :
    ‖dyadicDown l • x‖ < r := by
  induction l, hkl using Nat.le_induction with
  | base => exact h
  | succ l _ ih => exact dyadic_good_succ ih

private def dyadicValue
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (x : E) (k : ℕ) : F :=
  dyadicUp k • f (dyadicDown k • x)

private theorem dyadicValue_succ
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) {r : ℝ} {x : E} {k : ℕ}
    (hhalf : ∀ z, ‖z‖ < r → f ((1 / 2 : ℝ) • z) =
      (1 / 2 : ℝ) • f z)
    (hk : ‖dyadicDown k • x‖ < r) :
    dyadicValue f x (k + 1) = dyadicValue f x k := by
  unfold dyadicValue
  have he : dyadicDown (k + 1) • x =
      (1 / 2 : ℝ) • (dyadicDown k • x) := by
    simp [dyadicDown, pow_succ, smul_smul, mul_comm]
  rw [he, hhalf _ hk]
  simp [dyadicUp, pow_succ, smul_smul]

private theorem dyadicValue_mono
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) {r : ℝ} {x : E} {k l : ℕ}
    (hhalf : ∀ z, ‖z‖ < r → f ((1 / 2 : ℝ) • z) =
      (1 / 2 : ℝ) • f z)
    (hkl : k ≤ l) (hk : ‖dyadicDown k • x‖ < r) :
    dyadicValue f x l = dyadicValue f x k := by
  induction l, hkl using Nat.le_induction with
  | base => rfl
  | succ l hkl ih =>
      rw [dyadicValue_succ f hhalf (dyadic_good_mono hkl hk), ih]

private noncomputable def globalizedDyadic
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (r : ℝ) (hr : 0 < r) (x : E) : F :=
  dyadicValue f x (dyadicIndex r hr x)

private theorem local_half_of_metric
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (f : E → F) (r : ℝ) (hr : 0 < r) (hf0 : f 0 = 0)
    (hmetric : ∀ x, ‖x‖ < r → ∀ y, ‖y‖ < r →
      ‖f x - f y‖ = ‖x - y‖) :
    ∀ z, ‖z‖ < r →
      f ((1 / 2 : ℝ) • z) = (1 / 2 : ℝ) • f z := by
  intro z hz
  let s : Set E := {x | ‖x‖ < r}
  have hzero : (0 : E) ∈ s := by simpa [s] using hr
  have hhalf : (1 / 2 : ℝ) • z ∈ s := by
    change ‖(1 / 2 : ℝ) • z‖ < r
    rw [norm_smul]
    norm_num
    linarith [norm_nonneg z]
  have hmid := local_hilbert_isometry_midpoint f s
    (by intro x hx y hy; exact hmetric x hx y hy)
    hz hzero (by simpa only [add_zero] using hhalf)
  simpa only [add_zero, hf0] using hmid

/-- A Euclidean local isometry around zero extends uniquely by dyadic
rescaling to a global isometric embedding. No surjectivity is required. -/
theorem globalized_local_hilbert_isometry
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (f : E → F) (r : ℝ) (hr : 0 < r) (hf0 : f 0 = 0)
    (hmetric : ∀ x, ‖x‖ < r → ∀ y, ‖y‖ < r →
      ‖f x - f y‖ = ‖x - y‖) :
    ∃ g : E → F,
      (∀ x, ‖x‖ < r → g x = f x) ∧
      (∀ x y, ‖g x - g y‖ = ‖x - y‖) ∧ g 0 = 0 := by
  let hhalf := local_half_of_metric f r hr hf0 hmetric
  let g := globalizedDyadic f r hr
  have hagree : ∀ x, ‖x‖ < r → g x = f x := by
    intro x hx
    have h0 : ‖dyadicDown 0 • x‖ < r := by simpa [dyadicDown] using hx
    have hle : 0 ≤ dyadicIndex r hr x := Nat.zero_le _
    have hv := dyadicValue_mono f hhalf hle h0
    change g x = dyadicValue f x 0 at hv
    simpa [dyadicValue, dyadicDown, dyadicUp] using hv
  have hdist : ∀ x y, ‖g x - g y‖ = ‖x - y‖ := by
    intro x y
    let k := max (dyadicIndex r hr x) (dyadicIndex r hr y)
    have hxk : ‖dyadicDown k • x‖ < r :=
      dyadic_good_mono (Nat.le_max_left _ _) (dyadicIndex_good r hr x)
    have hyk : ‖dyadicDown k • y‖ < r :=
      dyadic_good_mono (Nat.le_max_right _ _) (dyadicIndex_good r hr y)
    have hgx : g x = dyadicValue f x k :=
      (dyadicValue_mono f hhalf (Nat.le_max_left _ _)
        (dyadicIndex_good r hr x)).symm
    have hgy : g y = dyadicValue f y k :=
      (dyadicValue_mono f hhalf (Nat.le_max_right _ _)
        (dyadicIndex_good r hr y)).symm
    rw [hgx, hgy]
    have he : dyadicValue f x k - dyadicValue f y k =
        dyadicUp k • (f (dyadicDown k • x) - f (dyadicDown k • y)) := by
      simp [dyadicValue, smul_sub]
    rw [he, norm_smul]
    rw [Real.norm_eq_abs, abs_of_pos (dyadicUp_pos k),
      hmetric _ hxk _ hyk]
    have hsub : dyadicDown k • x - dyadicDown k • y =
        dyadicDown k • (x - y) := (smul_sub _ _ _).symm
    rw [hsub, norm_smul, Real.norm_eq_abs,
      abs_of_pos (dyadicDown_pos k), ← mul_assoc, dyadic_cancel, one_mul]
  refine ⟨g, hagree, hdist, ?_⟩
  exact (hagree 0 (by simpa using hr)).trans hf0

#print axioms globalized_local_hilbert_isometry

/-- The local Euclidean isometry is the restriction of a global real-linear
isometric embedding. This is a local version of the affine-isometry theorem
proved without an openness or surjectivity assumption. -/
theorem local_hilbert_isometry_linear
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (f : E → F) (r : ℝ) (hr : 0 < r) (hf0 : f 0 = 0)
    (hmetric : ∀ x, ‖x‖ < r → ∀ y, ‖y‖ < r →
      ‖f x - f y‖ = ‖x - y‖) :
    ∃ L : E →ₗᵢ[ℝ] F, ∀ x, ‖x‖ < r → f x = L x := by
  obtain ⟨g, hagree, hdist, hg0⟩ :=
    globalized_local_hilbert_isometry f r hr hf0 hmetric
  have hi : Isometry g := Isometry.of_dist_eq (by
    intro x y
    simpa only [dist_eq_norm] using hdist x y)
  let a := hi.affineIsometryOfStrictConvexSpace
  let L : E →ₗᵢ[ℝ] F := a.linearIsometry
  refine ⟨L, ?_⟩
  intro x hx
  rw [← hagree x hx]
  have h := congrFun a.toAffineMap.decomp x
  change g x = L x + g 0 at h
  simpa only [hg0, add_zero] using h

#print axioms local_hilbert_isometry_linear

end Bures

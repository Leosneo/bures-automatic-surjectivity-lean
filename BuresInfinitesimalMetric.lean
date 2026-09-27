import BuresCoordinateCurvature
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! A general norm-lift differentiation lemma used to identify the
infinitesimal metric of an exact Frobenius quotient formula. -/

noncomputable section
namespace Bures
open scoped Matrix.Norms.Frobenius Topology

/-- If a real one-parameter distance is exactly the Frobenius norm from a
fixed factor to a differentiable optimal lift, its speed is the Frobenius
norm of the lift derivative. -/
theorem speed_of_differentiable_optimal_lift
    (D : ℝ → ℝ) (Y : ℝ → Mat n) (S V : Mat n)
    (hY : HasDerivAt Y V 0) (hY0 : Y 0 = S)
    (hD : ∀ t, D t = ‖S - Y t‖) :
    Filter.Tendsto (fun t => D t / |t|) (𝓝[≠] (0 : ℝ)) (𝓝 ‖V‖) := by
  have hs := hY.tendsto_slope_zero.norm
  have heq (t : ℝ) (ht : t ≠ 0) :
      D t / |t| = ‖slope Y 0 t‖ := by
    rw [hD, slope_def_module]
    simp only [hY0, sub_zero]
    rw [norm_smul, norm_inv, Real.norm_eq_abs]
    rw [← norm_neg (S - Y t), neg_sub]
    ring
  apply Filter.Tendsto.congr' ?_ hs
  filter_upwards [self_mem_nhdsWithin] with t ht
  simpa only [slope_def_module, zero_add, sub_zero] using (heq t ht).symm

/-- The squared-distance ratio has the expected quadratic limit. -/
theorem squared_speed_of_differentiable_optimal_lift
    (D : ℝ → ℝ) (Y : ℝ → Mat n) (S V : Mat n)
    (hY : HasDerivAt Y V 0) (hY0 : Y 0 = S)
    (hD : ∀ t, D t = ‖S - Y t‖) :
    Filter.Tendsto (fun t => D t ^ 2 / t ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (‖V‖ ^ 2)) := by
  convert (speed_of_differentiable_optimal_lift D Y S V hY hY0 hD).pow 2 using 1
  ext t
  simp only [div_pow, sq_abs]

/-- The same quadratic limit when the optimal-lift formula only holds near
the base point, as happens for a path constrained to positive matrices. -/
theorem squared_speed_of_eventual_optimal_lift
    (D : ℝ → ℝ) (Y : ℝ → Mat n) (S V : Mat n)
    (hY : HasDerivAt Y V 0) (hY0 : Y 0 = S)
    (hD : ∀ᶠ t in 𝓝[≠] (0 : ℝ), D t = ‖S - Y t‖) :
    Filter.Tendsto (fun t => D t ^ 2 / t ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (‖V‖ ^ 2)) := by
  let E : ℝ → ℝ := fun t => ‖S - Y t‖
  have hE := squared_speed_of_differentiable_optimal_lift E Y S V
    hY hY0 (fun _ => rfl)
  apply Filter.Tendsto.congr' ?_ hE
  filter_upwards [hD] with t ht
  simp [E, ht]

#print axioms squared_speed_of_differentiable_optimal_lift

end Bures

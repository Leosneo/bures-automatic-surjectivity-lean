import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic

/-! Algebraic last step of Euler-field rigidity. The missing geometric step
must first establish the displayed directional balance for an actual Bures
isometry; this lemma does not assume or prove that step. -/

namespace BuresSupport

theorem radial_scale_eq_one {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (hdim : 1 < Module.finrank ℝ V)
    (z : V) (c : ℝ) (ℓ : V → ℝ)
    (h : ∀ y : V, (1 - c) • y = (ℓ y) • z) : c = 1 := by
  by_contra hc
  have hne : 1 - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  have hgen (y : V) : ∃ a : ℝ, a • z = y := by
    refine ⟨ℓ y / (1 - c), ?_⟩
    calc
      _ = (1 / (1 - c)) • ((ℓ y) • z) := by simp [smul_smul, div_eq_mul_inv, mul_comm]
      _ = (1 / (1 - c)) • ((1 - c) • y) := by rw [h y]
      _ = y := by rw [smul_smul, one_div, inv_mul_cancel₀ hne, one_smul]
  exact (not_le.mpr hdim) (finrank_le_one z hgen)

#print axioms radial_scale_eq_one
end BuresSupport

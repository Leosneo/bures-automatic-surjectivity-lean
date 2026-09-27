import BuresCoordinateCurvature

/-! The exact vertical residual of constant Hermitian horizontal brackets. -/
noncomputable section
open scoped MatrixOrder ComplexOrder ContinuousLinearMap
namespace Bures

/-- A Gram-map tangent is Hermitian. -/
theorem gram_linear_isHermitian (S B : Mat n) :
    (B * S.conjTranspose + S * B.conjTranspose).IsHermitian := by
  apply Matrix.isHermitian_iff_isSelfAdjoint.mpr
  change (B * S.conjTranspose + S * B.conjTranspose).conjTranspose = _
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  exact add_comm _ _

/-- Subtract the unique horizontal component from a horizontal-field bracket.
The residual is vertical. It vanishes precisely when the generators commute. -/
theorem vertical_bracket_residual (S K L : Mat n) (hA : (gram S).PosDef)
    (hK : K.IsHermitian) (hL : L.IsHermitian) :
    ∃ J : Mat n, J.IsHermitian ∧
      ∃ D : Mat n →L[ℝ] Mat n,
        HasFDerivAt gram D S ∧
        D (((K * L - L * K) * S) - J * S) = 0 ∧
        ((((K * L - L * K) * S) - J * S = 0) ↔ Commute K L) := by
  let B := (K * L - L * K) * S
  let X := B * S.conjTranspose + S * B.conjTranspose
  have hX : X.IsHermitian := gram_linear_isHermitian S B
  obtain ⟨J, ⟨hJ, hJE⟩, _⟩ :=
    posDef_hermitian_sylvester_existsUnique hA hX
  obtain ⟨D, hD, hDformula⟩ := gram_hasFDerivAt S
  refine ⟨J, hJ, D, hD, ?_, ?_⟩
  · rw [map_sub, hDformula, hDformula,
      gram_horizontal_linear S J hJ]
    exact sub_eq_zero.mpr hJE.symm
  · constructor
    · intro hr
      have hS : IsUnit S := isUnit_of_mul_isUnit_left hA.isUnit
      apply (commutator_horizontal_iff hS hK hL).mp
      refine ⟨J, hJ, ?_⟩
      exact sub_eq_zero.mp hr
    · intro hc
      have hB : B = 0 := by
        simp [B, hc.eq]
      have hX0 : X = 0 := by simp [X, hB]
      have hJE0 : J * gram S + gram S * J = 0 := hX0 ▸ hJE
      obtain ⟨Y, hY, hu⟩ := posDef_sylvester_existsUnique hA (0 : Mat n)
      have hY0 : Y = 0 := (hu 0 (by simp)).symm
      have hJ0 : J = 0 := (hu J hJE0).trans hY0
      simp [B, hB, hJ0]

#print axioms vertical_bracket_residual
end Bures

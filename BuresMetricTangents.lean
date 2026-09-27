import BuresHorizontalLocal

/-! Every Hermitian tangent has a unique horizontal generator, and the
literal Bures distance has the corresponding local quadratic speed. -/
noncomputable section
open Filter
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator Matrix.Norms.Frobenius Topology
namespace Bures

/-- Every Hermitian tangent is represented by a horizontal Gram curve.
Its squared distance speed is the Sylvester quadratic form. -/
theorem exists_horizontal_curve_speed (A : PositiveDefinite n) (X : Mat n)
    (hX : X.IsHermitian) :
    ∃ K : Mat n, K.IsHermitian ∧ K * A.val + A.val * K = X ∧
      Filter.Tendsto (fun t : ℝ =>
        distance A (horizontalGramPoint A K t) ^ 2 / t ^ 2)
        (𝓝[≠] (0 : ℝ)) (𝓝 (tr (X * K) / 2)) := by
  obtain ⟨K, ⟨hK, hEq⟩, _⟩ :=
    posDef_hermitian_sylvester_existsUnique A.property hX
  refine ⟨K, hK, hEq, ?_⟩
  rw [← hEq]
  exact horizontalGramPoint_squared_speed A K hK

/-- The local squared speed of the radial tangent `2A` equals `tr A`.
This is an intrinsic expression in the literal Bures distance. -/
theorem radial_horizontal_curve_speed (A : PositiveDefinite n) :
    Filter.Tendsto (fun t : ℝ =>
      distance A (horizontalGramPoint A (1 : Mat n) t) ^ 2 / t ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (tr A.val)) := by
  have h := horizontalGramPoint_squared_speed A (1 : Mat n) Matrix.isHermitian_one
  have htarget : tr (((1 : Mat n) * A.val + A.val * 1) * 1) / 2 =
      tr A.val := by
    simp only [one_mul, mul_one, tr_add]
    ring
  rw [htarget] at h
  exact h

#print axioms exists_horizontal_curve_speed
#print axioms radial_horizontal_curve_speed
end Bures

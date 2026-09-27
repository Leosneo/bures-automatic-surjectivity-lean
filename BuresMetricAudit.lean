import BuresExtension

/-! Independent definitional checks: the metric distances are the literal
Bures formulas, the topologies are the original matrix subtype topologies,
and completeness uses the Bures uniformity explicitly. -/
noncomputable section
namespace Bures

example (n : ℕ) : (positiveDefiniteMetricSpace n).toUniformSpace.toTopologicalSpace =
    (inferInstance : TopologicalSpace (PositiveDefinite n)) := rfl

example (n : ℕ) : (psdMetricSpace n).toUniformSpace.toTopologicalSpace =
    (inferInstance : TopologicalSpace (PSD n)) := rfl

example (A B : PositiveDefinite n) :
    @dist (PositiveDefinite n) (positiveDefiniteMetricSpace n).toDist A B =
      distance A B := rfl

example (A B : PSD n) :
    @dist (PSD n) (psdMetricSpace n).toDist A B = psdDistance A B := rfl

example (n : ℕ) :
    @CompleteSpace (PSD n) (psdMetricSpace n).toUniformSpace := psdCompleteSpace

section
local instance : MetricSpace (PSD n) := psdMetricSpace n
local instance : MetricSpace (PositiveDefinite n) := positiveDefiniteMetricSpace n
local instance : UniformSpace (PSD n) := (psdMetricSpace n).toUniformSpace
local instance : UniformSpace (PositiveDefinite n) := (positiveDefiniteMetricSpace n).toUniformSpace

example (F : PositiveDefinite n → PositiveDefinite n) :
    Isometry F ↔ PreservesDistance F := isometry_iff_dist_eq

example (F : PositiveDefinite n → PositiveDefinite n) (hF : PreservesDistance F) :
    ∃ E : PSD n → PSD n,
      (∀ A B, psdDistance (E A) (E B) = psdDistance A B) ∧
      ∀ A, E (pdInclusion A) = pdInclusion (F A) := by
  obtain ⟨E, hE, hext⟩ := exists_psd_isometric_extension F hF
  exact ⟨E, hE.dist_eq, hext⟩
end

#print axioms exists_psd_isometric_extension
#print axioms surjective_of_preserves_trace
end Bures

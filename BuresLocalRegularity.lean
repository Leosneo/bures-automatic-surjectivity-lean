import BuresMetric

/-! An actual distance-preserving map is continuous in the ordinary matrix
topology. This is the topological part of the desired local regularity; it
does not assert differentiability or invoke Myers--Steenrod. -/

noncomputable section
open Topology
namespace Bures

local instance : MetricSpace (PositiveDefinite n) := positiveDefiniteMetricSpace n

/-- Preservation of the literal Bures formula gives an isometric embedding
in the metric that has the ordinary positive-definite matrix topology. -/
theorem isometry_of_preserves_distance
    (F : PositiveDefinite n → PositiveDefinite n)
    (hF : PreservesDistance F) : Isometry F :=
  Isometry.of_dist_eq hF

theorem continuous_of_preserves_distance
    (F : PositiveDefinite n → PositiveDefinite n)
    (hF : PreservesDistance F) : Continuous F :=
  (isometry_of_preserves_distance F hF).continuous

theorem injective_of_preserves_distance
    (F : PositiveDefinite n → PositiveDefinite n)
    (hF : PreservesDistance F) : Function.Injective F :=
  (isometry_of_preserves_distance F hF).injective

theorem isEmbedding_of_preserves_distance
    (F : PositiveDefinite n → PositiveDefinite n)
    (hF : PreservesDistance F) : IsEmbedding F :=
  (isometry_of_preserves_distance F hF).isEmbedding

#print axioms continuous_of_preserves_distance
#print axioms isEmbedding_of_preserves_distance
end Bures

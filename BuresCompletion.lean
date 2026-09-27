import BuresPSDMetric
import BuresMetric
import Mathlib.Topology.MetricSpace.ProperSpace
noncomputable section
open scoped MatrixOrder ComplexOrder Topology
open Filter
namespace Bures

/-- The standard positive-definite to positive-semidefinite inclusion. -/
def pdInclusion (A : PositiveDefinite n) : PSD n := ⟨A.val, A.property.posSemidef⟩

theorem denseRange_pdInclusion : DenseRange (pdInclusion (n := n)) := by
  intro A
  exact mem_closure_of_tendsto (tendsto_regularize A)
    (Filter.Eventually.of_forall fun m => ⟨regularize A m, rfl⟩)

theorem isCompact_psd_sublevel (R : ℝ) : IsCompact {A : PSD n | tr A.val ≤ R} := by
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  convert BuresSupport.isCompact_psd_trace_sublevel n R using 1
  ext A
  constructor
  · rintro ⟨B, hB, rfl⟩
    exact ⟨B.property, hB⟩
  · rintro ⟨hA, ht⟩
    exact ⟨⟨A, hA⟩, ht, rfl⟩

section Metric
local instance : MetricSpace (PSD n) := psdMetricSpace n
local instance : MetricSpace (PositiveDefinite n) := positiveDefiniteMetricSpace n

theorem isometry_pdInclusion : Isometry (pdInclusion (n := n)) := by
  apply Isometry.of_dist_eq
  intro A B
  rfl

/-- Properness of the actual PSD Bures metric; this implies completeness. -/
theorem psdProperSpace : ProperSpace (PSD n) := by
  apply ProperSpace.of_seq_closedBall (x := psdZero) (r := fun m : ℕ => (m : ℝ))
    tendsto_natCast_atTop_atTop
  apply Filter.Eventually.of_forall
  intro m
  have he : Metric.closedBall (psdZero : PSD n) (m : ℝ) =
      {A : PSD n | tr A.val ≤ (m : ℝ)^2} := by
    ext A
    rw [Metric.mem_closedBall]
    change psdDistance A psdZero ≤ (m : ℝ) ↔ _
    rw [psdDistance_zero]
    rw [Real.sqrt_le_iff]
    simp
  rw [he]
  exact isCompact_psd_sublevel _

theorem psdCompleteSpace :
    @CompleteSpace (PSD n) (psdMetricSpace n).toPseudoMetricSpace.toUniformSpace := by
  exact @complete_of_proper (PSD n) (psdMetricSpace n).toPseudoMetricSpace
    (psdProperSpace (n := n))

#print axioms psdProperSpace
#print axioms psdCompleteSpace
#print axioms isometry_pdInclusion
end Metric
end Bures

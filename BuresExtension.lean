import BuresCompletion
import IsometryExtension
import CompactSurjectivity

/-!
The completion and surjectivity part of the proposed Bures argument.

Every actual distance-preserving map has an isometric PSD extension. Surjectivity
is proved BELOW WITH AN EXPLICIT TRACE-PRESERVATION HYPOTHESIS. The geometric
deduction of that hypothesis is not supplied by this file.
-/
noncomputable section
open scoped MatrixOrder ComplexOrder
namespace Bures

local instance : MetricSpace (PSD n) := psdMetricSpace n
local instance : MetricSpace (PositiveDefinite n) := positiveDefiniteMetricSpace n
local instance : UniformSpace (PSD n) := (psdMetricSpace n).toPseudoMetricSpace.toUniformSpace
local instance : UniformSpace (PositiveDefinite n) :=
  (positiveDefiniteMetricSpace n).toPseudoMetricSpace.toUniformSpace
local instance : CompleteSpace (PSD n) := psdCompleteSpace

/-- Every isometric embedding of the open cone extends to the actual PSD cone. -/
theorem exists_psd_isometric_extension (F : PositiveDefinite n → PositiveDefinite n)
    (hF : PreservesDistance F) :
    ∃ E : PSD n → PSD n, Isometry E ∧ ∀ A, E (pdInclusion A) = pdInclusion (F A) := by
  exact BuresSupport.exists_isometry_extension pdInclusion isometry_pdInclusion
    denseRange_pdInclusion F (Isometry.of_dist_eq hF)

/-- Conditional result: the remaining hypothesis is trace preservation. This
theorem does not prove `AutomaticSurjectivity`. -/
theorem surjective_of_preserves_trace (F : PositiveDefinite n → PositiveDefinite n)
    (hF : PreservesDistance F) (htr : ∀ A, tr (F A).val = tr A.val) :
    Function.Surjective F := by
  obtain ⟨E, hE, hext⟩ := exists_psd_isometric_extension F hF
  have htrE : ∀ A : PSD n, tr (E A).val = tr A.val :=
    BuresSupport.extension_preserves_continuous_function pdInclusion denseRange_pdInclusion
      F E hE.continuous hext (fun A => tr A.val)
      (continuous_tr.comp continuous_subtype_val) htr
  have honto : Function.Surjective E :=
    BuresSupport.surjective_of_preserves_compact_sublevels (fun A : PSD n => tr A.val)
      isCompact_psd_sublevel hE htrE
  have hzero : E psdZero = psdZero := by
    apply Subtype.ext
    apply (tr_eq_zero_iff (E psdZero).property).mp
    rw [htrE]
    simp [psdZero, tr]
  have hf : ∀ A B, fidelityRoot (E A).val (E B).val = fidelityRoot A.val B.val :=
    preserves_fidelity_of_psdZero_fixed E hE.dist_eq hzero
  exact surjective_of_semidefinite_extension F E ⟨hE.injective, honto⟩ hzero hf
    (fun A => congrArg Subtype.val (hext A))

#print axioms exists_psd_isometric_extension
#print axioms surjective_of_preserves_trace
end Bures

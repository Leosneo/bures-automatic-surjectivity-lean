import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-! Isometric extension along a dense isometric embedding into a complete space. -/
noncomputable section
open Topology
namespace BuresSupport

theorem exists_isometry_extension {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompleteSpace Y] (e : X → Y) (he : Isometry e) (hd : DenseRange e)
    (f : X → X) (hf : Isometry f) :
    ∃ E : Y → Y, Isometry E ∧ ∀ x, E (e x) = e (f x) := by
  let di := he.isUniformInducing.isDenseInducing hd
  let E := di.extend (e ∘ f)
  have huc := (he.comp hf).uniformContinuous
  have hc : Continuous E :=
    (uniformContinuous_uniformly_extend he.isUniformInducing hd huc).continuous
  have hext (x : X) : E (e x) = e (f x) :=
    uniformly_extend_of_ind he.isUniformInducing hd huc x
  refine ⟨E, Isometry.of_dist_eq ?_, hext⟩
  intro a b
  refine hd.induction_on₂ (p := fun a b => dist (E a) (E b) = dist a b) ?_ ?_ a b
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro x y
    rw [hext, hext, he.dist_eq, he.dist_eq, hf.dist_eq]

theorem extension_preserves_continuous_function {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X → Y) (hd : DenseRange e)
    (f : X → X) (E : Y → Y) (hE : Continuous E) (hext : ∀ x, E (e x) = e (f x))
    (ρ : Y → ℝ) (hρ : Continuous ρ) (hp : ∀ x, ρ (e (f x)) = ρ (e x)) :
    ∀ y, ρ (E y) = ρ y := by
  have h : (fun y => ρ (E y)) = ρ := hd.equalizer (hρ.comp hE) hρ (by
    funext x
    rw [Function.comp_apply, Function.comp_apply, hext, hp])
  exact congrFun h

#print axioms exists_isometry_extension
end BuresSupport

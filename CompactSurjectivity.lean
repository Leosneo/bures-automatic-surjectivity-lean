import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.Sequences
import Mathlib.Tactic

/-! A complete auxiliary theorem used in the completion step of the draft.
This does NOT install a Bures metric or prove the Bures conjecture. -/

namespace BuresSupport

theorem compact_isometry_surjective {X : Type*} [MetricSpace X] [CompactSpace X]
    {f : X → X} (hf : Isometry f) : Function.Surjective f := by
  have iter_dist (k : ℕ) (a b : X) :
      dist (f^[k] a) (f^[k] b) = dist a b := by
    induction k with
    | zero => rfl
    | succ k ih =>
      simpa only [Function.iterate_succ_apply', hf.dist_eq] using ih
  intro x
  have hc : x ∈ closure (Set.range f) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨y, u, hu, ht⟩ := CompactSpace.tendsto_subseq (fun k => f^[k] x)
    obtain ⟨k, hk⟩ := Metric.tendsto_atTop.mp ht (ε / 2) (half_pos hε)
    have hnear : dist (f^[u k] x) (f^[u (k + 1)] x) < ε := by
      calc
        _ ≤ dist (f^[u k] x) y + dist y (f^[u (k + 1)] x) :=
          dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := add_lt_add
          (hk k le_rfl) (by
            simpa only [Function.comp_apply, dist_comm] using (hk (k + 1) (Nat.le_succ k)))
        _ = ε := by ring
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le
      (Nat.succ_le_of_lt (hu (Nat.lt_succ_self k)))
    have hd' : u (k + 1) = u k + (d + 1) := by
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hd
    refine ⟨f^[d + 1] x, ⟨f^[d] x, ?_⟩, ?_⟩
    · simp only [Function.iterate_succ_apply']
    · simpa only [hd', Function.iterate_add_apply, iter_dist] using hnear
  have hr : x ∈ Set.range f := by
    rwa [(isCompact_range hf.continuous).isClosed.closure_eq] at hc
  exact hr

/-- The compact trace-ball step, stated generally and proved without any
assumption that the map is already onto. Applying it to Bures matrices still
requires formal proofs of the Bures metric, compact trace sublevels and trace rigidity. -/
theorem surjective_of_preserves_compact_sublevels {X : Type*} [MetricSpace X]
    (ρ : X → ℝ) (hcompact : ∀ R : ℝ, IsCompact {x | ρ x ≤ R})
    {f : X → X} (hf : Isometry f) (hρ : ∀ x, ρ (f x) = ρ x) :
    Function.Surjective f := by
  intro y
  let S := {x : X | ρ x ≤ ρ y}
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp (hcompact (ρ y))
  let g : S → S := fun x => ⟨f x.val, by
    change ρ (f x.val) ≤ ρ y
    rw [hρ]
    exact x.property⟩
  have hg : Isometry g := Isometry.of_dist_eq (fun a b => hf.dist_eq a.val b.val)
  obtain ⟨x, hx⟩ := compact_isometry_surjective hg (⟨y, by change ρ y ≤ ρ y; rfl⟩ : S)
  exact ⟨x.val, congrArg Subtype.val hx⟩

#print axioms compact_isometry_surjective
#print axioms surjective_of_preserves_compact_sublevels

end BuresSupport

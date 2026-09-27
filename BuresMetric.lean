import BuresFrobenius
import BuresTopology

/-! The genuine Bures metric, retaining the usual topology on the open matrix
cone. No trace-preservation assumption is used. -/
noncomputable section
open scoped MatrixOrder ComplexOrder Matrix.Norms.Frobenius Topology
open Matrix
namespace Bures

lemma frobenius_matrixSqrt (A : PositiveDefinite n) :
    ‖matrixSqrt A.val‖ = Real.sqrt (tr A.val) := by
  rw [frobenius_norm_eq_sqrt_tr_gram,
    (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg A.val)).isHermitian.eq,
    matrixSqrt_mul_self A.property.posSemidef]

lemma sqrt_tr_le_sqrt_tr_add_distance (A B : PositiveDefinite n) :
    Real.sqrt (tr B.val) ≤ Real.sqrt (tr A.val) + distance A B := by
  obtain ⟨U, _, hUr, hd⟩ := distance_eq_frobenius_unitary A B
  have h := norm_sub_norm_le (matrixSqrt B.val * U) (matrixSqrt A.val)
  rw [frobenius_norm_mul_unitary _ U hUr, frobenius_matrixSqrt,
    frobenius_matrixSqrt, norm_sub_rev, ← hd] at h
  linarith

lemma isOpen_iff_bures_balls (s : Set (PositiveDefinite n)) :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, distance x y < ε → y ∈ s := by
  constructor
  · intro hs x hx
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hs x hx
    let R := 2 * Real.sqrt (tr x.val) + 1
    have hR : 0 < R := by dsimp [R]; positivity
    refine ⟨min 1 (δ / R), lt_min zero_lt_one (div_pos hδ hR), ?_⟩
    intro y hy
    have hy1 : distance x y < 1 := lt_of_lt_of_le hy (min_le_left _ _)
    have hyd : distance x y < δ / R := lt_of_lt_of_le hy (min_le_right _ _)
    have htr := sqrt_tr_le_sqrt_tr_add_distance x y
    have hn := frobenius_sub_le_distance x y
    have hnδ : ‖x.val - y.val‖ < δ := by
      have hc : Real.sqrt (tr x.val) + Real.sqrt (tr y.val) ≤ R := by
        dsimp [R]
        linarith
      have hmul : R * distance x y < δ := by
        nlinarith [(lt_div_iff₀ hR).mp hyd]
      exact lt_of_le_of_lt (hn.trans (mul_le_mul_of_nonneg_right hc (distance_nonneg x y))) hmul
    apply hball
    change dist y x < δ
    rw [Subtype.dist_eq, dist_eq_norm, norm_sub_rev]
    exact hnδ
  · intro h
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨ε, hε, hs⟩ := h x hx
    have hc : Continuous (fun y : PositiveDefinite n => distance x y) :=
      continuous_distance.comp (continuous_const.prodMk continuous_id)
    have hn : {y : PositiveDefinite n | distance x y < ε} ∈ 𝓝 x :=
      (isOpen_lt hc continuous_const).mem_nhds (by simpa [distance_self] using hε)
    exact Filter.mem_of_superset hn hs

/-- The literal Bures formula equips positive-definite matrices with a metric
whose underlying topology is definitionally the ordinary subtype topology. -/
@[implicit_reducible]
def positiveDefiniteMetricSpace (n : ℕ) : MetricSpace (PositiveDefinite n) :=
  MetricSpace.ofDistTopology distance distance_self distance_comm distance_triangle
    isOpen_iff_bures_balls (fun A B h => (distance_eq_zero_iff A B).mp h)

#print axioms positiveDefiniteMetricSpace
end Bures

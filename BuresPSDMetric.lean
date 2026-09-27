import BuresSeparation

/-! The Bures metric on the semidefinite completion has exactly the ordinary
matrix topology. -/
noncomputable section
open scoped MatrixOrder ComplexOrder Matrix.Norms.Frobenius Topology
open Matrix
namespace Bures

lemma sqrt_tr_le_sqrt_tr_add_psdDistance (A B : PSD n) :
    Real.sqrt (tr B.val) ≤ Real.sqrt (tr A.val) + psdDistance A B := by
  have h := psdDistance_triangle B A psdZero
  rw [psdDistance_zero, psdDistance_zero, psdDistance_comm B A] at h
  linarith

lemma isOpen_iff_psd_bures_balls (s : Set (PSD n)) :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, psdDistance x y < ε → y ∈ s := by
  constructor
  · intro hs x hx
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hs x hx
    let R := 2 * Real.sqrt (tr x.val) + 1
    have hR : 0 < R := by dsimp [R]; positivity
    refine ⟨min 1 (δ / R), lt_min zero_lt_one (div_pos hδ hR), ?_⟩
    intro y hy
    have hy1 : psdDistance x y < 1 := lt_of_lt_of_le hy (min_le_left _ _)
    have hyd : psdDistance x y < δ / R := lt_of_lt_of_le hy (min_le_right _ _)
    have htr := sqrt_tr_le_sqrt_tr_add_psdDistance x y
    have hn := frobenius_sub_le_psdDistance x y
    have hnδ : ‖x.val - y.val‖ < δ := by
      have hc : Real.sqrt (tr x.val) + Real.sqrt (tr y.val) ≤ R := by
        dsimp [R]
        linarith
      have hmul : R * psdDistance x y < δ := by
        nlinarith [(lt_div_iff₀ hR).mp hyd]
      exact lt_of_le_of_lt (hn.trans (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _))) hmul
    apply hball
    change dist y x < δ
    rw [Subtype.dist_eq, dist_eq_norm, norm_sub_rev]
    exact hnδ
  · intro h
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨ε, hε, hs⟩ := h x hx
    have hc : Continuous (fun y : PSD n => psdDistance x y) :=
      continuous_psdDistance.comp (continuous_const.prodMk continuous_id)
    have hn : {y : PSD n | psdDistance x y < ε} ∈ 𝓝 x :=
      (isOpen_lt hc continuous_const).mem_nhds (by simpa [psdDistance_self] using hε)
    exact Filter.mem_of_superset hn hs

/-- The literal PSD Bures metric retains the ordinary subtype topology. -/
@[implicit_reducible]
def psdMetricSpace (n : ℕ) : MetricSpace (PSD n) :=
  MetricSpace.ofDistTopology psdDistance psdDistance_self psdDistance_comm psdDistance_triangle
    isOpen_iff_psd_bures_balls psdDistance_eq_zero_imp

#print axioms psdMetricSpace
end Bures

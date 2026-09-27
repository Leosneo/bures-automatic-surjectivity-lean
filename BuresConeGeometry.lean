import BuresRadial
import BuresSymmetry
import BuresRadicand

/-! Exact metric-cone scaling identities for the literal Bures formula.  These
are useful geometric inputs, but do not identify the radial line from the
metric or prove automatic trace preservation. -/

noncomputable section
open scoped MatrixOrder ComplexOrder
namespace Bures

theorem fidelityRoot_smul_left (A B : PositiveDefinite n) {c : ℝ} (hc : 0 < c) :
    fidelityRoot (c • A.val) B.val = Real.sqrt c * fidelityRoot A.val B.val := by
  calc
    fidelityRoot (c • A.val) B.val = fidelityRoot B.val (c • A.val) := by
      simpa only [scale] using fidelityRoot_comm (scale c hc A) B
    _ = Real.sqrt c * fidelityRoot B.val A.val := fidelityRoot_smul_right B A hc.le
    _ = Real.sqrt c * fidelityRoot A.val B.val := by rw [fidelityRoot_comm]

/-- Scaling both matrices gives the exact quadratic cone law. -/
theorem distance_scale_pair_sq (A B : PositiveDefinite n)
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    distance (scale c hc A) (scale d hd B) ^ 2 =
      c * tr A.val + d * tr B.val -
        2 * (Real.sqrt c * Real.sqrt d * fidelityRoot A.val B.val) := by
  rw [distance_sq]
  change tr (c • A.val) + tr (d • B.val) -
    2 * fidelityRoot (c • A.val) (d • B.val) = _
  rw [tr_smul, tr_smul]
  have hfid : fidelityRoot (c • A.val) (d • B.val) =
      Real.sqrt c * Real.sqrt d * fidelityRoot A.val B.val := by
    calc
      _ = Real.sqrt c * fidelityRoot A.val (d • B.val) := by
        simpa only [scale] using fidelityRoot_smul_left A (scale d hd B) hc
      _ = _ := by rw [fidelityRoot_smul_right A B hd.le]; ring
  rw [hfid]

/-- Positive scaling acts by the expected metric homothety. -/
theorem distance_scale_pair (A B : PositiveDefinite n) {c : ℝ} (hc : 0 < c) :
    distance (scale c hc A) (scale c hc B) = Real.sqrt c * distance A B := by
  have hs : distance (scale c hc A) (scale c hc B) ^ 2 =
      (Real.sqrt c * distance A B) ^ 2 := by
    rw [distance_scale_pair_sq A B hc hc, mul_pow, distance_sq,
      ← pow_two (Real.sqrt c), Real.sq_sqrt hc.le]
    ring
  have hn := distance_nonneg (scale c hc A) (scale c hc B)
  have hm := mul_nonneg (Real.sqrt_nonneg c) (distance_nonneg A B)
  nlinarith

#print axioms fidelityRoot_smul_left
#print axioms distance_scale_pair_sq
#print axioms distance_scale_pair

end Bures

import BuresFourPoint
import BuresConeGeometry

/-! The four-point obstruction persists at every positive scale near the cone apex. -/

noncomputable section
open scoped MatrixOrder ComplexOrder
namespace Bures

def psdScale (c : ℝ) (hc : 0 ≤ c) (A : PSD n) : PSD n :=
  ⟨c • A.val, Matrix.nonneg_iff_posSemidef.mp
    (smul_nonneg hc (Matrix.nonneg_iff_posSemidef.mpr A.property))⟩

private theorem sandwich_psd (A B : PSD n) :
    (matrixSqrt A.val * B.val * matrixSqrt A.val).PosSemidef := by
  have h := B.property.mul_mul_conjTranspose_same (matrixSqrt A.val)
  have hs := (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg A.val)).isHermitian
  simpa only [hs.eq] using h

private theorem fidelityRoot_smul_right_psd (A B : PSD n) {c : ℝ} (hc : 0 ≤ c) :
    fidelityRoot A.val (c • B.val) = Real.sqrt c * fidelityRoot A.val B.val := by
  unfold fidelityRoot
  rw [mul_smul_comm, smul_mul_assoc, matrixSqrt_smul (sandwich_psd A B) hc,
    tr_smul]

private theorem fidelityRoot_smul_left_psd (A B : PSD n) {c : ℝ} (hc : 0 ≤ c) :
    fidelityRoot (c • A.val) B.val = Real.sqrt c * fidelityRoot A.val B.val := by
  calc
    fidelityRoot (c • A.val) B.val = fidelityRoot B.val (c • A.val) := by
      have h := psdDistance_comm (psdScale c hc A) B
      have hr := psdDistance_sq (psdScale c hc A) B
      have hs := psdDistance_sq B (psdScale c hc A)
      change psdDistance (psdScale c hc A) B ^ 2 = tr (c • A.val) + tr B.val -
        2 * fidelityRoot (c • A.val) B.val at hr
      change psdDistance B (psdScale c hc A) ^ 2 = tr B.val + tr (c • A.val) -
        2 * fidelityRoot B.val (c • A.val) at hs
      rw [h] at hr
      rw [hs] at hr
      linarith
    _ = Real.sqrt c * fidelityRoot B.val A.val := fidelityRoot_smul_right_psd B A hc
    _ = Real.sqrt c * fidelityRoot A.val B.val := by
      have h := psdDistance_comm A B
      have hr := psdDistance_sq A B
      have hs := psdDistance_sq B A
      rw [h, hs] at hr
      rw [add_comm (tr B.val) (tr A.val)] at hr
      rw [show fidelityRoot B.val A.val = fidelityRoot A.val B.val by linarith]

theorem psdDistance_scale_pair (A B : PSD n) {c : ℝ} (hc : 0 ≤ c) :
    psdDistance (psdScale c hc A) (psdScale c hc B) =
      Real.sqrt c * psdDistance A B := by
  have hsq : psdDistance (psdScale c hc A) (psdScale c hc B) ^ 2 =
      (Real.sqrt c * psdDistance A B) ^ 2 := by
    rw [psdDistance_sq, mul_pow, psdDistance_sq]
    change tr (c • A.val) + tr (c • B.val) -
      2 * fidelityRoot (c • A.val) (c • B.val) = _
    rw [tr_smul, tr_smul]
    have hleft := fidelityRoot_smul_left_psd A (psdScale c hc B) hc
    change fidelityRoot (c • A.val) (c • B.val) =
      Real.sqrt c * fidelityRoot A.val (c • B.val) at hleft
    rw [hleft]
    change c * tr A.val + c * tr B.val -
      2 * (Real.sqrt c * fidelityRoot A.val (c • B.val)) = _
    rw [fidelityRoot_smul_right_psd A B hc, Real.sq_sqrt hc]
    rw [← mul_assoc (Real.sqrt c) (Real.sqrt c) (fidelityRoot A.val B.val),
      Real.mul_self_sqrt hc]
    ring
  have h₁ := psdDistance_nonneg (psdScale c hc A) (psdScale c hc B)
  have h₂ := mul_nonneg (Real.sqrt_nonneg c) (psdDistance_nonneg A B)
  nlinarith

theorem psdDistance_scale_zero (A : PSD n) {c : ℝ} (hc : 0 ≤ c) :
    psdDistance (psdScale c hc A) psdZero =
      Real.sqrt c * psdDistance A psdZero := by
  have hz : psdScale c hc (psdZero : PSD n) = psdZero := by
    apply Subtype.ext
    change (c • (0 : Mat n)) = 0
    ext i j
    simp [Matrix.smul_apply]
  simpa only [hz] using psdDistance_scale_pair A (psdZero : PSD n) hc

/-- Every quadratic scaling ray converges to the PSD apex in the ordinary
matrix topology (equivalently, the PSD Bures metric topology). -/
theorem tendsto_psdScale_sq_zero (A : PSD n) :
    Filter.Tendsto (fun t : ℝ => psdScale (t ^ 2) (sq_nonneg t) A)
      (nhds (0 : ℝ)) (nhds (psdZero : PSD n)) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have h : Filter.Tendsto (fun t : ℝ => ((t ^ 2 : ℝ) : ℂ) * A.val i j)
      (nhds (0 : ℝ)) (nhds (0 : ℂ)) := by
    convert ((Complex.continuous_ofReal.comp
      (continuous_id.pow 2)).mul continuous_const).tendsto 0 using 1
    simp
  simpa only [psdScale, psdZero, Matrix.smul_apply, Complex.real_smul,
    smul_eq_mul] using h

theorem four_point_non_euclidean_at_scale {c : ℝ} (hc : 0 < c) :
    ∃ A B C D : PSD 2,
      0 < psdDistance A C ^ 2 + psdDistance B D ^ 2 -
        psdDistance A B ^ 2 - psdDistance B C ^ 2 -
        psdDistance C D ^ 2 - psdDistance D A ^ 2 := by
  obtain ⟨A, B, C, D, h⟩ := four_point_non_euclidean
  refine ⟨psdScale c hc.le A, psdScale c hc.le B,
    psdScale c hc.le C, psdScale c hc.le D, ?_⟩
  simp only [psdDistance_scale_pair (hc := hc.le), mul_pow, Real.sq_sqrt hc.le]
  nlinarith [mul_pos hc h]

/-- The failure of the Hilbert four-point inequality occurs in every
metric neighborhood of the apex. This gives a precise target for any
attempt to prove that an isometric extension cannot send the apex to a
smooth interior point. -/
theorem four_point_non_euclidean_near_zero (ε : ℝ) (hε : 0 < ε) :
    ∃ A B C D : PSD 2,
      psdDistance A psdZero < ε ∧ psdDistance B psdZero < ε ∧
      psdDistance C psdZero < ε ∧ psdDistance D psdZero < ε ∧
      0 < psdDistance A C ^ 2 + psdDistance B D ^ 2 -
        psdDistance A B ^ 2 - psdDistance B C ^ 2 -
        psdDistance C D ^ 2 - psdDistance D A ^ 2 := by
  obtain ⟨A, B, C, D, hbad⟩ := four_point_non_euclidean
  let rA := psdDistance A psdZero
  let rB := psdDistance B psdZero
  let rC := psdDistance C psdZero
  let rD := psdDistance D psdZero
  let R := max (max rA rB) (max rC rD)
  have hR : 0 ≤ R := by
    have ha : 0 ≤ rA := psdDistance_nonneg A psdZero
    exact le_trans ha (le_trans (le_max_left _ _) (le_max_left _ _))
  let δ := ε / (1 + R)
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hden : 0 < 1 + R := by linarith
  let c := δ ^ 2
  have hc : 0 < c := pow_pos hδ _
  have hsqrt : Real.sqrt c = δ := by
    dsimp [c]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hδ]
  have hsmall (r : ℝ) (hr : r ≤ R) : δ * r < ε := by
    have hmul : ε * r < ε * (1 + R) := by
      apply mul_lt_mul_of_pos_left _ hε
      linarith
    have hrew : δ * r = (ε * r) / (1 + R) := by
      dsimp [δ]
      ring
    rw [hrew]
    exact (div_lt_iff₀ hden).mpr hmul
  have hA : rA ≤ R := le_trans (le_max_left _ _) (le_max_left _ _)
  have hB : rB ≤ R := le_trans (le_max_right _ _) (le_max_left _ _)
  have hC : rC ≤ R := le_trans (le_max_left _ _) (le_max_right _ _)
  have hD : rD ≤ R := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨psdScale c hc.le A, psdScale c hc.le B,
    psdScale c hc.le C, psdScale c hc.le D, ?_, ?_, ?_, ?_, ?_⟩
  · rw [psdDistance_scale_zero, hsqrt]
    exact hsmall rA hA
  · rw [psdDistance_scale_zero, hsqrt]
    exact hsmall rB hB
  · rw [psdDistance_scale_zero, hsqrt]
    exact hsmall rC hC
  · rw [psdDistance_scale_zero, hsqrt]
    exact hsmall rD hD
  · simp only [psdDistance_scale_pair (hc := hc.le), mul_pow, hsqrt]
    nlinarith [mul_pos hc hbad]

#print axioms psdDistance_scale_pair
#print axioms tendsto_psdScale_sq_zero
#print axioms four_point_non_euclidean_at_scale
#print axioms four_point_non_euclidean_near_zero

end Bures

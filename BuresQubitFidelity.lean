import BuresPSD

/-! Elementary two-by-two algebra toward a boundary tangent formula. -/

noncomputable section
open scoped MatrixOrder ComplexOrder
open Matrix
namespace Bures

private theorem trace_sq_det_identity (M : Mat 2) :
    (Matrix.trace M) ^ 2 = Matrix.trace (M * M) + 2 * Matrix.det M := by
  simp only [Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two]
  ring

private theorem complex_trace_eq_real (M : Mat 2) (hM : M.PosSemidef) :
    Matrix.trace M = (tr M : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa using (Complex.nonneg_iff.mp hM.trace_nonneg).2.symm

private theorem complex_det_eq_real (M : Mat 2) (hM : M.PosSemidef) :
    M.det = ((M.det.re : ℝ) : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa using (Complex.nonneg_iff.mp hM.det_nonneg).2.symm

/-- Squared qubit fidelity in terms of trace and determinant. -/
theorem fidelityRoot_sq_qubit (A B : PSD 2) :
    fidelityRoot A.val B.val ^ 2 =
      tr (A.val * B.val) + 2 * Real.sqrt (A.val.det.re * B.val.det.re) := by
  let X := matrixSqrt A.val
  let C := X * B.val * X
  let S := matrixSqrt C
  have hX : X.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg _)
  have hC : C.PosSemidef := by
    have h := B.property.mul_mul_conjTranspose_same X
    simpa only [hX.isHermitian.eq] using h
  have hS : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg _)
  have hSS : S * S = C := matrixSqrt_mul_self hC
  have hXX : X * X = A.val := matrixSqrt_mul_self A.property
  have htrace : tr C = tr (A.val * B.val) := by
    dsimp [C]
    rw [tr_mul_comm, ← mul_assoc, hXX]
  have hdetC : C.det = A.val.det * B.val.det := by
    calc
      C.det = X.det * B.val.det * X.det := by simp [C, Matrix.det_mul]
      _ = (X * X).det * B.val.det := by rw [Matrix.det_mul]; ring
      _ = A.val.det * B.val.det := by rw [hXX]
  have hSdet : S.det = RCLike.sqrt C.det := by
    exact hC.det_sqrt
  have hkey := trace_sq_det_identity S
  rw [complex_trace_eq_real S hS, hSS, complex_trace_eq_real C hC] at hkey
  change (↑(fidelityRoot A.val B.val) : ℂ) ^ 2 =
      ↑(tr C) + 2 * S.det at hkey
  rw [hSdet, hdetC, complex_det_eq_real A.val A.property,
    complex_det_eq_real B.val B.property] at hkey
  have hreal := congrArg Complex.re hkey
  rw [htrace] at hreal
  simpa [RCLike.sqrt_complex, ← Complex.ofReal_mul, ← Complex.ofReal_pow,
    Complex.re_sqrt_ofReal] using hreal

/-- Lower-triangular Gram coordinates for the qubit cone. -/
def qubitCholesky (x : ℝ) (v : ℂ) (w : ℝ) : Mat 2 :=
  !![(x : ℂ), 0; v, (w : ℂ)]

def qubitGram (x : ℝ) (v : ℂ) (w : ℝ) : PSD 2 :=
  ⟨qubitCholesky x v w * (qubitCholesky x v w)ᴴ,
    Matrix.posSemidef_self_mul_conjTranspose _⟩

theorem qubitGram_entries (x : ℝ) (v : ℂ) (w : ℝ) :
    (qubitGram x v w).val =
      !![((x : ℂ) * x), (x : ℂ) * star v;
         v * x, v * star v + (w : ℂ) * w] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [qubitGram, qubitCholesky, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Fin.sum_univ_two, Matrix.conjTranspose_apply]

theorem qubitGram_det (x : ℝ) (v : ℂ) (w : ℝ) :
    (qubitGram x v w).val.det = ((x * w) ^ 2 : ℝ) := by
  rw [qubitGram_entries, Matrix.det_fin_two]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem qubitGram_trace (x : ℝ) (v : ℂ) (w : ℝ) :
    tr (qubitGram x v w).val = x ^ 2 + Complex.normSq v + w ^ 2 := by
  rw [qubitGram_entries]
  simp [tr, Matrix.trace_fin_two, Complex.normSq_apply]
  ring

theorem qubitGram_covers_pos_first_diag (A : PSD 2)
    (h00 : 0 < (A.val 0 0).re) :
    ∃ x : ℝ, ∃ v : ℂ, ∃ w : ℝ,
      0 < x ∧ 0 ≤ w ∧ A = qubitGram x v w := by
  let a : ℝ := (A.val 0 0).re
  let x : ℝ := Real.sqrt a
  let d : ℝ := A.val.det.re
  let v : ℂ := A.val 1 0 / (x : ℂ)
  let w : ℝ := Real.sqrt d / x
  have hx : 0 < x := Real.sqrt_pos.2 h00
  have hdet : 0 ≤ d := (Complex.nonneg_iff.mp A.property.det_nonneg).1
  have hw : 0 ≤ w := div_nonneg (Real.sqrt_nonneg _) hx.le
  refine ⟨x, v, w, hx, hw, ?_⟩
  have hdiag00 : A.val 0 0 = (a : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using (Complex.nonneg_iff.mp (A.property.diag_nonneg (i := 0))).2.symm
  have hdiag11 : A.val 1 1 = ((A.val 1 1).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using (Complex.nonneg_iff.mp (A.property.diag_nonneg (i := 1))).2.symm
  have hdetc : A.val.det = (d : ℂ) := complex_det_eq_real A.val A.property
  have hsym : A.val 0 1 = star (A.val 1 0) := by
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_apply] using
      (congrArg (fun M : Mat 2 => M 0 1) A.property.isHermitian.eq).symm
  have hxsq : x ^ 2 = a := Real.sq_sqrt h00.le
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
  have hwsq : w ^ 2 = d / a := by
    dsimp [w]
    rw [div_pow, Real.sq_sqrt hdet, hxsq]
  apply Subtype.ext
  rw [qubitGram_entries]
  ext i j
  fin_cases i <;> fin_cases j
  · change A.val 0 0 = (x : ℂ) * x
    rw [hdiag00]
    push_cast [← hxsq]
    ring
  · change A.val 0 1 = (x : ℂ) * star v
    rw [hsym]
    simp [v, Complex.conj_ofReal]
    field_simp [hxc]
  · change A.val 1 0 = v * (x : ℂ)
    simp [v, hxc]
  · change A.val 1 1 = v * star v + (w : ℂ) * w
    rw [hdiag11]
    have hdetform : (d : ℂ) = (a : ℂ) * A.val 1 1 -
        A.val 0 1 * A.val 1 0 := by
      rw [← hdetc, Matrix.det_fin_two, hdiag00]
    have ha : (a : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt h00)
    simp only [v, w]
    rw [hdiag11] at hdetform
    -- The lower-right entry is the Schur-complement identity.
    simp only [Complex.star_def]
    simp only [map_div₀, Complex.conj_ofReal]
    have hwsqc : ((Real.sqrt d / x : ℝ) : ℂ) ^ 2 = ((d / a : ℝ) : ℂ) := by
      exact_mod_cast hwsq
    rw [← pow_two, hwsqc]
    rw [hsym] at hdetform
    have hxsqc : (x : ℂ) ^ 2 = (a : ℂ) := by exact_mod_cast hxsq
    field_simp [hxc, ha]
    rw [hxsqc]
    have hmul : (a : ℂ) * ((d / a : ℝ) : ℂ) = (d : ℂ) := by
      exact_mod_cast (mul_div_cancel₀ d (ne_of_gt h00))
    rw [hmul]
    simp only [starRingEnd_apply]
    linear_combination -hdetform

theorem qubitGram_fidelity_sq (x y w z : ℝ) (v u : ℂ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hw : 0 ≤ w) (hz : 0 ≤ z) :
    fidelityRoot (qubitGram x v w).val (qubitGram y u z).val ^ 2 =
      tr ((qubitGram x v w).val * (qubitGram y u z).val) +
        2 * (x * w) * (y * z) := by
  rw [fidelityRoot_sq_qubit, qubitGram_det, qubitGram_det]
  simp only [Complex.ofReal_re]
  have hxw : 0 ≤ x * w := mul_nonneg hx hw
  have hyz : 0 ≤ y * z := mul_nonneg hy hz
  rw [← mul_pow, Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg hxw hyz)]
  ring

theorem qubitGram_fidelity_eq_sqrt (x y w z : ℝ) (v u : ℂ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hw : 0 ≤ w) (hz : 0 ≤ z) :
    fidelityRoot (qubitGram x v w).val (qubitGram y u z).val =
      Real.sqrt (tr ((qubitGram x v w).val * (qubitGram y u z).val) +
        2 * (x * w) * (y * z)) := by
  have hsq := qubitGram_fidelity_sq x y w z v u hx hy hw hz
  have hnonneg : 0 ≤ fidelityRoot (qubitGram x v w).val (qubitGram y u z).val := by
    unfold fidelityRoot
    apply tr_nonneg
    exact Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg _)
  rw [← hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg]

theorem qubitGram_distance_sq (x y w z : ℝ) (v u : ℂ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hw : 0 ≤ w) (hz : 0 ≤ z) :
    psdDistance (qubitGram x v w) (qubitGram y u z) ^ 2 =
      x ^ 2 + Complex.normSq v + w ^ 2 +
      (y ^ 2 + Complex.normSq u + z ^ 2) -
      2 * Real.sqrt (tr ((qubitGram x v w).val * (qubitGram y u z).val) +
        2 * (x * w) * (y * z)) := by
  rw [psdDistance_sq, qubitGram_trace, qubitGram_trace,
    qubitGram_fidelity_eq_sqrt x y w z v u hx hy hw hz]

/-- The qubit fidelity polynomial is a sum of two complex squared magnitudes. -/
theorem qubitGram_fidelity_polynomial (x y w z : ℝ) (v u : ℂ) :
    tr ((qubitGram x v w).val * (qubitGram y u z).val) +
      2 * (x * w) * (y * z) =
      Complex.normSq ((x * y + w * z : ℝ) + star v * u) +
      Complex.normSq (v * (z : ℂ) - (w : ℂ) * u) := by
  rw [qubitGram_entries, qubitGram_entries]
  simp [tr, Matrix.trace_fin_two,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  ring

/-- The real Frobenius pairing of two triangular lifts. -/
def qubitLiftPairing (x y w z : ℝ) (v u : ℂ) : ℝ :=
  x * y + w * z + (star v * u).re

/-- The quartic error in the rank-one Bures tangent. -/
def qubitLiftDefect (w z : ℝ) (v u : ℂ) : ℝ :=
  (star v * u).im ^ 2 + Complex.normSq (v * (z : ℂ) - (w : ℂ) * u)

theorem qubitLiftDefect_nonneg (w z : ℝ) (v u : ℂ) :
    0 ≤ qubitLiftDefect w z v u := by
  unfold qubitLiftDefect
  exact add_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)

theorem qubitGram_fidelity_sq_decomposition (x y w z : ℝ) (v u : ℂ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hw : 0 ≤ w) (hz : 0 ≤ z) :
    fidelityRoot (qubitGram x v w).val (qubitGram y u z).val ^ 2 =
      qubitLiftPairing x y w z v u ^ 2 + qubitLiftDefect w z v u := by
  rw [qubitGram_fidelity_sq x y w z v u hx hy hw hz,
    qubitGram_fidelity_polynomial]
  unfold qubitLiftPairing qubitLiftDefect
  simp [Complex.normSq_apply, Complex.add_re, Complex.add_im]
  ring

theorem qubitGram_euclidean_sq (x y w z : ℝ) (v u : ℂ) :
    tr (qubitGram x v w).val + tr (qubitGram y u z).val -
      2 * qubitLiftPairing x y w z v u =
      (x - y) ^ 2 + Complex.normSq (v - u) + (w - z) ^ 2 := by
  rw [qubitGram_trace, qubitGram_trace]
  unfold qubitLiftPairing
  simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re]
  ring

theorem qubitGram_distance_sq_defect (x y w z : ℝ) (v u : ℂ) :
    psdDistance (qubitGram x v w) (qubitGram y u z) ^ 2 =
      (x - y) ^ 2 + Complex.normSq (v - u) + (w - z) ^ 2 -
        2 * (fidelityRoot (qubitGram x v w).val (qubitGram y u z).val -
          qubitLiftPairing x y w z v u) := by
  rw [psdDistance_sq, ← qubitGram_euclidean_sq]
  ring

/-- At positive lift pairing, the deviation from the Euclidean metric is
controlled exactly by the nonnegative quartic defect. -/
theorem qubitGram_distance_sq_error_bound (x y w z : ℝ) (v u : ℂ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hw : 0 ≤ w) (hz : 0 ≤ z)
    (hpair : 0 < qubitLiftPairing x y w z v u) :
    0 ≤ (x - y) ^ 2 + Complex.normSq (v - u) + (w - z) ^ 2 -
      psdDistance (qubitGram x v w) (qubitGram y u z) ^ 2 ∧
    (x - y) ^ 2 + Complex.normSq (v - u) + (w - z) ^ 2 -
      psdDistance (qubitGram x v w) (qubitGram y u z) ^ 2 ≤
        2 * qubitLiftDefect w z v u / qubitLiftPairing x y w z v u := by
  let F := fidelityRoot (qubitGram x v w).val (qubitGram y u z).val
  let α := qubitLiftPairing x y w z v u
  let β := qubitLiftDefect w z v u
  have hF : 0 ≤ F := by
    dsimp [F, fidelityRoot]
    apply tr_nonneg
    exact Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg _)
  have hβ : 0 ≤ β := qubitLiftDefect_nonneg w z v u
  have hsq : F ^ 2 = α ^ 2 + β :=
    qubitGram_fidelity_sq_decomposition x y w z v u hx hy hw hz
  have hαF : α ≤ F := by nlinarith
  have hfact : (F - α) * (F + α) = β := by nlinarith
  have hbound : F - α ≤ β / α := by
    apply (le_div_iff₀ hpair).2
    nlinarith
  rw [qubitGram_distance_sq_defect]
  constructor
  · dsimp [F, α] at hαF
    nlinarith
  · dsimp [F, α, β] at hbound
    calc
      _ = 2 * (fidelityRoot (qubitGram x v w).val
        (qubitGram y u z).val - qubitLiftPairing x y w z v u) := by ring
      _ ≤ 2 * (qubitLiftDefect w z v u / qubitLiftPairing x y w z v u) :=
        mul_le_mul_of_nonneg_left hbound (by norm_num)
      _ = _ := by ring

/-- From a diagonal rank-one base, Cholesky coordinates measure the Bures
distance exactly, including at the singular boundary. -/
theorem qubitGram_distance_sq_from_diagonal_rank_one (x₀ x w : ℝ) (v : ℂ)
    (hx₀ : 0 ≤ x₀) (hx : 0 ≤ x) (hw : 0 ≤ w) :
    psdDistance (qubitGram x₀ 0 0) (qubitGram x v w) ^ 2 =
      (x₀ - x) ^ 2 + Complex.normSq v + w ^ 2 := by
  have hsq := qubitGram_fidelity_sq_decomposition x₀ x 0 w (0 : ℂ) v
    hx₀ hx le_rfl hw
  simp [qubitLiftPairing, qubitLiftDefect] at hsq
  have hF : 0 ≤ fidelityRoot (qubitGram x₀ 0 0).val (qubitGram x v w).val := by
    unfold fidelityRoot
    apply tr_nonneg
    exact Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg _)
  have hprod : 0 ≤ x₀ * x := mul_nonneg hx₀ hx
  have hfeq : fidelityRoot (qubitGram x₀ 0 0).val
      (qubitGram x v w).val = x₀ * x := by nlinarith
  rw [qubitGram_distance_sq_defect, hfeq]
  simp [qubitLiftPairing]

private theorem normSq_sub_le_two (a b : ℂ) :
    Complex.normSq (a - b) ≤ 2 * (Complex.normSq a + Complex.normSq b) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  nlinarith [sq_nonneg (a.re + b.re), sq_nonneg (a.im + b.im)]

theorem qubitLiftDefect_le_quartic (w z : ℝ) (v u : ℂ) :
    qubitLiftDefect w z v u ≤
      Complex.normSq v * Complex.normSq u +
        2 * (z ^ 2 * Complex.normSq v + w ^ 2 * Complex.normSq u) := by
  have h₁ := Complex.im_sq_le_normSq (star v * u)
  rw [Complex.normSq_mul] at h₁
  simp [Complex.normSq_conj] at h₁
  have h₁' : (star v * u).im ^ 2 ≤ Complex.normSq v * Complex.normSq u := by
    simpa [pow_two, Complex.mul_im, Complex.conj_re, Complex.conj_im] using h₁
  have h₂ := normSq_sub_le_two (v * (z : ℂ)) ((w : ℂ) * u)
  simp only [Complex.normSq_mul, Complex.normSq_ofReal] at h₂
  unfold qubitLiftDefect
  nlinarith [h₁', h₂]

theorem qubitLiftDefect_le_five_pow_four (δ w z : ℝ) (v u : ℂ)
    (hv : Complex.normSq v ≤ δ ^ 2) (hu : Complex.normSq u ≤ δ ^ 2)
    (hw : w ^ 2 ≤ δ ^ 2) (hz : z ^ 2 ≤ δ ^ 2) :
    qubitLiftDefect w z v u ≤ 5 * δ ^ 4 := by
  have hδ : 0 ≤ δ ^ 2 := sq_nonneg _
  have hvu : Complex.normSq v * Complex.normSq u ≤ δ ^ 4 := by
    calc
      _ ≤ δ ^ 2 * δ ^ 2 :=
        mul_le_mul hv hu (Complex.normSq_nonneg _) hδ
      _ = δ ^ 4 := by ring
  have hzv : z ^ 2 * Complex.normSq v ≤ δ ^ 4 := by
    calc
      _ ≤ δ ^ 2 * δ ^ 2 :=
        mul_le_mul hz hv (Complex.normSq_nonneg _) hδ
      _ = δ ^ 4 := by ring
  have hwu : w ^ 2 * Complex.normSq u ≤ δ ^ 4 := by
    calc
      _ ≤ δ ^ 2 * δ ^ 2 :=
        mul_le_mul hw hu (Complex.normSq_nonneg _) hδ
      _ = δ ^ 4 := by ring
  have hdef := qubitLiftDefect_le_quartic w z v u
  linarith

theorem qubitLiftPairing_lower (x y w z : ℝ) (v u : ℂ) :
    x * y + w * z - (Complex.normSq v + Complex.normSq u) / 2 ≤
      qubitLiftPairing x y w z v u := by
  have hsum := Complex.normSq_nonneg (v + u)
  rw [Complex.normSq_add] at hsum
  have hre : (v * star u).re = (star v * u).re := by
    simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  simp only [starRingEnd_apply] at hsum
  rw [hre] at hsum
  unfold qubitLiftPairing
  linarith

end Bures

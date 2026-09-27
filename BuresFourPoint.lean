import BuresPSD
import BuresRadial
import Mathlib.Analysis.InnerProductSpace.Basic

/-! A four-point obstruction to Hilbert embeddability of the literal Bures cone. -/

noncomputable section
open scoped MatrixOrder ComplexOrder Matrix.Norms.Frobenius InnerProductSpace
namespace Bures
set_option maxRecDepth 2048

private def q0 : Mat 2 := !![1, 0; 0, 0]
private def q1 : Mat 2 := !![(1/2 : ℂ), 1/2; 1/2, 1/2]
private def q2 : Mat 2 := !![0, 0; 0, 1]
private def q3 : Mat 2 := !![(1/2 : ℂ), -1/2; -1/2, 1/2]

private theorem q0_gram : q0 * q0.conjTranspose = q0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [q0, Matrix.mul_apply, Fin.sum_univ_two]

private theorem q1_gram : q1 * q1.conjTranspose = q1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [q1, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.conjTranspose_apply] <;> norm_num

private theorem q2_gram : q2 * q2.conjTranspose = q2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [q2, Matrix.mul_apply, Fin.sum_univ_two]

private theorem q3_gram : q3 * q3.conjTranspose = q3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [q3, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.conjTranspose_apply] <;> norm_num

private def Q0 : PSD 2 := ⟨q0, q0_gram ▸ Matrix.posSemidef_self_mul_conjTranspose q0⟩
private def Q1 : PSD 2 := ⟨q1, q1_gram ▸ Matrix.posSemidef_self_mul_conjTranspose q1⟩
private def Q2 : PSD 2 := ⟨q2, q2_gram ▸ Matrix.posSemidef_self_mul_conjTranspose q2⟩
private def Q3 : PSD 2 := ⟨q3, q3_gram ▸ Matrix.posSemidef_self_mul_conjTranspose q3⟩

private theorem q0_sq : q0 * q0 = q0 := by
  have hP : q0.PosSemidef := Q0.property
  simpa only [hP.isHermitian.eq] using q0_gram

private theorem q1_sq : q1 * q1 = q1 := by
  have hP : q1.PosSemidef := Q1.property
  simpa only [hP.isHermitian.eq] using q1_gram

private theorem q2_sq : q2 * q2 = q2 := by
  have hP : q2.PosSemidef := Q2.property
  simpa only [hP.isHermitian.eq] using q2_gram

private theorem q3_sq : q3 * q3 = q3 := by
  have hP : q3.PosSemidef := Q3.property
  simpa only [hP.isHermitian.eq] using q3_gram

private theorem tr_q0 : tr q0 = 1 := by norm_num [tr, q0, Matrix.trace]
private theorem tr_q1 : tr q1 = 1 := by norm_num [tr, q1, Matrix.trace]
private theorem tr_q2 : tr q2 = 1 := by norm_num [tr, q2, Matrix.trace]
private theorem tr_q3 : tr q3 = 1 := by norm_num [tr, q3, Matrix.trace]

private theorem fidelity_proj {P Q : Mat 2} (hP : P.PosSemidef)
    (hPP : P * P = P) (htr : tr P = 1) {c : ℝ} (hc : 0 ≤ c)
    (hPQ : P * Q * P = c • P) : fidelityRoot P Q = Real.sqrt c := by
  have hsP : matrixSqrt P = P := matrixSqrt_unique hP hPP
  rw [fidelityRoot, hsP, hPQ, matrixSqrt_smul hP hc, tr_smul, hsP, htr, mul_one]

private theorem q0_q1_q0 : q0 * q1 * q0 = (1/2 : ℝ) • q0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [q0, q1, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply] <;>
    norm_num

private theorem q0_q2_q0 : q0 * q2 * q0 = (0 : ℝ) • q0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [q0, q2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply] <;>
    norm_num

private theorem q0_q3_q0 : q0 * q3 * q0 = (1/2 : ℝ) • q0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [q0, q3, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply] <;>
    norm_num

private theorem q1_q2_q1 : q1 * q2 * q1 = (1/2 : ℝ) • q1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [q1, q2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply] <;>
    norm_num

private theorem q1_q3_q1 : q1 * q3 * q1 = (0 : ℝ) • q1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [q1, q3, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply] <;>
    norm_num

private theorem q2_q3_q2 : q2 * q3 * q2 = (1/2 : ℝ) • q2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [q2, q3, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply] <;>
    norm_num

private theorem fidelity_01 : fidelityRoot q0 q1 = Real.sqrt (1/2 : ℝ) :=
  fidelity_proj Q0.property q0_sq tr_q0 (by norm_num) q0_q1_q0

private theorem fidelity_02 : fidelityRoot q0 q2 = 0 := by
  simpa using fidelity_proj Q0.property q0_sq tr_q0 (by norm_num) q0_q2_q0

private theorem fidelity_03 : fidelityRoot q0 q3 = Real.sqrt (1/2 : ℝ) :=
  fidelity_proj Q0.property q0_sq tr_q0 (by norm_num) q0_q3_q0

private theorem fidelity_12 : fidelityRoot q1 q2 = Real.sqrt (1/2 : ℝ) :=
  fidelity_proj Q1.property q1_sq tr_q1 (by norm_num) q1_q2_q1

private theorem fidelity_13 : fidelityRoot q1 q3 = 0 := by
  simpa using fidelity_proj Q1.property q1_sq tr_q1 (by norm_num) q1_q3_q1

private theorem fidelity_23 : fidelityRoot q2 q3 = Real.sqrt (1/2 : ℝ) :=
  fidelity_proj Q2.property q2_sq tr_q2 (by norm_num) q2_q3_q2

private theorem sq_01 : psdDistance Q0 Q1 ^ 2 = 2 - 2 * Real.sqrt (1/2 : ℝ) := by
  rw [psdDistance_sq]
  change tr q0 + tr q1 - 2 * fidelityRoot q0 q1 = _
  rw [tr_q0, tr_q1, fidelity_01]
  ring

private theorem sq_02 : psdDistance Q0 Q2 ^ 2 = 2 := by
  rw [psdDistance_sq]
  change tr q0 + tr q2 - 2 * fidelityRoot q0 q2 = _
  rw [tr_q0, tr_q2, fidelity_02]
  ring

private theorem sq_03 : psdDistance Q0 Q3 ^ 2 = 2 - 2 * Real.sqrt (1/2 : ℝ) := by
  rw [psdDistance_sq]
  change tr q0 + tr q3 - 2 * fidelityRoot q0 q3 = _
  rw [tr_q0, tr_q3, fidelity_03]
  ring

private theorem sq_12 : psdDistance Q1 Q2 ^ 2 = 2 - 2 * Real.sqrt (1/2 : ℝ) := by
  rw [psdDistance_sq]
  change tr q1 + tr q2 - 2 * fidelityRoot q1 q2 = _
  rw [tr_q1, tr_q2, fidelity_12]
  ring

private theorem sq_13 : psdDistance Q1 Q3 ^ 2 = 2 := by
  rw [psdDistance_sq]
  change tr q1 + tr q3 - 2 * fidelityRoot q1 q3 = _
  rw [tr_q1, tr_q3, fidelity_13]
  ring

private theorem sq_23 : psdDistance Q2 Q3 ^ 2 = 2 - 2 * Real.sqrt (1/2 : ℝ) := by
  rw [psdDistance_sq]
  change tr q2 + tr q3 - 2 * fidelityRoot q2 q3 = _
  rw [tr_q2, tr_q3, fidelity_23]
  ring

/-- Four rank-one projections violate the squared-distance inequality required by
an isometric embedding of the Bures cone in a real Hilbert space. -/
theorem four_point_non_euclidean :
    ∃ A B C D : PSD 2,
      0 < psdDistance A C ^ 2 + psdDistance B D ^ 2 -
        psdDistance A B ^ 2 - psdDistance B C ^ 2 -
        psdDistance C D ^ 2 - psdDistance D A ^ 2 := by
  refine ⟨Q0, Q1, Q2, Q3, ?_⟩
  rw [sq_02, sq_13, sq_01, sq_12, sq_23, psdDistance_comm Q3 Q0, sq_03]
  have hs : (Real.sqrt (1/2 : ℝ)) ^ 2 = 1/2 :=
    Real.sq_sqrt (by norm_num)
  have hp : 0 ≤ Real.sqrt (1/2 : ℝ) := Real.sqrt_nonneg _
  nlinarith

/-- The opposite four-point inequality holds in every real Hilbert space. -/
theorem hilbert_four_point {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (a b c d : E) :
    dist a c ^ 2 + dist b d ^ 2 ≤
      dist a b ^ 2 + dist b c ^ 2 + dist c d ^ 2 + dist d a ^ 2 := by
  have h := sq_nonneg ‖a - b + c - d‖
  simp only [dist_eq_norm] at *
  have hi : ‖a - b + c - d‖ ^ 2 =
      ‖a - b‖ ^ 2 + ‖c - d‖ ^ 2 +
      2 * ⟪a - b, c - d⟫_ℝ := by
    calc
      _ = ‖(a - b) + (c - d)‖ ^ 2 := by congr 1; abel
      _ = _ := by rw [norm_add_sq_real]; ring
  rw [hi] at h
  simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right] at h ⊢
  -- Symmetry of the real inner product closes the four-point identity.
  nlinarith [real_inner_comm a b, real_inner_comm a c, real_inner_comm a d,
    real_inner_comm b c, real_inner_comm b d, real_inner_comm c d]

/-- The literal Bures cone of 2×2 positive semidefinite matrices cannot embed
isometrically in any real inner-product space. -/
theorem no_hilbert_embedding (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] :
    ¬ ∃ f : PSD 2 → E, ∀ A B, dist (f A) (f B) = psdDistance A B := by
  rintro ⟨f, hf⟩
  obtain ⟨A, B, C, D, hbad⟩ := four_point_non_euclidean
  have hgood := hilbert_four_point (f A) (f B) (f C) (f D)
  rw [hf A C, hf B D, hf A B, hf B C, hf C D, hf D A] at hgood
  linarith

#print axioms four_point_non_euclidean
#print axioms hilbert_four_point
#print axioms no_hilbert_embedding

end Bures

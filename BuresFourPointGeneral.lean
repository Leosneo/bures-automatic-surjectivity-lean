import BuresFourPoint

/-! Sparse four-point witnesses in every matrix size at least two. -/

noncomputable section
open scoped MatrixOrder ComplexOrder
namespace Bures

private def e (n : ℕ) (i j : Fin n) : Mat n := Matrix.single i j 1

private theorem e_mul_e {n : ℕ} (i j k l : Fin n) :
    e n i j * e n k l = if j = k then e n i l else 0 := by
  by_cases h : j = k
  · subst k
    simp [e, Matrix.single_mul_single_same]
  · simp [e, h, Matrix.single_mul_single_of_ne]

private theorem e_star {n : ℕ} (i j : Fin n) : (e n i j).conjTranspose = e n j i := by
  ext a b
  by_cases hi : i = b <;> by_cases hj : j = a <;>
    simp [e, Matrix.conjTranspose_apply, Matrix.single, hi, hj]

private def i0 (n : ℕ) (h : 2 ≤ n) : Fin n := ⟨0, by omega⟩
private def i1 (n : ℕ) (h : 2 ≤ n) : Fin n := ⟨1, by omega⟩
private theorem i0_ne_i1 (n : ℕ) (h : 2 ≤ n) : i0 n h ≠ i1 n h := by
  simp [i0, i1]

private def p0 (n : ℕ) (h : 2 ≤ n) : Mat n := e n (i0 n h) (i0 n h)
private def p1 (n : ℕ) (h : 2 ≤ n) : Mat n :=
  (1/2 : ℝ) • (e n (i0 n h) (i0 n h) + e n (i0 n h) (i1 n h) +
    e n (i1 n h) (i0 n h) + e n (i1 n h) (i1 n h))
private def p2 (n : ℕ) (h : 2 ≤ n) : Mat n := e n (i1 n h) (i1 n h)
private def p3 (n : ℕ) (h : 2 ≤ n) : Mat n :=
  (1/2 : ℝ) • (e n (i0 n h) (i0 n h) - e n (i0 n h) (i1 n h) -
    e n (i1 n h) (i0 n h) + e n (i1 n h) (i1 n h))

private theorem p0_gram (n : ℕ) (h : 2 ≤ n) :
    p0 n h * (p0 n h).conjTranspose = p0 n h := by
  simp [p0, e_star, e_mul_e]

private theorem p2_gram (n : ℕ) (h : 2 ≤ n) :
    p2 n h * (p2 n h).conjTranspose = p2 n h := by
  simp [p2, e_star, e_mul_e]

private theorem p1_star (n : ℕ) (h : 2 ≤ n) :
    (p1 n h).conjTranspose = p1 n h := by
  simp only [p1, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, e_star,
    star_trivial]
  abel

private theorem p1_sq (n : ℕ) (h : 2 ≤ n) : p1 n h * p1 n h = p1 n h := by
  simp only [p1, smul_mul_smul]
  simp only [add_mul, mul_add, e_mul_e,
    if_neg (i0_ne_i1 n h), if_neg (i0_ne_i1 n h).symm, add_zero]
  simp only [ite_true, zero_add]
  module

private theorem p3_star (n : ℕ) (h : 2 ≤ n) :
    (p3 n h).conjTranspose = p3 n h := by
  simp only [p3, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_sub, e_star, star_trivial]
  abel

private theorem p3_sq (n : ℕ) (h : 2 ≤ n) : p3 n h * p3 n h = p3 n h := by
  simp only [p3, smul_mul_smul]
  simp only [add_mul, mul_add, sub_mul, mul_sub, e_mul_e,
    if_neg (i0_ne_i1 n h), if_neg (i0_ne_i1 n h).symm, add_zero]
  simp only [ite_true, zero_add]
  module

private theorem p1_gram (n : ℕ) (h : 2 ≤ n) :
    p1 n h * (p1 n h).conjTranspose = p1 n h := by
  rw [p1_star]
  exact p1_sq n h

private theorem p3_gram (n : ℕ) (h : 2 ≤ n) :
    p3 n h * (p3 n h).conjTranspose = p3 n h := by
  rw [p3_star]
  exact p3_sq n h

private def P0 (n : ℕ) (h : 2 ≤ n) : PSD n :=
  ⟨p0 n h, p0_gram n h ▸ Matrix.posSemidef_self_mul_conjTranspose (p0 n h)⟩
private def P1 (n : ℕ) (h : 2 ≤ n) : PSD n :=
  ⟨p1 n h, p1_gram n h ▸ Matrix.posSemidef_self_mul_conjTranspose (p1 n h)⟩
private def P2 (n : ℕ) (h : 2 ≤ n) : PSD n :=
  ⟨p2 n h, p2_gram n h ▸ Matrix.posSemidef_self_mul_conjTranspose (p2 n h)⟩
private def P3 (n : ℕ) (h : 2 ≤ n) : PSD n :=
  ⟨p3 n h, p3_gram n h ▸ Matrix.posSemidef_self_mul_conjTranspose (p3 n h)⟩

private theorem tr_p0 (n : ℕ) (h : 2 ≤ n) : tr (p0 n h) = 1 := by
  simp [tr, p0, e, Matrix.trace_single_eq_same]

private theorem tr_p2 (n : ℕ) (h : 2 ≤ n) : tr (p2 n h) = 1 := by
  simp [tr, p2, e, Matrix.trace_single_eq_same]

private theorem tr_p1 (n : ℕ) (h : 2 ≤ n) : tr (p1 n h) = 1 := by
  rw [p1, tr_smul]
  simp [tr, e, Matrix.trace_add, Matrix.trace_single_eq_same,
    Matrix.trace_single_eq_of_ne, i0_ne_i1 n h, (i0_ne_i1 n h).symm]
  norm_num

private theorem tr_p3 (n : ℕ) (h : 2 ≤ n) : tr (p3 n h) = 1 := by
  rw [p3, tr_smul]
  simp [tr, e, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_single_eq_same,
    Matrix.trace_single_eq_of_ne, i0_ne_i1 n h, (i0_ne_i1 n h).symm]
  norm_num

private theorem p0_p1_p0 (n : ℕ) (h : 2 ≤ n) :
    p0 n h * p1 n h * p0 n h = (1/2 : ℝ) • p0 n h := by
  simp [p0, p1, mul_add, add_mul, e_mul_e, i0_ne_i1 n h,
    (i0_ne_i1 n h).symm]

private theorem p0_p2_p0 (n : ℕ) (h : 2 ≤ n) :
    p0 n h * p2 n h * p0 n h = (0 : ℝ) • p0 n h := by
  simp [p0, p2, e_mul_e, i0_ne_i1 n h, (i0_ne_i1 n h).symm] <;> module

private theorem p0_p3_p0 (n : ℕ) (h : 2 ≤ n) :
    p0 n h * p3 n h * p0 n h = (1/2 : ℝ) • p0 n h := by
  simp [p0, p3, mul_add, add_mul, mul_sub, sub_mul, e_mul_e,
    i0_ne_i1 n h, (i0_ne_i1 n h).symm]

private theorem p1_p2_p1 (n : ℕ) (h : 2 ≤ n) :
    p1 n h * p2 n h * p1 n h = (1/2 : ℝ) • p1 n h := by
  simp [p1, p2, mul_add, add_mul, e_mul_e, i0_ne_i1 n h,
    (i0_ne_i1 n h).symm] <;> module

private theorem p1_p3_p1 (n : ℕ) (h : 2 ≤ n) :
    p1 n h * p3 n h * p1 n h = (0 : ℝ) • p1 n h := by
  simp [p1, p3, mul_add, add_mul, mul_sub, sub_mul, e_mul_e,
    i0_ne_i1 n h, (i0_ne_i1 n h).symm] <;> module

private theorem p2_p3_p2 (n : ℕ) (h : 2 ≤ n) :
    p2 n h * p3 n h * p2 n h = (1/2 : ℝ) • p2 n h := by
  simp [p2, p3, mul_add, add_mul, mul_sub, sub_mul, e_mul_e,
    i0_ne_i1 n h, (i0_ne_i1 n h).symm]

private theorem p0_sq (n : ℕ) (h : 2 ≤ n) : p0 n h * p0 n h = p0 n h := by
  simp [p0, e_mul_e]

private theorem p2_sq (n : ℕ) (h : 2 ≤ n) : p2 n h * p2 n h = p2 n h := by
  simp [p2, e_mul_e]

private theorem fidelity_proj_n {n : ℕ} {P Q : Mat n} (hP : P.PosSemidef)
    (hPP : P * P = P) (htr : tr P = 1) {c : ℝ} (hc : 0 ≤ c)
    (hPQ : P * Q * P = c • P) : fidelityRoot P Q = Real.sqrt c := by
  have hsP : matrixSqrt P = P := matrixSqrt_unique hP hPP
  rw [fidelityRoot, hsP, hPQ, matrixSqrt_smul hP hc, tr_smul, hsP, htr, mul_one]

private theorem fidelity_01 (n : ℕ) (h : 2 ≤ n) :
    fidelityRoot (p0 n h) (p1 n h) = Real.sqrt (1/2 : ℝ) :=
  fidelity_proj_n (P0 n h).property (p0_sq n h) (tr_p0 n h)
    (by norm_num) (p0_p1_p0 n h)

private theorem fidelity_02 (n : ℕ) (h : 2 ≤ n) :
    fidelityRoot (p0 n h) (p2 n h) = 0 := by
  simpa using fidelity_proj_n (P0 n h).property (p0_sq n h) (tr_p0 n h)
    (by norm_num) (p0_p2_p0 n h)

private theorem fidelity_03 (n : ℕ) (h : 2 ≤ n) :
    fidelityRoot (p0 n h) (p3 n h) = Real.sqrt (1/2 : ℝ) :=
  fidelity_proj_n (P0 n h).property (p0_sq n h) (tr_p0 n h)
    (by norm_num) (p0_p3_p0 n h)

private theorem fidelity_12 (n : ℕ) (h : 2 ≤ n) :
    fidelityRoot (p1 n h) (p2 n h) = Real.sqrt (1/2 : ℝ) :=
  fidelity_proj_n (P1 n h).property (p1_sq n h) (tr_p1 n h)
    (by norm_num) (p1_p2_p1 n h)

private theorem fidelity_13 (n : ℕ) (h : 2 ≤ n) :
    fidelityRoot (p1 n h) (p3 n h) = 0 := by
  simpa using fidelity_proj_n (P1 n h).property (p1_sq n h) (tr_p1 n h)
    (by norm_num) (p1_p3_p1 n h)

private theorem fidelity_23 (n : ℕ) (h : 2 ≤ n) :
    fidelityRoot (p2 n h) (p3 n h) = Real.sqrt (1/2 : ℝ) :=
  fidelity_proj_n (P2 n h).property (p2_sq n h) (tr_p2 n h)
    (by norm_num) (p2_p3_p2 n h)

private theorem sq_unit_trace (A B : PSD n)
    (hA : tr A.val = 1) (hB : tr B.val = 1) :
    psdDistance A B ^ 2 = 2 - 2 * fidelityRoot A.val B.val := by
  rw [psdDistance_sq, hA, hB]
  ring

private theorem sq_01 (n : ℕ) (h : 2 ≤ n) :
    psdDistance (P0 n h) (P1 n h) ^ 2 = 2 - 2 * Real.sqrt (1/2 : ℝ) := by
  rw [sq_unit_trace (P0 n h) (P1 n h) (tr_p0 n h) (tr_p1 n h)]
  exact congrArg (fun x : ℝ => 2 - 2 * x) (fidelity_01 n h)

private theorem sq_02 (n : ℕ) (h : 2 ≤ n) :
    psdDistance (P0 n h) (P2 n h) ^ 2 = 2 := by
  rw [sq_unit_trace (P0 n h) (P2 n h) (tr_p0 n h) (tr_p2 n h)]
  change 2 - 2 * fidelityRoot (p0 n h) (p2 n h) = 2
  rw [fidelity_02]
  ring

private theorem sq_03 (n : ℕ) (h : 2 ≤ n) :
    psdDistance (P0 n h) (P3 n h) ^ 2 = 2 - 2 * Real.sqrt (1/2 : ℝ) := by
  rw [sq_unit_trace (P0 n h) (P3 n h) (tr_p0 n h) (tr_p3 n h)]
  exact congrArg (fun x : ℝ => 2 - 2 * x) (fidelity_03 n h)

private theorem sq_12 (n : ℕ) (h : 2 ≤ n) :
    psdDistance (P1 n h) (P2 n h) ^ 2 = 2 - 2 * Real.sqrt (1/2 : ℝ) := by
  rw [sq_unit_trace (P1 n h) (P2 n h) (tr_p1 n h) (tr_p2 n h)]
  exact congrArg (fun x : ℝ => 2 - 2 * x) (fidelity_12 n h)

private theorem sq_13 (n : ℕ) (h : 2 ≤ n) :
    psdDistance (P1 n h) (P3 n h) ^ 2 = 2 := by
  rw [sq_unit_trace (P1 n h) (P3 n h) (tr_p1 n h) (tr_p3 n h)]
  change 2 - 2 * fidelityRoot (p1 n h) (p3 n h) = 2
  rw [fidelity_13]
  ring

private theorem sq_23 (n : ℕ) (h : 2 ≤ n) :
    psdDistance (P2 n h) (P3 n h) ^ 2 = 2 - 2 * Real.sqrt (1/2 : ℝ) := by
  rw [sq_unit_trace (P2 n h) (P3 n h) (tr_p2 n h) (tr_p3 n h)]
  exact congrArg (fun x : ℝ => 2 - 2 * x) (fidelity_23 n h)

/-- Every literal Bures cone of matrix size at least two has a four-point
configuration that violates the Euclidean quadrilateral inequality. -/
theorem four_point_non_euclidean_any_size (n : ℕ) (h : 2 ≤ n) :
    ∃ A B C D : PSD n,
      0 < psdDistance A C ^ 2 + psdDistance B D ^ 2 -
        psdDistance A B ^ 2 - psdDistance B C ^ 2 -
        psdDistance C D ^ 2 - psdDistance D A ^ 2 := by
  refine ⟨P0 n h, P1 n h, P2 n h, P3 n h, ?_⟩
  rw [sq_02 n h, sq_13 n h, sq_01 n h, sq_12 n h, sq_23 n h,
    psdDistance_comm (P3 n h) (P0 n h), sq_03 n h]
  have hs : (Real.sqrt (1/2 : ℝ)) ^ 2 = 1/2 :=
    Real.sq_sqrt (by norm_num)
  have hp : 0 ≤ Real.sqrt (1/2 : ℝ) := Real.sqrt_nonneg _
  nlinarith

/-- Thus the literal Bures PSD cone cannot embed isometrically in any real
inner-product space, in every dimension at least two. -/
theorem no_hilbert_embedding_any_size (n : ℕ) (h : 2 ≤ n)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    ¬ ∃ f : PSD n → E, ∀ A B, dist (f A) (f B) = psdDistance A B := by
  rintro ⟨f, hf⟩
  obtain ⟨A, B, C, D, hbad⟩ := four_point_non_euclidean_any_size n h
  have hgood := hilbert_four_point (f A) (f B) (f C) (f D)
  rw [hf A C, hf B D, hf A B, hf B C, hf C D, hf D A] at hgood
  linarith

#print axioms four_point_non_euclidean_any_size
#print axioms no_hilbert_embedding_any_size

end Bures

import BuresQubitFidelity

/-! Unitary covariance of the literal semidefinite Bures distance and
normalization of nonzero rank-one qubit matrices. -/

noncomputable section
open scoped MatrixOrder ComplexOrder
open Matrix
namespace Bures

def unitaryConjPSD (U : Mat n) (A : PSD n) : PSD n :=
  ⟨U * A.val * Uᴴ, A.property.mul_mul_conjTranspose_same U⟩

theorem tr_unitaryConj (U M : Mat n) (hUl : Uᴴ * U = 1) :
    tr (U * M * Uᴴ) = tr M := by
  rw [tr_mul_comm, ← mul_assoc, hUl, one_mul]

theorem matrixSqrt_unitaryConj (U M : Mat n)
    (hUl : Uᴴ * U = 1) (_hUr : U * Uᴴ = 1) (hM : M.PosSemidef) :
    matrixSqrt (U * M * Uᴴ) = U * matrixSqrt M * Uᴴ := by
  have hR : (matrixSqrt M).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg M)
  apply matrixSqrt_unique (hR.mul_mul_conjTranspose_same U)
  calc
    (U * matrixSqrt M * Uᴴ) * (U * matrixSqrt M * Uᴴ) =
        U * (matrixSqrt M * (Uᴴ * U) * matrixSqrt M) * Uᴴ := by
      simp only [mul_assoc]
    _ = U * (matrixSqrt M * matrixSqrt M) * Uᴴ := by rw [hUl, mul_one]
    _ = U * M * Uᴴ := by rw [matrixSqrt_mul_self hM]

theorem fidelityRoot_unitaryConj (U : Mat n) (A B : PSD n)
    (hUl : Uᴴ * U = 1) (hUr : U * Uᴴ = 1) :
    fidelityRoot (U * A.val * Uᴴ) (U * B.val * Uᴴ) =
      fidelityRoot A.val B.val := by
  let R := matrixSqrt A.val
  have hR : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg _)
  have hSand : (R * B.val * R).PosSemidef := by
    have h := B.property.mul_mul_conjTranspose_same R
    simpa only [hR.isHermitian.eq] using h
  have hMat : (U * R * Uᴴ) * (U * B.val * Uᴴ) * (U * R * Uᴴ) =
      U * (R * B.val * R) * Uᴴ := by
    simp only [mul_assoc]
    rw [← mul_assoc Uᴴ U, hUl]
    simp only [one_mul]
    rw [← mul_assoc Uᴴ U, hUl]
    simp only [one_mul]
  unfold fidelityRoot
  rw [matrixSqrt_unitaryConj U A.val hUl hUr A.property, hMat,
    matrixSqrt_unitaryConj U (R * B.val * R) hUl hUr hSand,
    tr_unitaryConj U (matrixSqrt (R * B.val * R)) hUl]

theorem psdDistance_unitaryConj (U : Mat n) (A B : PSD n)
    (hUl : Uᴴ * U = 1) (hUr : U * Uᴴ = 1) :
    psdDistance (unitaryConjPSD U A) (unitaryConjPSD U B) =
      psdDistance A B := by
  unfold psdDistance unitaryConjPSD
  rw [tr_unitaryConj U A.val hUl, tr_unitaryConj U B.val hUl,
    fidelityRoot_unitaryConj U A B hUl hUr]

private def qubitSwap : Mat 2 := !![0, 1; 1, 0]

private theorem qubitSwap_selfAdjoint : qubitSwapᴴ = qubitSwap := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [qubitSwap, Matrix.conjTranspose_apply]

private theorem qubitSwap_sq : qubitSwap * qubitSwap = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [qubitSwap, Matrix.mul_apply, Fin.sum_univ_two]

private theorem qubitGram_zero_offdiag (x : ℝ) :
    (qubitGram x 0 0).val = Matrix.diagonal ![(x ^ 2 : ℂ), 0] := by
  rw [qubitGram_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.diagonal_apply]
  · ring

/-- Every nonzero qubit PSD matrix on the boundary is unitarily conjugate
to a positive rank-one diagonal Gram matrix. -/
theorem rankOne_psd_unitary_diagonal (P : PSD 2)
    (hP0 : P ≠ psdZero) (hPbdry : ¬ P.val.PosDef) :
    ∃ x₀ : ℝ, ∃ U : Mat 2, 0 < x₀ ∧ Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      unitaryConjPSD U P = qubitGram x₀ 0 0 := by
  let hA := P.property.isHermitian
  have h0 : 0 ≤ hA.eigenvalues 0 := P.property.eigenvalues_nonneg 0
  have h1 : 0 ≤ hA.eigenvalues 1 := P.property.eigenvalues_nonneg 1
  have hz : hA.eigenvalues 0 = 0 ∨ hA.eigenvalues 1 = 0 := by
    have hn : ¬ ∀ i, 0 < hA.eigenvalues i :=
      (hA.posDef_iff_eigenvalues_pos).not.mp hPbdry
    push Not at hn
    obtain ⟨i, hi⟩ := hn
    fin_cases i
    · exact Or.inl (le_antisymm hi h0)
    · exact Or.inr (le_antisymm hi h1)
  have hnotboth : ¬ (hA.eigenvalues 0 = 0 ∧ hA.eigenvalues 1 = 0) := by
    rintro ⟨hz0, hz1⟩
    have hd : Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) =
        (0 : Mat 2) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hz0, hz1]
    have hp : P.val = 0 := by
      rw [hA.spectral_theorem, hd]
      simp
    apply hP0
    apply Subtype.ext
    simpa [psdZero] using hp
  let V : Mat 2 := (star hA.eigenvectorUnitary : Mat 2)
  have hVdiag : V * P.val * Vᴴ =
      Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
    simpa only [V, Unitary.conjStarAlgAut_star_apply,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
      using hA.conjStarAlgAut_star_eigenvectorUnitary
  have hVl : Vᴴ * V = 1 := by
    simpa only [V, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose] using
      (Unitary.coe_mul_star_self hA.eigenvectorUnitary)
  have hVr : V * Vᴴ = 1 := by
    simpa only [V, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose] using
      (Unitary.coe_star_mul_self hA.eigenvectorUnitary)
  rcases hz with hz0 | hz1
  · have hp1 : 0 < hA.eigenvalues 1 := by
      rcases eq_or_lt_of_le h1 with heq | hpos
      · exact False.elim (hnotboth ⟨hz0, heq.symm⟩)
      · exact hpos
    let x₀ := Real.sqrt (hA.eigenvalues 1)
    let U := qubitSwap * V
    refine ⟨x₀, U, Real.sqrt_pos.2 hp1, ?_, ?_, ?_⟩
    · change (qubitSwap * V)ᴴ * (qubitSwap * V) = 1
      rw [Matrix.conjTranspose_mul, qubitSwap_selfAdjoint]
      calc
        Vᴴ * qubitSwap * (qubitSwap * V) =
            Vᴴ * (qubitSwap * qubitSwap) * V := by simp only [mul_assoc]
        _ = 1 := by rw [qubitSwap_sq, mul_one, hVl]
    · change (qubitSwap * V) * (qubitSwap * V)ᴴ = 1
      rw [Matrix.conjTranspose_mul, qubitSwap_selfAdjoint]
      calc
        qubitSwap * V * (Vᴴ * qubitSwap) =
            qubitSwap * (V * Vᴴ) * qubitSwap := by simp only [mul_assoc]
        _ = 1 := by rw [hVr, mul_one, qubitSwap_sq]
    · apply Subtype.ext
      change (qubitSwap * V) * P.val * (qubitSwap * V)ᴴ =
        (qubitGram x₀ 0 0).val
      rw [Matrix.conjTranspose_mul, qubitSwap_selfAdjoint]
      have he : (qubitSwap * V) * P.val * (Vᴴ * qubitSwap) =
          qubitSwap * (V * P.val * Vᴴ) * qubitSwap := by simp only [mul_assoc]
      rw [he, hVdiag, qubitGram_zero_offdiag]
      have hsq : ((x₀ : ℂ) ^ 2) = (hA.eigenvalues 1 : ℂ) := by
        exact_mod_cast Real.sq_sqrt hp1.le
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [qubitSwap, Matrix.mul_apply, Matrix.vecMul, dotProduct,
          Fin.sum_univ_two, Matrix.diagonal_apply, hz0, hsq]
  · have hp0 : 0 < hA.eigenvalues 0 := by
      rcases eq_or_lt_of_le h0 with heq | hpos
      · exact False.elim (hnotboth ⟨heq.symm, hz1⟩)
      · exact hpos
    let x₀ := Real.sqrt (hA.eigenvalues 0)
    refine ⟨x₀, V, Real.sqrt_pos.2 hp0, hVl, hVr, ?_⟩
    apply Subtype.ext
    change V * P.val * Vᴴ = (qubitGram x₀ 0 0).val
    rw [hVdiag, qubitGram_zero_offdiag]
    have hsq : ((x₀ : ℂ) ^ 2) = (hA.eigenvalues 0 : ℂ) := by
      exact_mod_cast Real.sq_sqrt hp0.le
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hz1, hsq]

#print axioms matrixSqrt_unitaryConj
#print axioms psdDistance_unitaryConj
#print axioms rankOne_psd_unitary_diagonal

end Bures

import Bures
import Mathlib.Analysis.Matrix.PosDef

/-! The Sylvester equation for positive definite matrices, proved from the
spectral theorem. No differential-geometric assertions are made here. -/
noncomputable section
open scoped ComplexOrder MatrixOrder
namespace Bures

theorem diagonal_sylvester_existsUnique (d : Fin n → ℝ) (hd : ∀ i, 0 < d i)
    (X : Mat n) : ∃! K : Mat n,
      K * Matrix.diagonal (fun i => (d i : ℂ)) +
      Matrix.diagonal (fun i => (d i : ℂ)) * K = X := by
  let K : Mat n := fun i j => X i j / ((d i : ℂ) + (d j : ℂ))
  have hn (i j : Fin n) : (d i : ℂ) + (d j : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (add_pos (hd i) (hd j)))
  refine ⟨K, ?_, ?_⟩
  · ext i j
    simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, K]
    field_simp [hn i j]
    ring
  · intro L hL
    ext i j
    have hij := congrArg (fun M : Mat n => M i j) hL
    simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul] at hij
    change L i j = X i j / ((d i : ℂ) + (d j : ℂ))
    apply (eq_div_iff (hn i j)).mpr
    linear_combination hij

/-- Every complex matrix has a unique Sylvester preimage for a positive
 definite coefficient matrix. -/
theorem posDef_sylvester_existsUnique {A : Mat n} (hA : A.PosDef) (X : Mat n) :
    ∃! K : Mat n, K * A + A * K = X := by
  let φ := Unitary.conjStarAlgAut ℂ (Mat n) (star hA.isHermitian.eigenvectorUnitary)
  have hφA : φ A = Matrix.diagonal (fun i => (hA.isHermitian.eigenvalues i : ℂ)) :=
    hA.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  obtain ⟨L, hL, huniq⟩ := diagonal_sylvester_existsUnique
    hA.isHermitian.eigenvalues hA.eigenvalues_pos (φ X)
  refine ⟨φ.symm L, ?_, ?_⟩
  · apply φ.injective
    change φ (φ.symm L * A + A * φ.symm L) = φ X
    simpa only [map_add, map_mul, φ.apply_symm_apply, hφA] using hL
  · intro K hK
    apply φ.injective
    change φ K = φ (φ.symm L)
    rw [φ.apply_symm_apply]
    apply huniq
    have ht := congrArg φ hK
    simpa only [map_add, map_mul, hφA] using ht

/-- For Hermitian right-hand side the unique Sylvester solution is Hermitian. -/
theorem posDef_hermitian_sylvester_existsUnique {A X : Mat n}
    (hA : A.PosDef) (hX : X.IsHermitian) :
    ∃! K : Mat n, K.IsHermitian ∧ K * A + A * K = X := by
  obtain ⟨K, hK, huniq⟩ := posDef_sylvester_existsUnique hA X
  have hs : K.conjTranspose * A + A * K.conjTranspose = X := by
    have ht := congrArg Matrix.conjTranspose hK
    simpa only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      hA.isHermitian.eq, hX.eq, add_comm] using ht
  refine ⟨K, ⟨huniq K.conjTranspose hs, hK⟩, ?_⟩
  exact fun L hL => huniq L hL.2

#print axioms posDef_sylvester_existsUnique
#print axioms posDef_hermitian_sylvester_existsUnique
end Bures

import Bures
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Complex.Module

/-! Algebraic radial rigidity. These results identify the common Hermitian
commutant; they do not assume or assert any Riemannian curvature formula. -/
noncomputable section
namespace Bures

theorem commute_all_of_commute_hermitian {K : Mat n}
    (h : ∀ L : Mat n, L.IsHermitian → Commute K L) (M : Mat n) : Commute K M := by
  have hr := h (realPart M) (Matrix.isHermitian_iff_isSelfAdjoint.mpr
    (realPart M).property)
  have hi := h (imaginaryPart M) (Matrix.isHermitian_iff_isSelfAdjoint.mpr
    (imaginaryPart M).property)
  rw [← realPart_add_I_smul_imaginaryPart M]
  exact hr.add_right (hi.smul_right Complex.I)

theorem scalar_of_commute_hermitian {K : Mat n}
    (h : ∀ L : Mat n, L.IsHermitian → Commute K L) :
    ∃ c : ℂ, K = Matrix.scalar (Fin n) c := by
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_iff_commute_single'.mpr
    (fun i j => (commute_all_of_commute_hermitian h (Matrix.single i j 1)).symm)
  exact ⟨c, hc.symm⟩

/-- A Hermitian common centralizer is a real scalar matrix, including size zero. -/
theorem real_scalar_of_commute_hermitian {K : Mat n} (hK : K.IsHermitian)
    (h : ∀ L : Mat n, L.IsHermitian → Commute K L) :
    ∃ c : ℝ, K = c • (1 : Mat n) := by
  obtain ⟨c, rfl⟩ := scalar_of_commute_hermitian h
  cases isEmpty_or_nonempty (Fin n) with
  | inl hn =>
    exact ⟨0, Subsingleton.elim _ _⟩
  | inr hn =>
    obtain ⟨i⟩ := hn
    have hc : star c = c := by
      simpa [Matrix.scalar_apply, Matrix.conjTranspose_apply] using
        congrArg (fun M : Mat n => M i i) hK.eq
    have hr : (c.re : ℂ) = c := Complex.conj_eq_iff_re.mp hc
    refine ⟨c.re, ?_⟩
    ext i j
    by_cases hij : i = j
    · subst j
      simpa [Matrix.scalar_apply] using hr.symm
    · simp [Matrix.scalar_apply, Matrix.diagonal, hij]

/-- The algebraic common zero-commutator locus is precisely the real scalar line. -/
theorem hermitian_common_commutant_iff {K : Mat n} (hK : K.IsHermitian) :
    (∀ L : Mat n, L.IsHermitian → Commute K L) ↔
      ∃ c : ℝ, K = c • (1 : Mat n) := by
  constructor
  · exact real_scalar_of_commute_hermitian hK
  · rintro ⟨c, rfl⟩ L _
    exact (Commute.one_left L).smul_left c

/-- Applying the Sylvester tangent expression to a scalar generator gives a
radial tangent vector. This is only the algebraic part of curvature nullity. -/
theorem radial_tangent_of_common_commutant {K : Mat n} (A : Mat n)
    (hK : K.IsHermitian) (h : ∀ L : Mat n, L.IsHermitian → Commute K L) :
    ∃ c : ℝ, K * A + A * K = c • A := by
  obtain ⟨c, rfl⟩ := real_scalar_of_commute_hermitian hK h
  refine ⟨c + c, ?_⟩
  rw [smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  exact (add_smul c c A).symm

/-- The Sylvester image of the common Hermitian commutant is exactly the radial
line, with no assumption on the matrix A. Identifying this algebraic locus with
metric curvature nullity is a separate geometric obligation. -/
theorem sylvester_common_commutant_iff (A X : Mat n) :
    (∃ K : Mat n, K.IsHermitian ∧
      (∀ L : Mat n, L.IsHermitian → Commute K L) ∧ X = K * A + A * K) ↔
    ∃ c : ℝ, X = c • A := by
  constructor
  · rintro ⟨K, hK, h, rfl⟩
    exact radial_tangent_of_common_commutant A hK h
  · rintro ⟨c, rfl⟩
    refine ⟨(c / 2) • (1 : Mat n), Matrix.isHermitian_one.smul (by rfl),
      fun L _ => (Commute.one_left L).smul_left (c / 2), ?_⟩
    rw [smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    module

#print axioms sylvester_common_commutant_iff
#print axioms hermitian_common_commutant_iff
#print axioms radial_tangent_of_common_commutant
end Bures

import RadialAlgebra
import BuresFrobenius
import Sylvester
import Mathlib.Analysis.Calculus.FDeriv.Star

/-! Algebraic part of the coordinate quotient curvature calculation.

For a full-rank lift `S`, tangent vectors of the form `K * S` with `K`
Hermitian are horizontal. Their constant-generator brackets have the form
`(K * L - L * K) * S`. This file proves that such a bracket is horizontal
precisely when its generators commute. In a flat quotient, identifying this
with *zero curvature* additionally requires the O'Neill curvature formula.
-/

noncomputable section
namespace Bures

open scoped Matrix.Norms.Frobenius ContinuousLinearMap MatrixOrder ComplexOrder

/-- The Gram map whose unitary quotient is the positive definite cone. -/
def gram (S : Mat n) : Mat n := S * S.conjTranspose

theorem gram_hasFDerivAt (S : Mat n) :
    ∃ L : Mat n →L[ℝ] Mat n,
      HasFDerivAt gram L S ∧
      ∀ H, L H = H * S.conjTranspose + S * H.conjTranspose := by
  let hi := hasFDerivAt_id (𝕜 := ℝ) (x := S)
  let hs := hi.star
  let hm := hi.mul' hs
  refine ⟨_, hm, ?_⟩
  intro H
  change S * H.conjTranspose + H * S.conjTranspose =
    H * S.conjTranspose + S * H.conjTranspose
  exact add_comm _ _

/-- Exact first-order expansion of the Gram map; the omitted term is quadratic. -/
theorem gram_add (S H : Mat n) :
    gram (S + H) = gram S +
      (H * S.conjTranspose + S * H.conjTranspose) +
      H * H.conjTranspose := by
  simp only [gram, Matrix.conjTranspose_add]
  noncomm_ring

/-- Along a Hermitian horizontal direction, the Gram-map linear term is
the Sylvester tangent expression at the base matrix. -/
theorem gram_horizontal_linear (S K : Mat n) (hK : K.IsHermitian) :
    (K * S) * S.conjTranspose + S * (K * S).conjTranspose =
      K * gram S + gram S * K := by
  simp only [gram, Matrix.conjTranspose_mul, hK.eq]
  noncomm_ring

/-- The actual Fréchet derivative of the Gram map sends horizontal lifts to
the Sylvester tangent at `A = S Sᴴ`. Every Hermitian base tangent has a unique
Hermitian generator when `A` is positive definite. -/
theorem gram_derivative_horizontal_bijective (S : Mat n)
    (hA : (gram S).PosDef) :
    ∃ L : Mat n →L[ℝ] Mat n,
      HasFDerivAt gram L S ∧
      ∀ X : Mat n, X.IsHermitian →
        ∃! K : Mat n, K.IsHermitian ∧ L (K * S) = X := by
  obtain ⟨L, hL, hLeq⟩ := gram_hasFDerivAt S
  refine ⟨L, hL, ?_⟩
  intro X hX
  obtain ⟨K, ⟨hK, hKeq⟩, huniq⟩ :=
    posDef_hermitian_sylvester_existsUnique hA hX
  refine ⟨K, ⟨hK, ?_⟩, ?_⟩
  · rw [hLeq]
    exact (gram_horizontal_linear S K hK).trans hKeq
  · intro J ⟨hJ, hJeq⟩
    apply huniq J
    refine ⟨hJ, ?_⟩
    calc
      J * gram S + gram S * J = L (J * S) :=
        (gram_horizontal_linear S J hJ).symm.trans (hLeq (J * S)).symm
      _ = X := hJeq

/-- The horizontal Frobenius energy is the Sylvester quadratic form on the
base tangent. This is the coordinate expression for the quotient metric. -/
theorem horizontal_energy_eq_sylvester (S K : Mat n)
    (hK : K.IsHermitian) :
    tr ((K * S).conjTranspose * (K * S)) =
      tr ((K * gram S + gram S * K) * K) / 2 := by
  have hcyc : Matrix.trace ((K * S).conjTranspose * (K * S)) =
      Matrix.trace (K * gram S * K) := by
    rw [Matrix.conjTranspose_mul, hK.eq]
    calc
      Matrix.trace ((S.conjTranspose * K) * (K * S)) =
          Matrix.trace ((K * S) * (S.conjTranspose * K)) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace (K * gram S * K) := by
        congr 1
        simp [gram, mul_assoc]
  have hother : Matrix.trace ((gram S * K) * K) =
      Matrix.trace (K * gram S * K) := by
    calc
      _ = Matrix.trace (K * (gram S * K)) := Matrix.trace_mul_comm _ _
      _ = _ := by congr 1; simp [mul_assoc]
  unfold tr
  rw [hcyc, add_mul, Matrix.trace_add, hother]
  simp only [Complex.add_re]
  ring

/-- The quotient-metric pairing with the radial lift `S` is half the real
trace of the corresponding Sylvester tangent. -/
theorem horizontal_radial_pairing (S K : Mat n)
    (hK : K.IsHermitian) :
    tr ((K * S).conjTranspose * S) =
      tr (K * gram S + gram S * K) / 2 := by
  have hcyc : tr ((K * S).conjTranspose * S) = tr (K * gram S) := by
    rw [Matrix.conjTranspose_mul, hK.eq]
    calc
      tr ((S.conjTranspose * K) * S) = tr (S * (S.conjTranspose * K)) :=
        tr_mul_comm _ _
      _ = tr (K * gram S) := by
        calc
          _ = tr ((S * S.conjTranspose) * K) := by simp only [mul_assoc]
          _ = tr (K * (S * S.conjTranspose)) := tr_mul_comm _ _
          _ = _ := rfl
  rw [hcyc, tr_add, tr_mul_comm (gram S) K]
  ring

/-- The squared Frobenius length of the radial lift is the trace of its
base Gram matrix. -/
theorem radial_lift_energy (S : Mat n) :
    tr (S.conjTranspose * S) = tr (gram S) := by
  rw [tr_mul_comm, gram]

/-- A skew-Hermitian right-rotation lies in the kernel of the Gram-map
linear term. -/
theorem gram_vertical_linear (S Ω : Mat n)
    (hΩ : Ω.conjTranspose = -Ω) :
    (S * Ω) * S.conjTranspose + S * (S * Ω).conjTranspose = 0 := by
  simp only [Matrix.conjTranspose_mul, hΩ]
  noncomm_ring

/-- Hermitian and skew-Hermitian factors are orthogonal for the real trace
pairing. This is the finite-dimensional horizontal/vertical orthogonality
underlying the quotient construction. -/
theorem hermitian_skew_trace_zero (H Ω : Mat n) (hH : H.IsHermitian)
    (hΩ : Ω.conjTranspose = -Ω) : tr (H * Ω) = 0 := by
  have hs : star (Matrix.trace (H * Ω)) = -Matrix.trace (H * Ω) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hΩ, hH.eq,
      neg_mul, Matrix.trace_neg, Matrix.trace_mul_comm]
  have hr := congrArg Complex.re hs
  simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at hr
  unfold tr
  linarith

/-- Horizontal lifts `K*S` are orthogonal to infinitesimal right-unitary
rotations `S*Ω` for the real Frobenius trace pairing. -/
theorem horizontal_vertical_orthogonal (S K Ω : Mat n)
    (hK : K.IsHermitian) (hΩ : Ω.conjTranspose = -Ω) :
    tr ((K * S).conjTranspose * (S * Ω)) = 0 := by
  rw [Matrix.conjTranspose_mul, hK.eq]
  have hH : (S.conjTranspose * K * S).IsHermitian := by
    apply Matrix.isHermitian_iff_isSelfAdjoint.mpr
    change (S.conjTranspose * K * S).conjTranspose = S.conjTranspose * K * S
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hK.eq]
    noncomm_ring
  convert hermitian_skew_trace_zero (S.conjTranspose * K * S) Ω hH hΩ using 1
  · congr 1
    simp only [mul_assoc]

/-- At an invertible lift, a bracket of Hermitian horizontal generators can
itself be horizontal only when the generators commute. -/
theorem commutator_horizontal_iff {S K L : Mat n} (hS : IsUnit S)
    (hK : K.IsHermitian) (hL : L.IsHermitian) :
    (∃ H : Mat n, H.IsHermitian ∧ (K * L - L * K) * S = H * S) ↔
      Commute K L := by
  constructor
  · rintro ⟨H, hH, heq⟩
    have hc : K * L - L * K = H := hS.mul_right_cancel heq
    exact (hermitian_commutator_iff_commute hK hL).mp (hc ▸ hH)
  · intro hc
    refine ⟨0, Matrix.isHermitian_zero, ?_⟩
    rw [hc.eq, sub_self, zero_mul]

/-- If every constant-generator bracket with `K` is horizontal at one
invertible lift, `K` is a real scalar matrix. -/
theorem all_brackets_horizontal_iff_scalar {S K : Mat n} (hS : IsUnit S)
    (hK : K.IsHermitian) :
    (∀ L : Mat n, L.IsHermitian →
      ∃ H : Mat n, H.IsHermitian ∧ (K * L - L * K) * S = H * S) ↔
      ∃ c : ℝ, K = c • (1 : Mat n) := by
  rw [← hermitian_common_commutant_iff hK]
  exact forall_congr' fun L => forall_congr' fun hL =>
    commutator_horizontal_iff hS hK hL

#print axioms commutator_horizontal_iff
#print axioms all_brackets_horizontal_iff_scalar
#print axioms gram_hasFDerivAt
#print axioms gram_derivative_horizontal_bijective
#print axioms horizontal_energy_eq_sylvester
#print axioms horizontal_radial_pairing
#print axioms horizontal_vertical_orthogonal
end Bures

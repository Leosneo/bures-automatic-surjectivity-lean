import BuresConnectionAlgebra
import BuresFrobenius

/-! Coordinate curvature algebra at the scalar base matrix 1.
This file does not yet assert that the algebraic expression is the curvature
of the literal metric: that identification requires smooth Sylvester inverse. -/
noncomputable section
open scoped MatrixOrder ComplexOrder Matrix.Norms.Frobenius
namespace Bures

/-- Four times the Christoffel expression at A=1. -/
def scaledConnectionOne (X Y : Mat n) : Mat n := -(X * Y + Y * X)

/-- Eight times its directional derivative at A=1, for constant tangent
vectors U,V and base displacement H. -/
def scaledConnectionDerivativeOne (H U V : Mat n) : Mat n :=
  H * U * V + H * V * U + U * V * H + V * U * H

/-- Sixteen times the coordinate curvature expression at A=1, built from
connection derivative and nested connection terms. -/
def scaledCurvatureOne (X Y Z : Mat n) : Mat n :=
  2 * (scaledConnectionDerivativeOne X Y Z -
      scaledConnectionDerivativeOne Y X Z) +
    scaledConnectionOne X (scaledConnectionOne Y Z) -
    scaledConnectionOne Y (scaledConnectionOne X Z)

/-- The scalar-base coordinate curvature collapses to a double commutator. -/
theorem scaledCurvatureOne_eq_commutator (X Y Z : Mat n) :
    scaledCurvatureOne X Y Z =
      3 * ((X * Y - Y * X) * Z - Z * (X * Y - Y * X)) := by
  simp only [scaledCurvatureOne, scaledConnectionDerivativeOne, scaledConnectionOne]
  noncomm_ring

/-- The trace contraction of a double commutator is exactly the squared
Frobenius norm of the commutator. -/
theorem trace_double_commutator_eq_commutator_norm_sq (K L : Mat n)
    (hK : K.IsHermitian) (hL : L.IsHermitian) :
    tr (((K * L - L * K) * L - L * (K * L - L * K)) * K) =
      ‖K * L - L * K‖ ^ 2 := by
  let C := K * L - L * K
  have hC : C.conjTranspose = -C := by
    dsimp [C]
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hK.eq, hL.eq]
    abel
  have hcyc : tr (L * C * K) = tr (C * K * L) := tr_cycle3 L C K
  have hm : C * L * K - C * K * L = -(C * C) := by
    dsimp [C]
    noncomm_ring
  calc
    tr ((C * L - L * C) * K) =
        tr (C * L * K) - tr (L * C * K) := by rw [sub_mul, tr_sub]
    _ = tr (C * L * K) - tr (C * K * L) := by rw [hcyc]
    _ = tr (-(C * C)) := by rw [← tr_sub, hm]
    _ = tr (C * C.conjTranspose) := by rw [hC, mul_neg]
    _ = ‖C‖ ^ 2 := (frobenius_sq_eq_tr_gram C).symm

/-- At the scalar base, every direction commuting with all Hermitian
directions is scalar, hence radial. This is the nullity of the curvature
algebra once it is identified with geometric curvature. -/
theorem scaledCurvatureOne_common_nullity (K : Mat n) (hK : K.IsHermitian)
    (hzero : ∀ L : Mat n, L.IsHermitian →
      scaledCurvatureOne K L L = 0) :
    ∃ c : ℝ, K = c • (1 : Mat n) := by
  apply (hermitian_common_commutant_iff hK).mp
  intro L hL
  let C : Mat n := K * L - L * K
  let T : Mat n := C * L - L * C
  have hcurv : (3 : Mat n) * T = 0 := by
    simpa only [scaledCurvatureOne_eq_commutator, C, T] using hzero L hL
  have hscalar : (3 : Mat n) * T = (3 : ℂ) • T := by
    calc
      (3 : Mat n) * T = T + T + T := by noncomm_ring
      _ = (3 : ℂ) • T := by
        ext i j
        simp [Matrix.smul_apply]
        ring
  rw [hscalar] at hcurv
  have hT : T = 0 := (smul_eq_zero.mp hcurv).resolve_left (by norm_num)
  have hsq : ‖C‖ ^ 2 = 0 := by
    rw [← trace_double_commutator_eq_commutator_norm_sq K L hK hL]
    change tr (T * K) = 0
    simp [hT, tr]
  have hnorm : ‖C‖ = 0 := by nlinarith [norm_nonneg C]
  have hC : C = 0 := norm_eq_zero.mp hnorm
  exact sub_eq_zero.mp hC

#print axioms scaledCurvatureOne_eq_commutator
end Bures
#print axioms Bures.scaledCurvatureOne_common_nullity

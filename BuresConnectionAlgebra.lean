import BuresCoordinateCurvature

/-! Algebraic Levi-Civita coefficients of the Bures Sylvester metric.
The geometric identification with the Levi-Civita connection requires a
smooth solution family and the Koszul identity. -/
noncomputable section
open scoped MatrixOrder ComplexOrder
namespace Bures

/-- Anticommutator, the coordinate Sylvester operator. -/
def anti (P Q : Mat n) : Mat n := P * Q + Q * P

/-- Candidate Christoffel term of the Bures metric in affine Hermitian
coordinates, expressed through Sylvester generators. -/
def christoffelAlgebra (A P Q : Mat n) : Mat n :=
  -(P * A * Q + Q * A * P)

theorem christoffelAlgebra_symm (A P Q : Mat n) :
    christoffelAlgebra A P Q = christoffelAlgebra A Q P := by
  simp only [christoffelAlgebra]
  rw [add_comm]

theorem christoffelAlgebra_isHermitian (A P Q : Mat n)
    (hA : A.IsHermitian) (hP : P.IsHermitian) (hQ : Q.IsHermitian) :
    (christoffelAlgebra A P Q).IsHermitian := by
  apply Matrix.isHermitian_iff_isSelfAdjoint.mpr
  change (christoffelAlgebra A P Q).conjTranspose = _
  simp only [christoffelAlgebra, Matrix.conjTranspose_neg,
    Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hA.eq, hP.eq, hQ.eq]
  noncomm_ring

/-- Matrix identity behind the Koszul formula. For `X={A,P}` and `Y={A,Q}`,
the right side is the three directional metric derivatives. -/
theorem christoffel_anticommutator_identity (A P Q : Mat n) :
    anti (anti A P) Q + anti (anti A Q) P =
      anti A (anti P Q) - 2 * christoffelAlgebra A P Q := by
  simp only [anti, christoffelAlgebra]
  noncomm_ring

/-- Euler's radial field `Z(A)=2A` has generator `1`, and its Christoffel
contribution in a tangent X={A,P} is exactly `-X`. -/
theorem christoffel_radial (A P : Mat n) :
    christoffelAlgebra A P 1 = -anti A P := by
  simp [christoffelAlgebra, anti, add_comm]

/-- For the affine Euler field, ordinary derivative `2X` plus the
Christoffel term with generator `1` equals `X`. -/
theorem euler_connection_algebra (A P : Mat n) :
    (2 : Mat n) * anti A P + christoffelAlgebra A P 1 = anti A P := by
  rw [christoffel_radial]
  noncomm_ring

#print axioms christoffel_anticommutator_identity
#print axioms euler_connection_algebra
end Bures

namespace Bures

theorem tr_cycle3 (A B C : Mat n) : tr (A * B * C) = tr (B * C * A) := by
  calc
    tr (A * B * C) = tr (A * (B * C)) := by rw [mul_assoc]
    _ = tr ((B * C) * A) := tr_mul_comm A (B * C)
    _ = tr (B * C * A) := rfl

theorem tr_anti_move (X Q R : Mat n) :
    tr (X * anti Q R) = tr (anti X Q * R) := by
  simp only [anti, mul_add, add_mul, tr_add, mul_assoc]
  simp only [← mul_assoc]
  rw [tr_cycle3 Q X R]

theorem tr_anti_swap (A B R : Mat n) :
    tr (anti A R * B) = tr (anti A B * R) := by
  simp only [anti, add_mul, tr_add]
  have h1 : tr (A * R * B) = tr (B * A * R) := by
    calc
      _ = tr (R * B * A) := tr_cycle3 A R B
      _ = tr (B * A * R) := tr_cycle3 R B A
  have h2 : tr (R * A * B) = tr (A * B * R) := tr_cycle3 R A B
  rw [h1, h2]
  abel

/-- The algebraic Koszul identity for the proposed Bures Christoffel term.
The three terms on the right are the derivatives of the Sylvester metric
along constant directions, once differentiability of the solution is proved. -/
theorem christoffel_koszul_trace (A P Q R : Mat n) :
    2 * tr (christoffelAlgebra A P Q * R) =
      -tr (anti A P * anti Q R) -
       tr (anti A Q * anti P R) +
       tr (anti A R * anti P Q) := by
  rw [tr_anti_move (anti A P) Q R,
    tr_anti_move (anti A Q) P R,
    tr_anti_swap A (anti P Q) R]
  have hm : anti A (anti P Q) - anti (anti A P) Q -
      anti (anti A Q) P = 2 * christoffelAlgebra A P Q := by
    simp only [anti, christoffelAlgebra]
    noncomm_ring
  have ht : tr ((2 * christoffelAlgebra A P Q) * R) =
      2 * tr (christoffelAlgebra A P Q * R) := by
    rw [two_mul, add_mul, tr_add]
    ring
  calc
    2 * tr (christoffelAlgebra A P Q * R) =
        tr ((2 * christoffelAlgebra A P Q) * R) := ht.symm
    _ = tr ((anti A (anti P Q) - anti (anti A P) Q -
        anti (anti A Q) P) * R) := by rw [hm]
    _ = _ := by
      simp only [sub_mul, tr_sub]
      ring

#print axioms christoffel_koszul_trace
end Bures

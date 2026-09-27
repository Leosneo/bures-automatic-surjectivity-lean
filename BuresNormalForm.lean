import BuresNormalLinearExtension
import BuresSquareTranslation

/-! The affine normal form at the identity, stated using literal positive
matrix square roots. -/
noncomputable section
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace Bures
set_option backward.isDefEq.respectTransparency false

def pdIdentity (n : ℕ) : PositiveDefinite n := ⟨1, Matrix.PosDef.one⟩

theorem matrixSqrt_pdIdentity (n : ℕ) : matrixSqrt (pdIdentity n).val = 1 :=
  matrixSqrt_unique Matrix.PosSemidef.one (one_mul 1)

theorem normalTransport_identity (B : PositiveDefinite n) :
    normalTransport (pdIdentity n) B = matrixSqrt B.val := by
  simp only [normalTransport, optimalLift, matrixSqrt_pdIdentity,
    inv_one, one_mul, mul_one]

theorem normalCoordinate_identity_squarePoint (T : Hermitian n)
    (hT : T.val.PosDef) :
    normalCoordinate (pdIdentity n) (squarePoint T.val hT) =
      T - (⟨1, Matrix.isHermitian_one⟩ : Hermitian n) := by
  apply Subtype.ext
  change normalTransport (pdIdentity n) (squarePoint T.val hT) - 1 = T.val - 1
  rw [normalTransport_identity, matrixSqrt_squarePoint]

theorem affine_normal_transport_of_representation
    (F : PositiveDefinite n → PositiveDefinite n)
    (L : Hermitian n →ₗ[ℝ] Hermitian n)
    (hrep : ∀ B : PositiveDefinite n,
      normalCoordinate (F (pdIdentity n)) (F B) =
        L (normalCoordinate (pdIdentity n) B))
    (T : Hermitian n) (hT : T.val.PosDef) :
    normalTransport (F (pdIdentity n)) (F (squarePoint T.val hT)) =
      ((⟨1, Matrix.isHermitian_one⟩ : Hermitian n) +
        L (T - (⟨1, Matrix.isHermitian_one⟩ : Hermitian n))).val := by
  have h := hrep (squarePoint T.val hT)
  rw [normalCoordinate_identity_squarePoint] at h
  have hm := congrArg Subtype.val h
  change normalTransport (F (pdIdentity n)) (F (squarePoint T.val hT)) - 1 =
    (L (T - (⟨1, Matrix.isHermitian_one⟩ : Hermitian n))).val at hm
  change normalTransport (F (pdIdentity n)) (F (squarePoint T.val hT)) =
    1 + (L (T - (⟨1, Matrix.isHermitian_one⟩ : Hermitian n))).val
  rw [← hm]
  abel

theorem affine_normal_chart_positive
    (F : PositiveDefinite n → PositiveDefinite n)
    (L : Hermitian n →ₗ[ℝ] Hermitian n)
    (hrep : ∀ B : PositiveDefinite n,
      normalCoordinate (F (pdIdentity n)) (F B) =
        L (normalCoordinate (pdIdentity n) B))
    (T : Hermitian n) (hT : T.val.PosDef) :
    ((⟨1, Matrix.isHermitian_one⟩ : Hermitian n) +
      L (T - (⟨1, Matrix.isHermitian_one⟩ : Hermitian n))).val.PosDef := by
  rw [← affine_normal_transport_of_representation F L hrep T hT]
  exact normalTransport_posDef _ _

theorem affine_normal_congruence_form
    (F : PositiveDefinite n → PositiveDefinite n)
    (L : Hermitian n →ₗ[ℝ] Hermitian n)
    (hrep : ∀ B : PositiveDefinite n,
      normalCoordinate (F (pdIdentity n)) (F B) =
        L (normalCoordinate (pdIdentity n) B))
    (T : Hermitian n) (hT : T.val.PosDef) :
    let P := ((⟨1, Matrix.isHermitian_one⟩ : Hermitian n) +
      L (T - (⟨1, Matrix.isHermitian_one⟩ : Hermitian n))).val
    (F (squarePoint T.val hT)).val = P * (F (pdIdentity n)).val * P := by
  dsimp only
  rw [← affine_normal_transport_of_representation F L hrep T hT]
  exact (normalTransport_congruence _ _).symm

#print axioms affine_normal_congruence_form
#print axioms affine_normal_chart_positive
end Bures

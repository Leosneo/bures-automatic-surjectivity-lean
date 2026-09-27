import BuresAnchorDerivative
import BuresLocalRegularity

/-! The exact distance-coordinate identity for anchors that lie in the image
of a literal Bures isometry. The Jacobian rank of these particular image
anchors is the remaining smoothness obligation. -/

noncomputable section
open scoped MatrixOrder ComplexOrder
namespace Bures

def pdHermitian (A : PositiveDefinite n) : Hermitian n :=
  ⟨A.val, A.property.isHermitian⟩

theorem image_anchor_coordinate_identity {ι : Type*}
    (F : PositiveDefinite n → PositiveDefinite n)
    (hF : PreservesDistance F) (anchors : ι → PositiveDefinite n)
    (A : PositiveDefinite n) :
    anchoredSquaredDistances (fun i => pdHermitian (F (anchors i)))
      (pdHermitian (F A)) =
    anchoredSquaredDistances (fun i => pdHermitian (anchors i))
      (pdHermitian A) := by
  funext i
  change squaredBuresHermitian (pdHermitian (F (anchors i)))
      (pdHermitian (F A)) =
    squaredBuresHermitian (pdHermitian (anchors i)) (pdHermitian A)
  rw [show squaredBuresHermitian (pdHermitian (F (anchors i)))
      (pdHermitian (F A)) = distance (F A) (F (anchors i)) ^ 2 from
        squaredBuresHermitian_eq_distance_sq (F A) (F (anchors i)),
    show squaredBuresHermitian (pdHermitian (anchors i)) (pdHermitian A) =
      distance A (anchors i) ^ 2 from
        squaredBuresHermitian_eq_distance_sq A (anchors i), hF]

#print axioms image_anchor_coordinate_identity
end Bures

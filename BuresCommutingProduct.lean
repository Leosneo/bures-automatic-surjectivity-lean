import BuresNormalChart
noncomputable section
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace Bures
local instance (n : ℕ) : CStarAlgebra (Mat n) where

theorem posSemidef_mul_of_commute {T S : Mat n}
    (hT : T.PosSemidef) (hS : S.PosSemidef)
    (hc : Commute T S) : (T * S).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp
    (Commute.mul_nonneg (Matrix.nonneg_iff_posSemidef.mpr hT)
      (Matrix.nonneg_iff_posSemidef.mpr hS) hc)

end Bures

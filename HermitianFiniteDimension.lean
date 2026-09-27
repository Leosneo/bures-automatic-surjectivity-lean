import HermitianSquareSmooth
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! The real Hermitian matrix space is finite dimensional. -/

noncomputable section
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace Bures
local instance (n : ℕ) : CStarAlgebra (Mat n) where

instance hermitianFiniteDimensional (n : ℕ) :
    FiniteDimensional ℝ (Hermitian n) :=
  FiniteDimensional.of_injective (hermitianInclusion n).toLinearMap (by
    intro x y h
    exact Subtype.ext h)

end Bures

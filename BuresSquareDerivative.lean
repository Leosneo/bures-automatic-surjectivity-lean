import Sylvester
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! Differential of matrix squaring, the first step toward a local inverse
description of the positive matrix square root. -/
noncomputable section
open scoped Matrix.Norms.L2Operator ContinuousLinearMap
namespace Bures

local instance (n : ℕ) : CStarAlgebra (Mat n) where

theorem hasFDerivAt_matrix_square (S : Mat n) :
    ∃ L : Mat n →L[ℂ] Mat n,
      HasFDerivAt (fun X : Mat n => X * X) L S ∧
      ∀ H, L H = S * H + H * S := by
  let h := (hasFDerivAt_id (𝕜 := ℂ) (x := S)).mul'
    (hasFDerivAt_id (𝕜 := ℂ) (x := S))
  refine ⟨_, h, ?_⟩
  intro H
  simp

#print axioms hasFDerivAt_matrix_square
end Bures

import BuresFrobenius
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! Continuous comparison between the operator and Frobenius norms on finite
complex matrices, using the nested ℓ² model of the Frobenius norm. -/

noncomputable section
open WithLp
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace Bures

def operatorMagnitude {n : ℕ} (M : Mat n) : ℝ :=
  letI : NormedAddCommGroup (Mat n) := Matrix.instL2OpNormedAddCommGroup
  ‖M‖

theorem operatorMagnitude_eq_norm (M : Mat n) :
    operatorMagnitude M = ‖M‖ := rfl

/-- The nested ℓ² model underlying the Frobenius norm on matrices. -/
abbrev FrobeniusModel (n : ℕ) :=
  WithLp 2 (Fin n → WithLp 2 (Fin n → ℂ))

def frobeniusMagnitude {n : ℕ} (M : Mat n) : ℝ :=
  ‖(toLp 2 (fun i => toLp 2 (fun j => M i j)) : FrobeniusModel n)‖

open scoped Matrix.Norms.Frobenius in
theorem frobeniusMagnitude_eq_norm (M : Mat n) :
    frobeniusMagnitude M = ‖M‖ := rfl

/-- The identity on matrix entries, regarded as a linear map from operator
normed matrices to their Frobenius ℓ² model. -/
def opToFrobeniusLinear (n : ℕ) : Mat n →ₗ[ℂ] FrobeniusModel n where
  toFun M := toLp 2 (fun i => toLp 2 (fun j => M i j))
  map_add' := by
    intro M N
    ext i j
    rfl
  map_smul' := by
    intro a M
    ext i j
    rfl

/-- Finite dimensionality makes the matrix-entry identity continuous. -/
def opToFrobeniusCLM (n : ℕ) : Mat n →L[ℂ] FrobeniusModel n :=
  (opToFrobeniusLinear n).toContinuousLinearMap

/-- The inverse matrix-entry linear map. -/
def frobeniusToOpLinear (n : ℕ) : FrobeniusModel n →ₗ[ℂ] Mat n where
  toFun x := fun i j => x i j
  map_add' := by
    intro x y
    ext i j
    rfl
  map_smul' := by
    intro a x
    ext i j
    rfl

def frobeniusToOpCLM (n : ℕ) : FrobeniusModel n →L[ℂ] Mat n :=
  (frobeniusToOpLinear n).toContinuousLinearMap

theorem frobeniusToOp_opToFrobenius (M : Mat n) :
    frobeniusToOpCLM n (opToFrobeniusCLM n M) = M := by
  ext i j
  rfl

/-- A finite constant bounds Frobenius norm by operator norm. -/
theorem exists_frobenius_le_operator (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : Mat n,
      frobeniusMagnitude M ≤ C * operatorMagnitude M := by
  let C : ℝ := ‖opToFrobeniusCLM n‖ + 1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro M
  have h := (opToFrobeniusCLM n).le_opNorm M
  have hnorm : ‖opToFrobeniusCLM n M‖ =
      frobeniusMagnitude M := rfl
  rw [hnorm] at h
  exact h.trans (by
    change ‖opToFrobeniusCLM n‖ * operatorMagnitude M ≤
      (‖opToFrobeniusCLM n‖ + 1) * operatorMagnitude M
    have hm : 0 ≤ operatorMagnitude M := by
      unfold operatorMagnitude
      exact norm_nonneg M
    nlinarith)

theorem exists_operator_le_frobenius (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : Mat n,
      operatorMagnitude M ≤ C * frobeniusMagnitude M := by
  let C : ℝ := ‖frobeniusToOpCLM n‖ + 1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro M
  have h := (frobeniusToOpCLM n).le_opNorm (opToFrobeniusCLM n M)
  rw [frobeniusToOp_opToFrobenius] at h
  change operatorMagnitude M ≤ ‖frobeniusToOpCLM n‖ * frobeniusMagnitude M at h
  exact h.trans (by
    change ‖frobeniusToOpCLM n‖ * frobeniusMagnitude M ≤
      (‖frobeniusToOpCLM n‖ + 1) * frobeniusMagnitude M
    have hm : 0 ≤ frobeniusMagnitude M := by
      unfold frobeniusMagnitude
      exact norm_nonneg _
    nlinarith)

#print axioms exists_frobenius_le_operator
#print axioms exists_operator_le_frobenius

end Bures

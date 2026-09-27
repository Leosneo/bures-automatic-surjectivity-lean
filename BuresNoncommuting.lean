import BuresShiftStrict
import Mathlib.Data.Matrix.Basis
noncomputable section
open scoped MatrixOrder ComplexOrder Matrix.Norms.Frobenius
namespace Bures

/-- In every matrix size at least two there are noncommuting positive
definite matrices. -/
theorem exists_noncommuting_posDef (n : ℕ) (hn : 2 ≤ n) :
    ∃ T S : Mat n, T.PosDef ∧ S.PosDef ∧ ¬ Commute T S := by
  classical
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
  let E : Mat n := Matrix.single i i (1 : ℂ)
  let F : Mat n := Matrix.single i i (1 : ℂ) + Matrix.single j i (1 : ℂ)
  let P : Mat n := E * E.conjTranspose
  let Q : Mat n := F * F.conjTranspose
  let T : Mat n := 1 + P
  let S : Mat n := 1 + Q
  have hP : P.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose E
  have hQ : Q.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose F
  have hT : T.PosDef := Matrix.PosDef.one.add_posSemidef hP
  have hS : S.PosDef := Matrix.PosDef.one.add_posSemidef hQ
  refine ⟨T, S, hT, hS, ?_⟩
  intro hc
  have hPQ : P * Q = Q * P := by
    have hh := hc.eq
    dsimp [T, S] at hh
    have he : P * Q = (1 + P) * (1 + Q) - (1 + Q) * (1 + P) + Q * P := by
      noncomm_ring
    rw [he, hh]
    simp
  have hPeq : P = Matrix.single i i (1 : ℂ) := by
    dsimp [P, E]
    simp [Matrix.conjTranspose_single, Matrix.single_mul_single_same]
  have hQeq : Q = Matrix.single i i (1 : ℂ) + Matrix.single i j 1 +
      Matrix.single j i 1 + Matrix.single j j 1 := by
    dsimp [Q, F]
    simp [Matrix.conjTranspose_add, Matrix.conjTranspose_single,
      add_mul, mul_add, Matrix.single_mul_single_same]
    abel
  have hi := congrArg (fun M : Mat n => M i j) hPQ
  simp [hPeq, hQeq, Matrix.add_mul,
    Matrix.single_mul_single_same, hij] at hi
  have : (Matrix.single j j (1 : ℂ) : Mat n) i j = 0 := by
    simp [hij.symm]
  rw [this] at hi
  norm_num at hi

#print axioms exists_noncommuting_posDef
end Bures

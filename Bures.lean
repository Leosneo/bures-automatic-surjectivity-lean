import Mathlib.Analysis.Matrix.Order
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Tactic

/-!
# The literal finite-dimensional Bures automatic-surjectivity problem

Komálovics–Molnár, JMAA 529 (2024), 127226, p.20 after Proposition 10.
The source's `d₂` differs from standard Bures distance by a factor `sqrt 2`.

The target below is a proposition definition. Its unconditional proof is
`Bures.automaticSurjectivity` in `BuresAutomaticSurjectivity.lean`.
No metric-space instance is installed for `PositiveDefinite`: preservation means
equality of the explicit Bures formula, never the ambient matrix norm distance.
-/

noncomputable section
open scoped MatrixOrder ComplexOrder

namespace Bures

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
abbrev PositiveDefinite (n : ℕ) := {A : Mat n // A.PosDef}

local instance (n : ℕ) :
    NonUnitalContinuousFunctionalCalculus ℝ (Mat n) IsSelfAdjoint :=
  ContinuousFunctionalCalculus.toNonUnital

local instance (n : ℕ) : NonnegSpectrumClass ℝ (Mat n) :=
  Matrix.instNonnegSpectrumClass

/-- Real trace; on Hermitian matrices the imaginary part of the trace vanishes. -/
def tr (A : Mat n) : ℝ := (Matrix.trace A).re

/-- The actual positive matrix square root from continuous functional calculus. -/
def matrixSqrt (A : Mat n) : Mat n := CFC.sqrt A

def fidelityRoot (A B : Mat n) : ℝ :=
  tr (matrixSqrt (matrixSqrt A * B * matrixSqrt A))

/-- Standard Bures--Wasserstein distance, with its literal matrix formula. -/
def distance (A B : PositiveDefinite n) : ℝ :=
  Real.sqrt (tr A.val + tr B.val - 2 * fidelityRoot A.val B.val)

/-- The p=2 normalization in the cited paper. -/
def literatureD2 (A B : PositiveDefinite n) : ℝ :=
  Real.sqrt ((tr A.val + tr B.val) / 2 - fidelityRoot A.val B.val)

def PreservesDistance (F : PositiveDefinite n → PositiveDefinite n) : Prop :=
  ∀ A B, distance (F A) (F B) = distance A B

/-- Exact target: no continuity, injectivity, trace or surjectivity hypothesis. -/
def AutomaticSurjectivity : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ F : PositiveDefinite n → PositiveDefinite n,
    PreservesDistance F → Function.Surjective F

/-- The same target using the paper's p=2 normalization. -/
def LiteratureProblem : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ F : PositiveDefinite n → PositiveDefinite n,
    (∀ A B, literatureD2 (F A) (F B) = literatureD2 A B) →
    Function.Surjective F

theorem matrixSqrt_nonneg (A : Mat n) : 0 ≤ matrixSqrt A :=
  CFC.sqrt_nonneg A

theorem matrixSqrt_mul_self {A : Mat n} (hA : A.PosSemidef) :
    matrixSqrt A * matrixSqrt A = A :=
  CFC.sqrt_mul_sqrt_self A hA.nonneg

theorem matrixSqrt_unique {A S : Mat n} (hS : S.PosSemidef)
    (hSq : S * S = A) : matrixSqrt A = S :=
  CFC.sqrt_unique hSq hS.nonneg

theorem distance_nonneg (A B : PositiveDefinite n) : 0 ≤ distance A B :=
  Real.sqrt_nonneg _

theorem distance_eq_sqrt_two_mul_d2 (A B : PositiveDefinite n) :
    distance A B = Real.sqrt 2 * literatureD2 A B := by
  unfold distance literatureD2
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

theorem preserves_iff_literature (F : PositiveDefinite n → PositiveDefinite n) :
    PreservesDistance F ↔
      ∀ A B, literatureD2 (F A) (F B) = literatureD2 A B := by
  unfold PreservesDistance
  simp only [distance_eq_sqrt_two_mul_d2]
  constructor
  · intro h A B
    exact mul_left_cancel₀
      (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))) (h A B)
  · intro h A B
    rw [h A B]

theorem exact_problem_equivalence : AutomaticSurjectivity ↔ LiteratureProblem := by
  unfold AutomaticSurjectivity LiteratureProblem
  simp only [preserves_iff_literature]

theorem sandwich_posSemidef (A B : PositiveDefinite n) :
    (matrixSqrt A.val * B.val * matrixSqrt A.val).PosSemidef := by
  have h := B.property.posSemidef.mul_mul_conjTranspose_same (matrixSqrt A.val)
  have hs := (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg A.val)).isHermitian
  simpa only [hs.eq] using h

theorem distance_self (A : PositiveDefinite n) : distance A A = 0 := by
  have h := matrixSqrt_mul_self A.property.posSemidef
  have hs : matrixSqrt A.val * A.val * matrixSqrt A.val = A.val * A.val := by
    calc
      _ = matrixSqrt A.val * (matrixSqrt A.val * matrixSqrt A.val) *
          matrixSqrt A.val := congrArg
            (fun X : Mat n => matrixSqrt A.val * X * matrixSqrt A.val) h.symm
      _ = (matrixSqrt A.val * matrixSqrt A.val) *
          (matrixSqrt A.val * matrixSqrt A.val) := by
        simp only [mul_assoc]
      _ = A.val * A.val := by rw [h]
  unfold distance fidelityRoot
  rw [hs, show matrixSqrt (A.val * A.val) = A.val from
    CFC.sqrt_mul_self A.val A.property.posSemidef.nonneg]
  have hz : tr A.val + tr A.val - 2 * tr A.val = 0 := by ring
  rw [hz, Real.sqrt_zero]

/-- The algebraic zero-curvature criterion used by the informal quotient argument.
This does not assert or assume O'Neill's geometric formula. -/
theorem hermitian_commutator_iff_commute {K L : Mat n}
    (hK : K.IsHermitian) (hL : L.IsHermitian) :
    (K * L - L * K).IsHermitian ↔ Commute K L := by
  constructor
  · intro h
    have hn : -(K * L - L * K) = K * L - L * K := by
      simpa only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
        hK.eq, hL.eq, neg_sub] using h.eq
    have hz : K * L - L * K = 0 := by
      ext i j
      have hij : -((K * L - L * K) i j) = (K * L - L * K) i j :=
        congrArg (fun M : Mat n => M i j) hn
      exact CharZero.neg_eq_self_iff.mp hij
    exact sub_eq_zero.mp hz
  · intro h
    rw [show K * L = L * K from h.eq, sub_self]
    exact Matrix.isHermitian_zero

#print axioms matrixSqrt_mul_self
#print axioms matrixSqrt_unique
#print axioms exact_problem_equivalence
#print axioms sandwich_posSemidef
#print axioms distance_self
#print axioms hermitian_commutator_iff_commute

end Bures

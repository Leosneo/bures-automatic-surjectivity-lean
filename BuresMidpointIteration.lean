import BuresNormalChart

/-! Exact dyadic contraction in normal coordinates, transported by every
isometry of the literal Bures distance. -/
noncomputable section
open scoped MatrixOrder ComplexOrder Matrix.Norms.Frobenius
namespace Bures

def canonicalMidpoint (A B : PositiveDefinite n) : PositiveDefinite n :=
  Classical.choose (metric_midpoint_exists A B)

theorem canonicalMidpoint_spec (A B : PositiveDefinite n) :
    IsMetricMidpoint A (canonicalMidpoint A B) B :=
  Classical.choose_spec (metric_midpoint_exists A B)

theorem map_canonicalMidpoint (F : PositiveDefinite n → PositiveDefinite n)
    (hF : PreservesDistance F) (A B : PositiveDefinite n) :
    F (canonicalMidpoint A B) = canonicalMidpoint (F A) (F B) :=
  metric_midpoint_unique _ _ (maps_metric_midpoint F hF (canonicalMidpoint_spec A B))
    (canonicalMidpoint_spec (F A) (F B))

def midpointIteration (A B : PositiveDefinite n) : ℕ → PositiveDefinite n
  | 0 => B
  | k + 1 => canonicalMidpoint A (midpointIteration A B k)

theorem map_midpointIteration (F : PositiveDefinite n → PositiveDefinite n)
    (hF : PreservesDistance F) (A B : PositiveDefinite n) (k : ℕ) :
    F (midpointIteration A B k) = midpointIteration (F A) (F B) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [midpointIteration, map_canonicalMidpoint F hF, ih]

theorem normalCoordinate_midpointIteration (A B : PositiveDefinite n) (k : ℕ) :
    normalCoordinate A (midpointIteration A B k) =
      ((1 / 2 : ℝ) ^ k) • normalCoordinate A B := by
  induction k with
  | zero =>
    apply Subtype.ext
    change (normalCoordinate A B).val = ((1 / 2 : ℝ) ^ 0) • (normalCoordinate A B).val
    ext i j
    simp [Matrix.smul_apply, Complex.real_smul]
  | succ k ih =>
    rw [midpointIteration, normalCoordinate_midpoint _ _ _ (canonicalMidpoint_spec _ _), ih]
    apply Subtype.ext
    change (1 / 2 : ℝ) • (((1 / 2 : ℝ) ^ k) • (normalCoordinate A B).val) =
      ((1 / 2 : ℝ) ^ (k + 1)) • (normalCoordinate A B).val
    ext i j
    simp only [Matrix.smul_apply, Complex.real_smul, pow_succ, Complex.ofReal_mul]
    ring

theorem normalTransport_midpointIteration (A B : PositiveDefinite n) (k : ℕ) :
    normalTransport A (midpointIteration A B k) =
      1 + ((1 / 2 : ℝ) ^ k) • (normalTransport A B - 1) := by
  have h := congrArg Subtype.val (normalCoordinate_midpointIteration A B k)
  change normalTransport A (midpointIteration A B k) - 1 =
    ((1 / 2 : ℝ) ^ k) • (normalTransport A B - 1) at h
  rw [← h]
  abel

theorem optimalLift_midpointIteration (A B : PositiveDefinite n) (k : ℕ) :
    optimalLift A (midpointIteration A B k) = matrixSqrt A.val +
      ((1 / 2 : ℝ) ^ k) • (optimalLift A B - matrixSqrt A.val) := by
  rw [← normalTransport_mul_sqrt, normalTransport_midpointIteration,
    add_mul, one_mul, smul_mul_assoc, sub_mul, one_mul,
    normalTransport_mul_sqrt]

theorem midpointIteration_gram (A B : PositiveDefinite n) (k : ℕ) :
    (midpointIteration A B k).val =
      gram (matrixSqrt A.val + ((1 / 2 : ℝ) ^ k) •
        (optimalLift A B - matrixSqrt A.val)) := by
  rw [← optimalLift_midpointIteration, optimalLift_gram]

theorem distance_midpointIteration (A B : PositiveDefinite n) (k : ℕ) :
    distance A (midpointIteration A B k) = ((1 / 2 : ℝ) ^ k) * distance A B := by
  induction k with
  | zero => simp [midpointIteration]
  | succ k ih =>
    rw [midpointIteration, (canonicalMidpoint_spec A (midpointIteration A B k)).1, ih]
    simp only [pow_succ]
    ring

#print axioms map_midpointIteration
#print axioms normalCoordinate_midpointIteration
#print axioms optimalLift_midpointIteration
#print axioms midpointIteration_gram
end Bures

import BuresQuotientGeodesic

/-! Distance-preserving maps preserve constant-speed Bures geodesics and
metric midpoints. This does not establish uniqueness of geodesics or smoothness
of the map. -/

noncomputable section
open scoped MatrixOrder ComplexOrder Matrix.Norms.Frobenius
namespace Bures

/-- A parametrized geodesic expressed entirely through the explicit Bures
distance, with no differential-geometric assumptions. -/
def IsConstantSpeedGeodesic (γ : Set.Icc (0 : ℝ) 1 → PositiveDefinite n)
    (A B : PositiveDefinite n) : Prop :=
  γ ⟨0, by norm_num⟩ = A ∧ γ ⟨1, by norm_num⟩ = B ∧
    ∀ s t, distance (γ s) (γ t) = |s.val - t.val| * distance A B

theorem exists_metric_geodesic (A B : PositiveDefinite n) :
    ∃ γ, IsConstantSpeedGeodesic γ A B :=
  exists_constant_speed_geodesic A B

/-- Any literal-distance isometry transports a constant-speed geodesic to
one of its image endpoints. -/
theorem maps_constant_speed_geodesic
    (F : PositiveDefinite n → PositiveDefinite n) (hF : PreservesDistance F)
    {γ : Set.Icc (0 : ℝ) 1 → PositiveDefinite n} {A B : PositiveDefinite n}
    (hγ : IsConstantSpeedGeodesic γ A B) :
    IsConstantSpeedGeodesic (F ∘ γ) (F A) (F B) := by
  rcases hγ with ⟨hzero, hone, hdist⟩
  refine ⟨congrArg F hzero, congrArg F hone, ?_⟩
  intro s t
  change distance (F (γ s)) (F (γ t)) = _
  rw [hF, hdist, hF]

/-- Midpoint in the literal metric, defined by its two equal half-distances. -/
def IsMetricMidpoint (A M B : PositiveDefinite n) : Prop :=
  distance A M = distance A B / 2 ∧ distance M B = distance A B / 2

theorem metric_midpoint_exists (A B : PositiveDefinite n) :
    ∃ M, IsMetricMidpoint A M B := by
  obtain ⟨γ, h0, h1, hdist⟩ := exists_constant_speed_geodesic A B
  let z : Set.Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
  let o : Set.Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩
  let m : Set.Icc (0 : ℝ) 1 := ⟨1 / 2, by norm_num⟩
  refine ⟨γ m, ?_, ?_⟩
  · calc
      distance A (γ m) = distance (γ z) (γ m) := by rw [show γ z = A from h0]
      _ = distance A B / 2 := by rw [hdist]; norm_num [z, m]; ring
  · calc
      distance (γ m) B = distance (γ m) (γ o) := by rw [show γ o = B from h1]
      _ = distance A B / 2 := by rw [hdist]; norm_num [m, o]; ring

theorem maps_metric_midpoint
    (F : PositiveDefinite n → PositiveDefinite n) (hF : PreservesDistance F)
    {A M B : PositiveDefinite n} (hM : IsMetricMidpoint A M B) :
    IsMetricMidpoint (F A) (F M) (F B) := by
  rcases hM with ⟨hAM, hMB⟩
  constructor
  · rw [hF, hF]
    exact hAM
  · rw [hF, hF]
    exact hMB

#print axioms exists_metric_geodesic
#print axioms maps_constant_speed_geodesic
#print axioms metric_midpoint_exists
#print axioms maps_metric_midpoint

end Bures

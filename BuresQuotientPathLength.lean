import BuresQuotientGeodesic
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! The quotient Frobenius length metric, expressed as an infimum over
continuously differentiable curves of invertible matrix factors. This is an intrinsic length
construction on the quotient by right unitary multiplication. The file does
not identify this length with an independently defined quotient Riemannian
tensor; that requires horizontal lifting and a length-preservation theorem. -/

noncomputable section
open scoped MatrixOrder ComplexOrder Matrix.Norms.Frobenius NNReal ENNReal
open Matrix
namespace Bures

/-- A path in the invertible factor space with prescribed Gram endpoints. -/
structure FrobeniusLiftPath (A B : PositiveDefinite n) where
  lift : ℝ → Mat n
  smooth : ContDiffOn ℝ 1 lift (Set.Icc 0 1)
  invertible : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsUnit (lift t)
  start : lift 0 * (lift 0)ᴴ = A.val
  finish : lift 1 * (lift 1)ᴴ = B.val

def FrobeniusLiftPath.length {A B : PositiveDefinite n}
    (p : FrobeniusLiftPath A B) : ℝ≥0∞ :=
  eVariationOn p.lift (Set.Icc (0 : ℝ) 1)

/-- The quotient path distance is the infimum of Frobenius lengths among
invertible factor paths whose Gram endpoints are A and B. -/
def quotientFrobeniusPathDistance (A B : PositiveDefinite n) : ℝ≥0∞ :=
  ⨅ p : FrobeniusLiftPath A B, p.length

private theorem norm_real_smul (r : ℝ) (M : Mat n) :
    ‖r • M‖ = |r| * ‖M‖ := by
  have h : r • M = (r : ℂ) • M := by
    ext i j
    simp [Matrix.smul_apply, Complex.real_smul]
  rw [h, norm_smul, Complex.norm_real, Real.norm_eq_abs]

private theorem affine_factor_lipschitz (X Y : Mat n) :
    LipschitzOnWith ⟨‖X - Y‖, norm_nonneg _⟩
      (fun t : ℝ => (1 - t) • X + t • Y) (Set.Icc (0 : ℝ) 1) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  have hd : ((1 - s) • X + s • Y) - ((1 - t) • X + t • Y) =
      (t - s) • (X - Y) := by
    ext i j
    simp [Matrix.smul_apply, Complex.real_smul]
    ring
  rw [dist_eq_norm, hd, norm_real_smul, Real.dist_eq, abs_sub_comm]
  simpa only [NNReal.coe_mk, mul_comm] using
    (le_refl (|s - t| * ‖X - Y‖))

private theorem affine_factor_variation_le (X Y : Mat n) :
    eVariationOn (fun t : ℝ => (1 - t) • X + t • Y) (Set.Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal ‖X - Y‖ := by
  let C : ℝ≥0 := ⟨‖X - Y‖, norm_nonneg _⟩
  have hLip : LipschitzOnWith C
      (fun t : ℝ => (1 - t) • X + t • Y) (Set.Icc (0 : ℝ) 1) :=
    affine_factor_lipschitz X Y
  have hId : eVariationOn (fun t : ℝ => t) (Set.Icc (0 : ℝ) 1) ≤ 1 := by
    have h := (monotone_id.monotoneOn Set.univ).eVariationOn_le
      (show (0 : ℝ) ∈ Set.univ by trivial)
      (show (1 : ℝ) ∈ Set.univ by trivial)
    simpa using h
  have h := hLip.comp_eVariationOn_le (g := id)
    (s := Set.Icc (0 : ℝ) 1) (fun _ ht => ht)
  simpa [Function.comp_def, C] using h.trans (mul_le_mul_right hId _)

theorem distance_le_lift_path_length {A B : PositiveDefinite n}
    (p : FrobeniusLiftPath A B) :
    ENNReal.ofReal (distance A B) ≤ p.length := by
  have h0 := p.invertible 0 (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)
  have h1 := p.invertible 1 (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1)
  have hAB := distance_le_frobenius_factors (p.lift 0) (p.lift 1) h0 h1
  have hAeq : (⟨p.lift 0 * (p.lift 0)ᴴ,
      Matrix.PosDef.mul_conjTranspose_self (p.lift 0)
        (Matrix.vecMul_injective_of_isUnit h0)⟩ : PositiveDefinite n) = A :=
    Subtype.ext p.start
  have hBeq : (⟨p.lift 1 * (p.lift 1)ᴴ,
      Matrix.PosDef.mul_conjTranspose_self (p.lift 1)
        (Matrix.vecMul_injective_of_isUnit h1)⟩ : PositiveDefinite n) = B :=
    Subtype.ext p.finish
  rw [hAeq, hBeq] at hAB
  have hvar := eVariationOn.edist_le p.lift
    (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num)
  rw [edist_dist, dist_eq_norm] at hvar
  exact (ENNReal.ofReal_le_ofReal hAB).trans hvar

private theorem optimal_affine_lift_path (A B : PositiveDefinite n) :
    ∃ p : FrobeniusLiftPath A B,
      p.length ≤ ENNReal.ofReal (distance A B) := by
  obtain ⟨U, hUl, hUr, hd, hseg⟩ := optimal_alignment_invertible_segment A B
  let X := matrixSqrt A.val
  let Y := matrixSqrt B.val * U
  let W (t : ℝ) : Mat n := (1 - t) • X + t • Y
  have hW0 : W 0 = X := by
    ext i j
    simp [W, Matrix.smul_apply]
  have hW1 : W 1 = Y := by
    ext i j
    simp [W, Matrix.smul_apply]
  let p : FrobeniusLiftPath A B := {
    lift := W
    smooth := by
      apply ContDiff.contDiffOn
      dsimp [W]
      exact (((contDiff_const.sub contDiff_id).smul_const X).add
        (contDiff_id.smul_const Y))
    invertible := by
      intro t ht
      exact hseg t ht.1 ht.2
    start := by
      rw [hW0, (Matrix.nonneg_iff_posSemidef.mp
        (matrixSqrt_nonneg A.val)).isHermitian.eq]
      exact matrixSqrt_mul_self A.property.posSemidef
    finish := by
      rw [hW1, Matrix.conjTranspose_mul]
      simp only [Y, mul_assoc]
      rw [← mul_assoc U Uᴴ, hUr, one_mul,
        (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg B.val)).isHermitian.eq]
      exact matrixSqrt_mul_self B.property.posSemidef
  }
  refine ⟨p, ?_⟩
  change eVariationOn W (Set.Icc (0 : ℝ) 1) ≤ ENNReal.ofReal (distance A B)
  have h := affine_factor_variation_le X Y
  change distance A B = ‖X - Y‖ at hd
  simpa only [W, ← hd] using h

/-- The literal Bures distance is exactly the quotient lift-length distance
of Frobenius curves of invertible factors, in extended nonnegative reals. -/
theorem distance_eq_quotientFrobeniusPathDistance (A B : PositiveDefinite n) :
    ENNReal.ofReal (distance A B) = quotientFrobeniusPathDistance A B := by
  apply le_antisymm
  · exact le_iInf fun p => distance_le_lift_path_length p
  · obtain ⟨p, hp⟩ := optimal_affine_lift_path A B
    exact (iInf_le (fun p : FrobeniusLiftPath A B => p.length) p).trans hp

#print axioms distance_le_lift_path_length
#print axioms distance_eq_quotientFrobeniusPathDistance

end Bures

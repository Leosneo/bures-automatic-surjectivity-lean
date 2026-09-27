import BuresTopology
import BuresRadicand
import BuresInterior
import BuresTriangle
import BuresSymmetry
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open scoped MatrixOrder ComplexOrder Topology
open Filter
namespace Bures

abbrev PSD (n : ℕ) := {A : Mat n // A.PosSemidef}

def regularize (A : PSD n) (m : ℕ) : PositiveDefinite n :=
  ⟨A.val + (1 / ((m : ℝ) + 1)) • (1 : Mat n),
    Matrix.PosDef.posSemidef_add A.property
      (Matrix.PosDef.one.smul (by positivity : (0 : ℝ) < 1 / ((m : ℝ) + 1)))⟩

theorem tendsto_regularize (A : PSD n) :
    Tendsto (fun m => ((⟨(regularize A m).val, (regularize A m).property.posSemidef⟩)
      : PSD n)) atTop (𝓝 A) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have ht := Complex.continuous_ofReal.tendsto 0 |>.comp
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h := (tendsto_const_nhds (x := A.val i j)).add
    (ht.mul (tendsto_const_nhds (x := (1 : Mat n) i j)))
  simpa [regularize, Matrix.add_apply, Matrix.smul_apply,
    Complex.real_smul] using h

theorem radicand_nonneg_psd (A B : PSD n) :
    0 ≤ tr A.val + tr B.val - 2 * fidelityRoot A.val B.val := by
  have hA := tendsto_regularize A
  have hB := tendsto_regularize B
  have hf := continuous_fidelityRoot_psd.tendsto (A, B) |>.comp (hA.prodMk_nhds hB)
  have htrA := continuous_tr.tendsto A.val |>.comp (tendsto_subtype_rng.mp hA)
  have htrB := continuous_tr.tendsto B.val |>.comp (tendsto_subtype_rng.mp hB)
  exact ge_of_tendsto (htrA.add htrB |>.sub (tendsto_const_nhds.mul hf))
    (Filter.Eventually.of_forall fun m => radicand_nonneg (regularize A m) (regularize B m))

/-- Literal Bures distance on the positive semidefinite cone. -/
def psdDistance (A B : PSD n) : ℝ :=
  Real.sqrt (tr A.val + tr B.val - 2 * fidelityRoot A.val B.val)

theorem continuous_psdDistance :
    Continuous (fun p : PSD n × PSD n => psdDistance p.1 p.2) := by
  exact Real.continuous_sqrt.comp
    (((continuous_tr.comp (continuous_subtype_val.comp continuous_fst)).add
      (continuous_tr.comp (continuous_subtype_val.comp continuous_snd))).sub
        (continuous_const.mul continuous_fidelityRoot_psd))

theorem tendsto_psdDistance_regularize (A B : PSD n) :
    Tendsto (fun m => distance (regularize A m) (regularize B m)) atTop
      (𝓝 (psdDistance A B)) := by
  have hA := tendsto_regularize A
  have hB := tendsto_regularize B
  have hf := continuous_fidelityRoot_psd.tendsto (A, B) |>.comp (hA.prodMk_nhds hB)
  have htrA := continuous_tr.tendsto A.val |>.comp (tendsto_subtype_rng.mp hA)
  have htrB := continuous_tr.tendsto B.val |>.comp (tendsto_subtype_rng.mp hB)
  have h := Real.continuous_sqrt.tendsto
    (tr A.val + tr B.val - 2 * fidelityRoot A.val B.val) |>.comp
      (htrA.add htrB |>.sub (tendsto_const_nhds.mul hf))
  exact h

theorem psdDistance_nonneg (A B : PSD n) : 0 ≤ psdDistance A B := Real.sqrt_nonneg _

theorem psdDistance_self (A : PSD n) : psdDistance A A = 0 := by
  have h := tendsto_psdDistance_regularize A A
  simp only [distance_self] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

theorem psdDistance_comm (A B : PSD n) : psdDistance A B = psdDistance B A := by
  have h := tendsto_psdDistance_regularize A B
  have he (m : ℕ) : distance (regularize A m) (regularize B m) =
      distance (regularize B m) (regularize A m) := by
    simp only [distance, fidelityRoot_comm (regularize A m) (regularize B m), add_comm]
  simp only [he] at h
  exact tendsto_nhds_unique h (tendsto_psdDistance_regularize B A)

theorem psdDistance_triangle (A B C : PSD n) :
    psdDistance A C ≤ psdDistance A B + psdDistance B C := by
  exact le_of_tendsto_of_tendsto (tendsto_psdDistance_regularize A C)
    ((tendsto_psdDistance_regularize A B).add (tendsto_psdDistance_regularize B C))
    (Filter.Eventually.of_forall fun m =>
      distance_triangle (regularize A m) (regularize B m) (regularize C m))

theorem psdDistance_sq (A B : PSD n) :
    psdDistance A B ^ 2 = tr A.val + tr B.val - 2 * fidelityRoot A.val B.val :=
  Real.sq_sqrt (radicand_nonneg_psd A B)

def psdZero : PSD n := ⟨0, Matrix.PosSemidef.zero⟩

theorem psdDistance_zero (A : PSD n) : psdDistance A psdZero = Real.sqrt (tr A.val) := by
  simp [psdDistance, psdZero, fidelityRoot, matrixSqrt, tr]

/-- Fixing the cone origin recovers trace from the explicit squared distance. -/
theorem preserves_trace_of_psdZero_fixed (F : PSD n → PSD n)
    (hF : ∀ A B, psdDistance (F A) (F B) = psdDistance A B)
    (hzero : F psdZero = psdZero) (A : PSD n) : tr (F A).val = tr A.val := by
  have h := hF A psdZero
  rw [hzero, psdDistance_zero, psdDistance_zero] at h
  exact (Real.sqrt_inj (tr_nonneg (F A).property) (tr_nonneg A.property)).mp h

/-- Squared Bures distance and trace determine the literal fidelity. -/
theorem preserves_fidelity_of_psdZero_fixed (F : PSD n → PSD n)
    (hF : ∀ A B, psdDistance (F A) (F B) = psdDistance A B)
    (hzero : F psdZero = psdZero) (A B : PSD n) :
    fidelityRoot (F A).val (F B).val = fidelityRoot A.val B.val := by
  have h := congrArg (fun x : ℝ => x ^ 2) (hF A B)
  dsimp only at h
  rw [psdDistance_sq, psdDistance_sq,
    preserves_trace_of_psdZero_fixed F hF hzero A,
    preserves_trace_of_psdZero_fixed F hF hzero B] at h
  linarith

#print axioms psdDistance_triangle
#print axioms radicand_nonneg_psd
#print axioms preserves_fidelity_of_psdZero_fixed
end Bures

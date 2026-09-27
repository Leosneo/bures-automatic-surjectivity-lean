import BuresExtension
import BuresApexFourPoint
import HermitianFiniteDimension
import BuresNormalChart
import BuresSquareTranslation
import BuresNormalForm

/-! Blow-down transfer for the actual semidefinite Bures metric.
The normal-chart affine form is rescaled to a homogeneous isometry,
first on positive definite inputs and then on the full PSD cone. -/

noncomputable section
open scoped MatrixOrder ComplexOrder Topology
open Filter
open Matrix
namespace Bures

local instance : MetricSpace (PSD n) := psdMetricSpace n

/-- Pointwise limits of literal Bures isometries preserve the literal
distance. The hypothesis explicitly includes convergence of every matrix. -/
theorem psd_isometry_of_pointwise_limit
    (E : ℕ → PSD n → PSD n) (Φ : PSD n → PSD n)
    (hE : ∀ k A B, psdDistance (E k A) (E k B) = psdDistance A B)
    (hlim : ∀ A, Tendsto (fun k => E k A) atTop (𝓝 (Φ A))) :
    ∀ A B, psdDistance (Φ A) (Φ B) = psdDistance A B := by
  intro A B
  have h := continuous_psdDistance.tendsto (Φ A, Φ B) |>.comp
    ((hlim A).prodMk_nhds (hlim B))
  have he : (fun k => psdDistance (E k A) (E k B)) =
      fun _ : ℕ => psdDistance A B := by
    funext k
    exact hE k A B
  have h' : Tendsto (fun k => psdDistance (E k A) (E k B))
      atTop (𝓝 (psdDistance (Φ A) (Φ B))) := by
    simpa only [Function.comp_def] using h
  rw [he] at h'
  exact tendsto_nhds_unique h' tendsto_const_nhds

/-- For an equicontinuous family of literal isometries, pointwise convergence
on positive-definite matrices determines pointwise convergence on the whole
PSD completion. -/
theorem psd_isometry_limit_of_dense_pd
    (E : ℕ → PSD n → PSD n) (Φ : PSD n → PSD n)
    (hE : ∀ k A B, psdDistance (E k A) (E k B) = psdDistance A B)
    (hΦ : Continuous Φ)
    (hpd : ∀ B : PositiveDefinite n,
      Tendsto (fun k => E k (pdInclusion B)) atTop (𝓝 (Φ (pdInclusion B)))) :
    ∀ X, Tendsto (fun k => E k X) atTop (𝓝 (Φ X)) := by
  intro X
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨δ, hδ, hclose⟩ :=
    (Metric.continuousAt_iff.mp (hΦ.continuousAt (x := X))) (ε / 3) hε3
  obtain ⟨B, hXB⟩ := denseRange_pdInclusion.exists_dist_lt X
    (lt_min hε3 hδ)
  have hφ : dist (Φ (pdInclusion B)) (Φ X) < ε / 3 := by
    apply hclose
    rw [dist_comm]
    exact lt_of_lt_of_le hXB (min_le_right _ _)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hpd B) (ε / 3) hε3
  refine ⟨N, fun k hk => ?_⟩
  have hEB : dist (E k X) (E k (pdInclusion B)) < ε / 3 := by
    change psdDistance (E k X) (E k (pdInclusion B)) < ε / 3
    rw [hE]
    exact lt_of_lt_of_le hXB (min_le_left _ _)
  have hmid := hN k hk
  calc
    dist (E k X) (Φ X) ≤
        dist (E k X) (E k (pdInclusion B)) +
          dist (E k (pdInclusion B)) (Φ X) := dist_triangle _ _ _
    _ ≤ dist (E k X) (E k (pdInclusion B)) +
          (dist (E k (pdInclusion B)) (Φ (pdInclusion B)) +
            dist (Φ (pdInclusion B)) (Φ X)) := by
              gcongr
              exact dist_triangle _ _ _
    _ < ε := by linarith

/-- A semidefinite Bures self-isometry fixing the cone origin is onto.
The proof uses the proper compact trace sublevels of the literal metric. -/
theorem psd_isometry_surjective_of_zero_fixed
    (Φ : PSD n → PSD n)
    (hΦ : ∀ A B, psdDistance (Φ A) (Φ B) = psdDistance A B)
    (hzero : Φ psdZero = psdZero) : Function.Surjective Φ := by
  have htr : ∀ A, tr (Φ A).val = tr A.val :=
    preserves_trace_of_psdZero_fixed Φ hΦ hzero
  exact BuresSupport.surjective_of_preserves_compact_sublevels
    (fun A : PSD n => tr A.val) isCompact_psd_sublevel
    (Isometry.of_dist_eq hΦ) htr

/-- The candidate blow-down built from a real-linear Hermitian normal-chart
map and a positive centre. It is PSD for every input, whether or not the
linear map preserves the positive cone. -/
def normalBlowdownModel (L : Hermitian n →ₗ[ℝ] Hermitian n)
    (C : PositiveDefinite n) (X : PSD n) : PSD n := by
  let R : Hermitian n := ⟨matrixSqrt X.val,
    (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg X.val)).isHermitian⟩
  let K := L R
  exact ⟨K.val * C.val * K.val,
    by
      have hK : (K.val)ᴴ = K.val := by
        simpa only [Matrix.star_eq_conjTranspose] using K.property
      simpa only [hK] using
        C.property.posSemidef.mul_mul_conjTranspose_same K.val⟩

set_option backward.isDefEq.respectTransparency false
theorem continuous_normalBlowdownModel
    (L : Hermitian n →ₗ[ℝ] Hermitian n)
    (C : PositiveDefinite n) : Continuous (normalBlowdownModel L C) := by
  have hroot : Continuous (fun X : PSD n =>
      (⟨matrixSqrt X.val,
        (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg X.val)).isHermitian⟩ :
        Hermitian n)) :=
    continuous_matrixSqrt_psd.subtype_mk _
  have hK : Continuous (fun X : PSD n => L
      (⟨matrixSqrt X.val,
        (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg X.val)).isHermitian⟩ :
        Hermitian n)) :=
    L.continuous_of_finiteDimensional.comp hroot
  apply continuous_iff_continuousAt.mpr
  intro X
  have hM : Continuous (fun X : PSD n =>
      (L (⟨matrixSqrt X.val,
        (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg X.val)).isHermitian⟩ :
        Hermitian n)).val * C.val *
      (L (⟨matrixSqrt X.val,
        (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg X.val)).isHermitian⟩ :
        Hermitian n)).val) :=
    ((continuous_subtype_val.comp hK).mul continuous_const).mul
      (continuous_subtype_val.comp hK)
  exact hM.subtype_mk _ |>.continuousAt
set_option backward.isDefEq.respectTransparency true

theorem normalBlowdownModel_zero (L : Hermitian n →ₗ[ℝ] Hermitian n)
    (C : PositiveDefinite n) : normalBlowdownModel L C psdZero = psdZero := by
  apply Subtype.ext
  change (L (⟨matrixSqrt (0 : Mat n), _⟩ : Hermitian n)).val * C.val *
    (L (⟨matrixSqrt (0 : Mat n), _⟩ : Hermitian n)).val = 0
  have hR : (⟨matrixSqrt (0 : Mat n),
      (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg (0 : Mat n))).isHermitian⟩ :
      Hermitian n) = 0 := by
    apply Subtype.ext
    simp [matrixSqrt]
  rw [hR, map_zero]
  simp

/-- Rescale a PSD self-map around the cone apex. -/
def rescaledPsdMap (E : PSD n → PSD n) (t : ℝ) (ht : 0 < t)
    (X : PSD n) : PSD n :=
  psdScale t⁻¹ (inv_nonneg.mpr ht.le) (E (psdScale t ht.le X))

theorem rescaledPsdMap_isometry (E : PSD n → PSD n)
    (hE : ∀ X Y, psdDistance (E X) (E Y) = psdDistance X Y)
    (t : ℝ) (ht : 0 < t) (X Y : PSD n) :
    psdDistance (rescaledPsdMap E t ht X) (rescaledPsdMap E t ht Y) =
      psdDistance X Y := by
  unfold rescaledPsdMap
  rw [psdDistance_scale_pair (hc := inv_nonneg.mpr ht.le), hE,
    psdDistance_scale_pair (hc := ht.le), Real.sqrt_inv t]
  have hs : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ht)
  simp [hs]

set_option backward.isDefEq.respectTransparency false
/-- Positivity of all normal-chart factors forces the linear part to preserve
the closed positive cone. Scaling a positive input to infinity removes the
constant term of the affine chart. -/
theorem linear_posSemidef_of_positive_chart
    (L : Hermitian n →ₗ[ℝ] Hermitian n)
    (hchart : ∀ (T : Hermitian n), T.val.PosDef →
      ((⟨1, Matrix.isHermitian_one⟩ : Hermitian n) +
        L (T - (⟨1, Matrix.isHermitian_one⟩ : Hermitian n))).val.PosDef)
    (T : Hermitian n) (hT : T.val.PosDef) : (L T).val.PosSemidef := by
  let I : Hermitian n := ⟨1, Matrix.isHermitian_one⟩
  let W : Hermitian n := I - L I
  have hpos (k : ℕ) :
      ((↑(k + 1) : ℝ) • (L T) + W).val.PosDef := by
    have hscaled : ((↑(k + 1) : ℝ) • T).val.PosDef :=
      hT.smul (by exact_mod_cast Nat.succ_pos k)
    have he : (↑(k + 1) : ℝ) • L T + W =
        I + L ((↑(k + 1) : ℝ) • T - I) := by
      rw [map_sub, map_smul]
      dsimp [W]
      module
    simpa only [he] using hchart ((↑(k + 1) : ℝ) • T) hscaled
  have hnonneg (k : ℕ) :
      0 ≤ (L T).val + (↑(k + 1) : ℝ)⁻¹ • W.val := by
    have hk : (0 : ℝ) < ↑(k + 1) := by exact_mod_cast Nat.succ_pos k
    have hs : (0 : ℝ) < (↑(k + 1) : ℝ)⁻¹ := inv_pos.mpr hk
    have hp' := ((hpos k).smul hs).posSemidef.nonneg
    convert hp' using 1
    change (L T).val + (↑(k + 1) : ℝ)⁻¹ • W.val =
      (↑(k + 1) : ℝ)⁻¹ •
        ((↑(k + 1) : ℝ) • (L T).val + W.val)
    rw [smul_add, smul_smul]
    rw [inv_mul_cancel₀ (ne_of_gt hk), one_smul]
  have htend : Tendsto (fun k : ℕ =>
      (L T).val + (↑(k + 1) : ℝ)⁻¹ • W.val) atTop (𝓝 (L T).val) := by
    have hinv : Tendsto (fun k : ℕ => (↑(k + 1) : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa [one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using tendsto_const_nhds.add (hinv.smul_const W.val)
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (L T).property
  intro x
  have hc : Continuous (fun M : Mat n => star x ⬝ᵥ (M *ᵥ x)) := by fun_prop
  have hq := hc.tendsto (L T).val |>.comp htend
  have he : ∀ k : ℕ, 0 ≤ star x ⬝ᵥ
      (((L T).val + (↑(k + 1) : ℝ)⁻¹ • W.val) *ᵥ x) := by
    intro k
    exact ((Matrix.nonneg_iff_posSemidef.mp (hnonneg k)).dotProduct_mulVec_nonneg x)
  exact isClosed_Ici.mem_of_tendsto hq (Filter.Eventually.of_forall he)
set_option backward.isDefEq.respectTransparency true

/-- Once the blow-down excludes singular images of positive inputs, the
positive normal-chart condition upgrades semidefinite to definite. -/
theorem linear_posDef_of_positive_chart_and_unit
    (L : Hermitian n →ₗ[ℝ] Hermitian n)
    (hchart : ∀ (T : Hermitian n), T.val.PosDef →
      ((⟨1, Matrix.isHermitian_one⟩ : Hermitian n) +
        L (T - (⟨1, Matrix.isHermitian_one⟩ : Hermitian n))).val.PosDef)
    (hunit : ∀ (T : Hermitian n), T.val.PosDef → IsUnit (L T).val)
    (T : Hermitian n) (hT : T.val.PosDef) : (L T).val.PosDef := by
  classical
  exact (linear_posSemidef_of_positive_chart L hchart T hT).posDef_iff_isUnit.mpr
    (hunit T hT)

set_option backward.isDefEq.respectTransparency false
/-- The affine normal factor has the expected homogeneous blow-down. -/
theorem tendsto_affine_normal_factor
    (L : Hermitian n →ₗ[ℝ] Hermitian n) (T : Hermitian n) :
    Tendsto (fun k : ℕ =>
      (↑(k + 1) : ℝ)⁻¹ •
        ((⟨1, Matrix.isHermitian_one⟩ : Hermitian n) +
          L ((↑(k + 1) : ℝ) • T -
            (⟨1, Matrix.isHermitian_one⟩ : Hermitian n))))
      atTop (𝓝 (L T)) := by
  let I : Hermitian n := ⟨1, Matrix.isHermitian_one⟩
  let W : Hermitian n := I - L I
  have he (k : ℕ) :
      (↑(k + 1) : ℝ)⁻¹ • (I + L ((↑(k + 1) : ℝ) • T - I)) =
      L T + (↑(k + 1) : ℝ)⁻¹ • W := by
    have hk : (0 : ℝ) < ↑(k + 1) := by exact_mod_cast Nat.succ_pos k
    have hs : (↑(k + 1) : ℝ)⁻¹ * ↑(k + 1) = 1 :=
      inv_mul_cancel₀ (ne_of_gt hk)
    simp only [map_sub, map_smul, smul_add, smul_sub, smul_smul]
    rw [hs, one_smul]
    dsimp [W]
    module
  have hinv : Tendsto (fun k : ℕ => (↑(k + 1) : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have ht : Tendsto (fun k : ℕ =>
      L T + (↑(k + 1) : ℝ)⁻¹ • W) atTop (𝓝 (L T)) := by
    simpa using (tendsto_const_nhds (x := L T)).add (hinv.smul_const W)
  exact ht.congr' (Filter.Eventually.of_forall fun k => (he k).symm)
set_option backward.isDefEq.respectTransparency true

/-- Matrix congruence of the affine normal factor converges to the quadratic
homogeneous model. This is the analytic core of the blow-down calculation. -/
theorem tendsto_affine_normal_congruence
    (L : Hermitian n →ₗ[ℝ] Hermitian n) (C : PositiveDefinite n)
    (T : Hermitian n) :
    Tendsto (fun k : ℕ =>
      let R : Hermitian n :=
        (↑(k + 1) : ℝ)⁻¹ •
          ((⟨1, Matrix.isHermitian_one⟩ : Hermitian n) +
            L ((↑(k + 1) : ℝ) • T -
              (⟨1, Matrix.isHermitian_one⟩ : Hermitian n)))
      R.val * C.val * R.val) atTop
      (𝓝 ((L T).val * C.val * (L T).val)) := by
  have h := (continuous_subtype_val.tendsto (L T)).comp
    (tendsto_affine_normal_factor L T)
  exact (h.mul tendsto_const_nhds).mul h

/-- On the open cone, the affine normal form has the asserted literal PSD
blow-down. This input only specifies the value on square points. -/
theorem normalBlowdown_limit_pd_of_affine_form
    (E : PSD n → PSD n)
    (L : Hermitian n →ₗ[ℝ] Hermitian n) (C : PositiveDefinite n)
    (hform : ∀ (T : Hermitian n) (hT : T.val.PosDef),
      let P := ((⟨1, Matrix.isHermitian_one⟩ : Hermitian n) +
        L (T - (⟨1, Matrix.isHermitian_one⟩ : Hermitian n))).val
      (E (pdInclusion (squarePoint T.val hT))).val = P * C.val * P)
    (B : PositiveDefinite n) :
    Tendsto (fun k : ℕ =>
      rescaledPsdMap E ((↑(k + 1) : ℝ) ^ 2)
        (sq_pos_of_pos (by exact_mod_cast Nat.succ_pos k)) (pdInclusion B))
      atTop (𝓝 (normalBlowdownModel L C (pdInclusion B))) := by
  let T : Hermitian n := ⟨matrixSqrt B.val,
    (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg B.val)).isHermitian⟩
  have hT : T.val.PosDef := by
    change (matrixSqrt B.val).PosDef
    exact B.property.isStrictlyPositive.sqrt.posDef
  have hTsq : T.val * T.val = B.val := matrixSqrt_mul_self B.property.posSemidef
  have hm := tendsto_affine_normal_congruence L C T
  rw [tendsto_subtype_rng]
  convert hm using 1
  · funext k
    let s : ℝ := ↑(k + 1)
    have hs : 0 < s := by dsimp [s]; exact_mod_cast Nat.succ_pos k
    have hst : (s • T).val.PosDef := hT.smul hs
    have hscale : psdScale (s ^ 2) (sq_nonneg s) (pdInclusion B) =
        pdInclusion (squarePoint (s • T).val hst) := by
      apply Subtype.ext
      change s ^ 2 • B.val = (s • T.val) * (s • T.val)
      rw [smul_mul_smul_comm, hTsq]
      simp [pow_two]
    change ((s ^ 2)⁻¹ • (E (psdScale (s ^ 2) (sq_nonneg s)
      (pdInclusion B))).val) = _
    rw [hscale]
    rw [hform (s • T) hst]
    let P : Hermitian n :=
      (⟨1, Matrix.isHermitian_one⟩ : Hermitian n) +
        L (s • T - (⟨1, Matrix.isHermitian_one⟩ : Hermitian n))
    change (s ^ 2)⁻¹ • (P.val * C.val * P.val) =
      (s⁻¹ • P).val * C.val * (s⁻¹ • P).val
    change (s ^ 2)⁻¹ • (P.val * C.val * P.val) =
      (s⁻¹ • P.val) * C.val * (s⁻¹ • P.val)
    rw [smul_mul_assoc, smul_mul_smul_comm]
    simp [pow_two]

/-- The global affine normal representation makes its quadratic blow-down an
actual isometry of the literal Bures metric, including the singular boundary.
The proof uses the isometric PSD extension and positive-definite density. -/
theorem normalBlowdown_isometry_of_normal_form
    (F : PositiveDefinite n → PositiveDefinite n)
    (hF : PreservesDistance F)
    (L : Hermitian n →ₗ[ℝ] Hermitian n)
    (hrep : ∀ B : PositiveDefinite n,
      normalCoordinate (F (pdIdentity n)) (F B) =
        L (normalCoordinate (pdIdentity n) B)) :
    ∀ X Y : PSD n,
      psdDistance (normalBlowdownModel L (F (pdIdentity n)) X)
        (normalBlowdownModel L (F (pdIdentity n)) Y) =
      psdDistance X Y := by
  obtain ⟨E, hE, hext⟩ := exists_psd_isometric_extension F hF
  have he : ∀ X Y : PSD n, psdDistance (E X) (E Y) = psdDistance X Y := by
    intro X Y
    exact hE.dist_eq X Y
  have hform : ∀ (T : Hermitian n) (hT : T.val.PosDef),
      let P := ((⟨1, Matrix.isHermitian_one⟩ : Hermitian n) +
        L (T - (⟨1, Matrix.isHermitian_one⟩ : Hermitian n))).val
      (E (pdInclusion (squarePoint T.val hT))).val =
        P * (F (pdIdentity n)).val * P := by
    intro T hT
    rw [hext]
    exact affine_normal_congruence_form F L hrep T hT
  let Φ := normalBlowdownModel L (F (pdIdentity n))
  let Eseq : ℕ → PSD n → PSD n := fun k X =>
    rescaledPsdMap E ((↑(k + 1) : ℝ) ^ 2)
      (sq_pos_of_pos (by exact_mod_cast Nat.succ_pos k)) X
  have hseq : ∀ k X Y, psdDistance (Eseq k X) (Eseq k Y) =
      psdDistance X Y := by
    intro k X Y
    exact rescaledPsdMap_isometry E he _ _ X Y
  have hpd : ∀ B : PositiveDefinite n,
      Tendsto (fun k => Eseq k (pdInclusion B)) atTop
        (𝓝 (Φ (pdInclusion B))) := by
    intro B
    exact normalBlowdown_limit_pd_of_affine_form E L
      (F (pdIdentity n)) hform B
  have hall := psd_isometry_limit_of_dense_pd Eseq Φ hseq
    (continuous_normalBlowdownModel L (F (pdIdentity n))) hpd
  exact psd_isometry_of_pointwise_limit Eseq Φ hseq hall

/-- A blow-down limit at the cone apex is an isometry. If its limit is the
normal-chart quadratic model, it fixes zero and is therefore surjective. -/
theorem normalBlowdown_surjective_of_limit
    (E : PSD n → PSD n)
    (hE : ∀ X Y, psdDistance (E X) (E Y) = psdDistance X Y)
    (L : Hermitian n →ₗ[ℝ] Hermitian n) (C : PositiveDefinite n)
    (t : ℕ → ℝ) (ht : ∀ k, 0 < t k)
    (hlim : ∀ X, Tendsto
      (fun k => rescaledPsdMap E (t k) (ht k) X) atTop
      (𝓝 (normalBlowdownModel L C X))) :
    Function.Surjective (normalBlowdownModel L C) := by
  have hIso := psd_isometry_of_pointwise_limit
    (fun k X => rescaledPsdMap E (t k) (ht k) X)
    (normalBlowdownModel L C)
    (fun k X Y => rescaledPsdMap_isometry E hE (t k) (ht k) X Y)
    hlim
  exact psd_isometry_surjective_of_zero_fixed _ hIso
    (normalBlowdownModel_zero L C)

/-- Surjective blow-down isometries preserve the positive-definite stratum.
This is an algebraic consequence of fidelity preservation and uses no
invariance of domain. -/
theorem normalBlowdown_posDef_iff
    (L : Hermitian n →ₗ[ℝ] Hermitian n) (C : PositiveDefinite n)
    (hIso : ∀ X Y, psdDistance (normalBlowdownModel L C X)
      (normalBlowdownModel L C Y) = psdDistance X Y)
    (honto : Function.Surjective (normalBlowdownModel L C)) (X : PSD n) :
    (normalBlowdownModel L C X).val.PosDef ↔ X.val.PosDef := by
  have hzero := normalBlowdownModel_zero L C
  have hinj : Function.Injective (normalBlowdownModel L C) :=
    (Isometry.of_dist_eq hIso).injective
  have hf : ∀ U V, fidelityRoot (normalBlowdownModel L C U).val
      (normalBlowdownModel L C V).val = fidelityRoot U.val V.val :=
    preserves_fidelity_of_psdZero_fixed _ hIso hzero
  exact posDef_image_iff_of_fidelity_bijection _ ⟨hinj, honto⟩ hzero hf X

/-- In particular, the Hermitian factor `L (sqrt X)` is invertible for every
positive-definite input X. -/
theorem normalBlowdown_factor_isUnit
    (L : Hermitian n →ₗ[ℝ] Hermitian n) (C : PositiveDefinite n)
    (hIso : ∀ X Y, psdDistance (normalBlowdownModel L C X)
      (normalBlowdownModel L C Y) = psdDistance X Y)
    (honto : Function.Surjective (normalBlowdownModel L C))
    (X : PSD n) (hX : X.val.PosDef) :
    IsUnit (L ⟨matrixSqrt X.val,
      (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg X.val)).isHermitian⟩).val := by
  let R : Hermitian n := ⟨matrixSqrt X.val,
      (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg X.val)).isHermitian⟩
  let K := L R
  have hp := (normalBlowdown_posDef_iff L C hIso honto X).mpr hX
  have hu : IsUnit (K.val * C.val * K.val) := by
    change IsUnit (normalBlowdownModel L C X).val
    exact hp.isUnit
  exact isUnit_of_mul_isUnit_right hu

/-- The blow-down factor is invertible on every positive Hermitian argument,
not only those presented syntactically as square roots. -/
theorem normalBlowdown_linear_isUnit
    (L : Hermitian n →ₗ[ℝ] Hermitian n) (C : PositiveDefinite n)
    (hIso : ∀ X Y, psdDistance (normalBlowdownModel L C X)
      (normalBlowdownModel L C Y) = psdDistance X Y)
    (honto : Function.Surjective (normalBlowdownModel L C))
    (T : Hermitian n) (hT : T.val.PosDef) : IsUnit (L T).val := by
  let B := squarePoint T.val hT
  let X : PSD n := ⟨B.val, B.property.posSemidef⟩
  have hroot : matrixSqrt X.val = T.val := matrixSqrt_squarePoint T.val hT
  have hX : X.val.PosDef := B.property
  simpa only [hroot] using normalBlowdown_factor_isUnit L C hIso honto X hX

/-- The global normal-chart condition and blow-down isometry make the linear
normal part strictly positive on the interior cone. -/
theorem normalBlowdown_linear_posDef
    (L : Hermitian n →ₗ[ℝ] Hermitian n) (C : PositiveDefinite n)
    (hchart : ∀ (T : Hermitian n), T.val.PosDef →
      ((⟨1, Matrix.isHermitian_one⟩ : Hermitian n) +
        L (T - (⟨1, Matrix.isHermitian_one⟩ : Hermitian n))).val.PosDef)
    (hIso : ∀ X Y, psdDistance (normalBlowdownModel L C X)
      (normalBlowdownModel L C Y) = psdDistance X Y)
    (honto : Function.Surjective (normalBlowdownModel L C))
    (T : Hermitian n) (hT : T.val.PosDef) : (L T).val.PosDef :=
  linear_posDef_of_positive_chart_and_unit L hchart
    (normalBlowdown_linear_isUnit L C hIso honto) T hT

/-- A surjective quadratic blow-down with a globally positive normal chart
forces the normal linear map to cover the entire positive cone. -/
theorem normalBlowdown_linear_surjective_on_posDef
    (L : Hermitian n →ₗ[ℝ] Hermitian n) (C : PositiveDefinite n)
    (hchart : ∀ (T : Hermitian n), T.val.PosDef →
      ((⟨1, Matrix.isHermitian_one⟩ : Hermitian n) +
        L (T - (⟨1, Matrix.isHermitian_one⟩ : Hermitian n))).val.PosDef)
    (hIso : ∀ X Y, psdDistance (normalBlowdownModel L C X)
      (normalBlowdownModel L C Y) = psdDistance X Y)
    (honto : Function.Surjective (normalBlowdownModel L C))
    (Y : Hermitian n) (hY : Y.val.PosDef) :
    ∃ T : Hermitian n, T.val.PosDef ∧ L T = Y := by
  let B := normalChartPoint C Y hY
  let P : PSD n := ⟨B.val, B.property.posSemidef⟩
  obtain ⟨X, hXeq⟩ := honto P
  have hX : X.val.PosDef :=
    (normalBlowdown_posDef_iff L C hIso honto X).mp (by
      rw [hXeq]
      exact B.property)
  let T : Hermitian n := ⟨matrixSqrt X.val,
    (Matrix.nonneg_iff_posSemidef.mp (matrixSqrt_nonneg X.val)).isHermitian⟩
  have hT : T.val.PosDef := by
    change (matrixSqrt X.val).PosDef
    exact hX.isStrictlyPositive.sqrt.posDef
  have hK := normalBlowdown_linear_posDef L C hchart hIso honto T hT
  have hB : normalChartPoint C (L T) hK = B := by
    apply Subtype.ext
    have h := congrArg Subtype.val hXeq
    exact h.trans (rfl : P.val = B.val)
  refine ⟨T, hT, ?_⟩
  apply Subtype.ext
  have h := congrArg (normalTransport C) hB
  simpa only [B, normalTransport_chartPoint] using h

#print axioms psd_isometry_of_pointwise_limit
#print axioms psd_isometry_surjective_of_zero_fixed
#print axioms normalBlowdownModel_zero
#print axioms rescaledPsdMap_isometry
#print axioms normalBlowdown_surjective_of_limit
#print axioms normalBlowdown_posDef_iff
#print axioms normalBlowdown_factor_isUnit
#print axioms psd_isometry_limit_of_dense_pd
#print axioms continuous_normalBlowdownModel
#print axioms linear_posSemidef_of_positive_chart
#print axioms tendsto_affine_normal_factor
#print axioms tendsto_affine_normal_congruence
#print axioms normalBlowdown_limit_pd_of_affine_form
#print axioms normalBlowdown_isometry_of_normal_form
#print axioms normalBlowdown_linear_surjective_on_posDef

end Bures

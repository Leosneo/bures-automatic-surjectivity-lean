import BuresNoncommuting

noncomputable section
open scoped MatrixOrder ComplexOrder Matrix.Norms.Frobenius
namespace Bures

/-- For n≥2, a positive-semidefinite displacement in square-root
coordinates cannot act isometrically unless it vanishes. -/
theorem squareTranslation_displacement_zero (n : ℕ) (hn : 2 ≤ n)
    (D : Hermitian n) (hD : D.val.PosSemidef)
    (hF : PreservesDistance (squareTranslation D hD)) : D = 0 := by
  obtain ⟨c, hDc⟩ := squareTranslation_displacement_scalar D hD hF
  have hc : 0 ≤ c := by
    let i : Fin n := ⟨0, by omega⟩
    have hi := hD.diag_nonneg (i := i)
    rw [hDc] at hi
    simpa [Matrix.smul_apply, Matrix.one_apply, i, Complex.le_def] using hi
  by_contra hDne
  have hcne : c ≠ 0 := by
    intro hz
    apply hDne
    apply Subtype.ext
    rw [hDc, hz]
    ext i j
    simp [Matrix.smul_apply, Complex.real_smul]
  have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hcne)
  obtain ⟨T, S, hT, hS, hnoncomm⟩ := exists_noncommuting_posDef n hn
  let A := squarePoint T hT
  let B := squarePoint S hS
  have hTshift : squareTranslation D hD A =
      squarePoint (T + c • (1 : Mat n))
        (hT.add_posSemidef (Matrix.PosDef.one.smul hcpos).posSemidef) := by
    apply Subtype.ext
    change (matrixSqrt A.val + D.val) * (matrixSqrt A.val + D.val) =
      (T + c • (1 : Mat n)) * (T + c • (1 : Mat n))
    rw [matrixSqrt_squarePoint, hDc]
  have hSshift : squareTranslation D hD B =
      squarePoint (S + c • (1 : Mat n))
        (hS.add_posSemidef (Matrix.PosDef.one.smul hcpos).posSemidef) := by
    apply Subtype.ext
    change (matrixSqrt B.val + D.val) * (matrixSqrt B.val + D.val) =
      (S + c • (1 : Mat n)) * (S + c • (1 : Mat n))
    rw [matrixSqrt_squarePoint, hDc]
  have hd := hF A B
  rw [hTshift, hSshift] at hd
  exact hnoncomm (commute_of_scalar_shift_distance_eq T S hT hS c hcpos hd)

#print axioms squareTranslation_displacement_zero
end Bures

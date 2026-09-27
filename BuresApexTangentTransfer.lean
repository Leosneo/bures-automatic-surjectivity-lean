import BuresApexFourPoint

/-! Quantitative transfer of the Hilbert four-point inequality to an
approximately Euclidean model of six pairwise Bures distances. -/

noncomputable section
open scoped MatrixOrder ComplexOrder Matrix.Norms.Frobenius InnerProductSpace
namespace Bures

/-- If the six squared distances of a Bures quadrilateral are within `η`
of distances of four Hilbert vectors, its four-point excess is at most `6η`.
The estimate is independent of how the Hilbert vectors were obtained. -/
theorem four_point_defect_le_six_error
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A B C D : PSD 2) (a b c d : E) (η : ℝ)
    (hAC : |psdDistance A C ^ 2 - dist a c ^ 2| ≤ η)
    (hBD : |psdDistance B D ^ 2 - dist b d ^ 2| ≤ η)
    (hAB : |psdDistance A B ^ 2 - dist a b ^ 2| ≤ η)
    (hBC : |psdDistance B C ^ 2 - dist b c ^ 2| ≤ η)
    (hCD : |psdDistance C D ^ 2 - dist c d ^ 2| ≤ η)
    (hDA : |psdDistance D A ^ 2 - dist d a ^ 2| ≤ η) :
    psdDistance A C ^ 2 + psdDistance B D ^ 2 -
      psdDistance A B ^ 2 - psdDistance B C ^ 2 -
      psdDistance C D ^ 2 - psdDistance D A ^ 2 ≤ 6 * η := by
  have hgood := hilbert_four_point a b c d
  have hAC' := (abs_le.mp hAC).2
  have hBD' := (abs_le.mp hBD).2
  have hAB' := (abs_le.mp hAB).1
  have hBC' := (abs_le.mp hBC).1
  have hCD' := (abs_le.mp hCD).1
  have hDA' := (abs_le.mp hDA).1
  linarith

/-- A positive Bures four-point defect forbids a sufficiently accurate
Hilbert model of these six squared distances. -/
theorem no_hilbert_model_below_defect
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A B C D : PSD 2) (η : ℝ)
    (hη : 6 * η < psdDistance A C ^ 2 + psdDistance B D ^ 2 -
      psdDistance A B ^ 2 - psdDistance B C ^ 2 -
      psdDistance C D ^ 2 - psdDistance D A ^ 2) :
    ¬ ∃ a b c d : E,
      |psdDistance A C ^ 2 - dist a c ^ 2| ≤ η ∧
      |psdDistance B D ^ 2 - dist b d ^ 2| ≤ η ∧
      |psdDistance A B ^ 2 - dist a b ^ 2| ≤ η ∧
      |psdDistance B C ^ 2 - dist b c ^ 2| ≤ η ∧
      |psdDistance C D ^ 2 - dist c d ^ 2| ≤ η ∧
      |psdDistance D A ^ 2 - dist d a ^ 2| ≤ η := by
  rintro ⟨a, b, c, d, hAC, hBD, hAB, hBC, hCD, hDA⟩
  have h := four_point_defect_le_six_error A B C D a b c d η
    hAC hBD hAB hBC hCD hDA
  linarith

#print axioms four_point_defect_le_six_error
#print axioms no_hilbert_model_below_defect

end Bures

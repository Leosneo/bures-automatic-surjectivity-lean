import BuresSquareTranslation
noncomputable section
open scoped MatrixOrder ComplexOrder Matrix.Norms.Frobenius
namespace Bures

theorem tr_scalar_shift_square (T : Mat n) (c : ℝ) :
    tr ((T + c • (1 : Mat n)) * (T + c • (1 : Mat n))) =
      tr (T * T) + 2 * c * tr T + c * c * tr (1 : Mat n) := by
  have h1 : T * (c • (1 : Mat n)) = c • T := by
    rw [mul_smul_comm, mul_one]
  have h2 : (c • (1 : Mat n)) * T = c • T := by
    rw [smul_mul_assoc, one_mul]
  have h3 : (c • (1 : Mat n)) * (c • (1 : Mat n)) =
      (c * c) • (1 : Mat n) := by
    rw [smul_mul_smul_comm, one_mul]
  simp only [add_mul, mul_add, h1, h2, h3, tr_add, tr_smul]
  ring

end Bures

namespace Bures

theorem tr_scalar_shift_overlap (T S U : Mat n) (c : ℝ) :
    tr ((T + c • (1 : Mat n)) * (S + c • (1 : Mat n)) * U) =
      tr (T * S * U) + c * tr (T * U) + c * tr (S * U) +
        c * c * tr U := by
  have h1 : T * (c • (1 : Mat n)) = c • T := by
    rw [mul_smul_comm, mul_one]
  have h2 : (c • (1 : Mat n)) * S = c • S := by
    rw [smul_mul_assoc, one_mul]
  have h3 : (c • (1 : Mat n)) * (c • (1 : Mat n)) =
      (c * c) • (1 : Mat n) := by
    rw [smul_mul_smul_comm, one_mul]
  simp only [add_mul, mul_add, h1, h2, h3, tr_add, tr_smul,
    smul_mul_assoc, one_mul]
  ring

end Bures

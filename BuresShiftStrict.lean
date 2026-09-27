import BuresShiftTrace

noncomputable section
open scoped MatrixOrder ComplexOrder Matrix.Norms.Frobenius
namespace Bures

/-- A nonzero positive scalar shift can preserve one Bures distance only
when the positive square roots of those two endpoints commute. -/
theorem commute_of_scalar_shift_distance_eq (T S : Mat n)
    (hT : T.PosDef) (hS : S.PosDef) (c : ℝ) (hc : 0 < c)
    (hd : distance
      (squarePoint (T + c • (1 : Mat n))
        (hT.add_posSemidef (Matrix.PosDef.one.smul hc).posSemidef))
      (squarePoint (S + c • (1 : Mat n))
        (hS.add_posSemidef (Matrix.PosDef.one.smul hc).posSemidef)) =
      distance (squarePoint T hT) (squarePoint S hS)) :
    Commute T S := by
  let P : Mat n := T + c • (1 : Mat n)
  let Q : Mat n := S + c • (1 : Mat n)
  have hP : P.PosDef := hT.add_posSemidef (Matrix.PosDef.one.smul hc).posSemidef
  have hQ : Q.PosDef := hS.add_posSemidef (Matrix.PosDef.one.smul hc).posSemidef
  let A := squarePoint T hT
  let B := squarePoint S hS
  let C := squarePoint P hP
  let D := squarePoint Q hQ
  have hd' : distance C D = distance A B := hd
  obtain ⟨U, hUl, hUr, hmax⟩ := (fidelityRoot_variational C D).2
  have hCp : matrixSqrt C.val = P := matrixSqrt_squarePoint P hP
  have hDq : matrixSqrt D.val = Q := matrixSqrt_squarePoint Q hQ
  have hAp : matrixSqrt A.val = T := matrixSqrt_squarePoint T hT
  have hBs : matrixSqrt B.val = S := matrixSqrt_squarePoint S hS
  have hmax' : tr (P * Q * U) = fidelityRoot C.val D.val := by
    simpa only [hCp, hDq] using hmax
  have hvar : tr (T * S * U) ≤ fidelityRoot A.val B.val := by
    simpa only [hAp, hBs] using
      (fidelityRoot_variational A B).1 U hUl
  have hTloss : tr (T * U) ≤ tr T := tr_mul_le_of_unitary hT.posSemidef hUl
  have hSloss : tr (S * U) ≤ tr S := tr_mul_le_of_unitary hS.posSemidef hUl
  have hIloss : tr ((1 : Mat n) * U) ≤ tr (1 : Mat n) :=
    tr_mul_le_of_unitary Matrix.PosDef.one.posSemidef hUl
  have hdistA := distance_sq A B
  have hdistC := distance_sq C D
  rw [hd', hdistA] at hdistC
  have hCA : tr C.val = tr (T * T) + 2 * c * tr T +
      c * c * tr (1 : Mat n) := tr_scalar_shift_square T c
  have hDB : tr D.val = tr (S * S) + 2 * c * tr S +
      c * c * tr (1 : Mat n) := tr_scalar_shift_square S c
  have hA : tr A.val = tr (T * T) := rfl
  have hB : tr B.val = tr (S * S) := rfl
  have hfid : fidelityRoot C.val D.val =
      tr (T * S * U) + c * tr (T * U) + c * tr (S * U) +
        c * c * tr U := by
    rw [← hmax', show P = T + c • (1 : Mat n) from rfl,
      show Q = S + c • (1 : Mat n) from rfl]
    exact tr_scalar_shift_overlap T S U c
  rw [hCA, hDB, hA, hB, hfid] at hdistC
  have hdiff : 0 ≤ fidelityRoot A.val B.val - tr (T * S * U) := sub_nonneg.mpr hvar
  have htl : 0 ≤ tr T - tr (T * U) := sub_nonneg.mpr hTloss
  have hsl : 0 ≤ tr S - tr (S * U) := sub_nonneg.mpr hSloss
  have hil : 0 ≤ tr (1 : Mat n) - tr U := by
    simpa only [one_mul] using sub_nonneg.mpr hIloss
  have heq : (fidelityRoot A.val B.val - tr (T * S * U)) +
      c * ((tr T - tr (T * U)) + (tr S - tr (S * U))) +
      (c * c) * (tr (1 : Mat n) - tr U) = 0 := by
    nlinarith [hdistC]
  have hsum : 0 ≤ c * ((tr T - tr (T * U)) +
      (tr S - tr (S * U))) := mul_nonneg hc.le (add_nonneg htl hsl)
  have hq : 0 ≤ (c * c) * (tr (1 : Mat n) - tr U) :=
    mul_nonneg (mul_nonneg hc.le hc.le) hil
  have hqzero : (c * c) * (tr (1 : Mat n) - tr U) = 0 := by
    linarith
  have hzero : tr (1 : Mat n) - tr U = 0 :=
    (mul_eq_zero.mp hqzero).resolve_left (mul_ne_zero hc.ne' hc.ne')
  have hU : U = 1 := by
    apply tr_mul_eq_of_posDef_unitary Matrix.PosDef.one hUl
    simpa only [one_mul] using (sub_eq_zero.mp hzero).symm
  subst U
  have hfid0 : fidelityRoot A.val B.val = tr (T * S) := by
    simp only [mul_one] at heq
    simp only [sub_self, mul_zero, add_zero] at heq
    linarith only [heq]
  have hnormsq : ‖T - S‖ ^ 2 =
      tr A.val + tr B.val - 2 * tr (T * S) := by
    rw [frobenius_sq_eq_tr_gram]
    have ht := tr_gram_factor_difference A B 1 (by simp)
    rw [hAp, hBs, mul_one] at ht
    simpa only [Matrix.conjTranspose_sub, hT.isHermitian.eq,
      hS.isHermitian.eq, mul_one] using ht
  have hnorm : distance A B = ‖T - S‖ := by
    have hdsq := distance_sq A B
    rw [hfid0] at hdsq
    have hdn : 0 ≤ distance A B := distance_nonneg A B
    nlinarith only [hdsq, hnormsq, hdn, norm_nonneg (T - S)]
  exact commute_of_distance_eq_sqrt_norm T S hT hS hnorm

#print axioms commute_of_scalar_shift_distance_eq
end Bures

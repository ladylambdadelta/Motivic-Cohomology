import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.QuantitativeTransitionScalarComparison

/-!
# Rational transition-curvature ratio

This owner divides the unsquared scalar comparison by its positive
denominators.  The resulting ratio is bounded by `d/(d+2)`, exactly the
rational lower bound already dominated by the exponential odd ratio.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Real.transitionReducedCurvatureRatio (s d : ℝ) : ℝ :=
  (2 * (s - 1) * d) / (s * (s - 2) ^ 2)

theorem Real.transitionScalar_d_add_two_pos
    {d : ℝ}
    (hd : 0 ≤ d) :
    0 < d + 2 := by
  exact add_pos_of_nonneg_of_pos hd zero_lt_two

theorem Real.transitionScalar_energyDenominator_pos
    {s : ℝ}
    (hs : 4 ≤ s) :
    0 < s * (s - 2) ^ 2 := by
  have hsPos := Real.transitionScalar_pos hs
  have hsubPos : 0 < s - 2 := by
    have htwoLtFour : (2 : ℝ) < 4 := by
      exact lt_add_of_pos_right 2 zero_lt_two
    exact sub_pos.mpr (lt_of_lt_of_le htwoLtFour hs)
  exact mul_pos hsPos (sq_pos_of_pos hsubPos)

theorem Real.transitionScalar_cross_product
    {s d : ℝ}
    (hs : 4 ≤ s)
    (hd : 0 ≤ d)
    (hdSquare : d ^ 2 = s * (s - 4)) :
    (2 * (s - 1) * d) * (d + 2) ≤
      d * (s * (s - 2) ^ 2) := by
  have hbase :=
    Real.transitionScalar_unsquared_comparison hs hd hdSquare
  have hscaled := mul_le_mul_of_nonneg_left hbase hd
  have hleft :
      d * (2 * (s - 1) * (d + 2)) =
        (2 * (s - 1) * d) * (d + 2) := by
    calc
      d * (2 * (s - 1) * (d + 2)) =
          (d * (2 * (s - 1))) * (d + 2) :=
        (mul_assoc d (2 * (s - 1)) (d + 2)).symm
      _ = ((2 * (s - 1)) * d) * (d + 2) :=
        congrArg (fun value : ℝ => value * (d + 2))
          (mul_comm d (2 * (s - 1)))
  exact le_trans (le_of_eq hleft.symm) hscaled

theorem Real.transitionReducedCurvatureRatio_le_rationalOddLower
    {s d : ℝ}
    (hs : 4 ≤ s)
    (hd : 0 ≤ d)
    (hdSquare : d ^ 2 = s * (s - 4)) :
    Real.transitionReducedCurvatureRatio s d ≤
      Real.rationalOddLower d := by
  have henergy := Real.transitionScalar_energyDenominator_pos hs
  have hgap := Real.transitionScalar_d_add_two_pos hd
  have hcross := Real.transitionScalar_cross_product hs hd hdSquare
  unfold Real.transitionReducedCurvatureRatio
  unfold Real.rationalOddLower
  exact (div_le_div_iff₀ henergy hgap).mpr hcross

theorem Real.transitionScalar_fullDenominator_eq
    (s : ℝ) :
    s ^ 2 * (s - 2) ^ 2 =
      s * (s * (s - 2) ^ 2) := by
  calc
    s ^ 2 * (s - 2) ^ 2 = (s * s) * (s - 2) ^ 2 :=
      congrArg (fun value : ℝ => value * (s - 2) ^ 2) (pow_two s)
    _ = s * (s * (s - 2) ^ 2) :=
      mul_assoc s s ((s - 2) ^ 2)

theorem Real.transitionScalar_fullNumerator_eq
    (s d : ℝ) :
    2 * d * s * (s - 1) =
      s * (2 * (s - 1) * d) := by
  calc
    2 * d * s * (s - 1) = (2 * d) * (s * (s - 1)) :=
      mul_assoc (2 * d) s (s - 1)
    _ = (s * (s - 1)) * (2 * d) :=
      mul_comm (2 * d) (s * (s - 1))
    _ = s * ((s - 1) * (2 * d)) :=
      mul_assoc s (s - 1) (2 * d)
    _ = s * (2 * ((s - 1) * d)) := by
      exact congrArg (fun value : ℝ => s * value)
        ((mul_assoc (s - 1) 2 d).symm.trans
          (congrArg (fun value : ℝ => value * d)
            (mul_comm (s - 1) 2)).trans
          (mul_assoc 2 (s - 1) d))
    _ = s * (2 * (s - 1) * d) := by
      exact congrArg (fun value : ℝ => s * value)
        (mul_assoc 2 (s - 1) d).symm

theorem Real.transitionScalarCurvatureRatio_eq_reduced
    {s d : ℝ}
    (hs : 4 ≤ s) :
    Real.transitionScalarCurvatureRatio s d =
      Real.transitionReducedCurvatureRatio s d := by
  have hsNe : s ≠ 0 := ne_of_gt (Real.transitionScalar_pos hs)
  unfold Real.transitionScalarCurvatureRatio
  unfold Real.transitionReducedCurvatureRatio
  have hnumerator := Real.transitionScalar_fullNumerator_eq s d
  have hdenominator := Real.transitionScalar_fullDenominator_eq s
  calc
    (2 * d * s * (s - 1)) / (s ^ 2 * (s - 2) ^ 2) =
        (s * (2 * (s - 1) * d)) /
          (s * (s * (s - 2) ^ 2)) :=
      congrArg₂ (fun numerator denominator : ℝ => numerator / denominator)
        hnumerator hdenominator
    _ = (2 * (s - 1) * d) / (s * (s - 2) ^ 2) :=
      mul_div_mul_left (2 * (s - 1) * d)
        (s * (s - 2) ^ 2) hsNe

theorem Real.transitionScalarCurvatureRatio_le_rationalOddLower
    {s d : ℝ}
    (hs : 4 ≤ s)
    (hd : 0 ≤ d)
    (hdSquare : d ^ 2 = s * (s - 4)) :
    Real.transitionScalarCurvatureRatio s d ≤
      Real.rationalOddLower d := by
  have hnormalize :=
    Real.transitionScalarCurvatureRatio_eq_reduced (d := d) hs
  have hbound :=
    Real.transitionReducedCurvatureRatio_le_rationalOddLower hs hd hdSquare
  exact Eq.subst
    (motive := fun value : ℝ => value ≤ Real.rationalOddLower d)
    hnormalize.symm
    hbound

theorem Real.transitionScalarCurvatureRatio_le_exponentialOddRatio
    {s d : ℝ}
    (hs : 4 ≤ s)
    (hd : 0 ≤ d)
    (hdSquare : d ^ 2 = s * (s - 4)) :
    Real.transitionScalarCurvatureRatio s d ≤
      Real.exponentialOddRatio d := by
  exact le_trans
    (Real.transitionScalarCurvatureRatio_le_rationalOddLower
      hs hd hdSquare)
    (Real.rationalOddLower_le_exponentialOddRatio hd)

theorem Real.transitionScalarCurvatureRatio_nonneg
    {s d : ℝ}
    (hs : 4 ≤ s)
    (hd : 0 ≤ d) :
    0 ≤ Real.transitionScalarCurvatureRatio s d := by
  unfold Real.transitionScalarCurvatureRatio
  have hnumerator : 0 ≤ 2 * d * s * (s - 1) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (Nat.cast_nonneg 2) hd)
        (le_of_lt (Real.transitionScalar_pos hs)))
      (le_of_lt (Real.transitionScalar_sub_one_pos hs))
  have hdenominator : 0 ≤ s ^ 2 * (s - 2) ^ 2 :=
    mul_nonneg (sq_nonneg s) (sq_nonneg (s - 2))
  exact div_nonneg hnumerator hdenominator

end
end LFunctions
end Boundary

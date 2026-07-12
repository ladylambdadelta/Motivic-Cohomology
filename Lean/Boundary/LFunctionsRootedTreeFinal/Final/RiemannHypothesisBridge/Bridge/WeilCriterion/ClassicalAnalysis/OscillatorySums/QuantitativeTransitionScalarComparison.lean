import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.QuantitativeTransitionDiscriminantNormalization

/-!
# Scalar comparison for transition curvature

This owner turns the nonnegative squared discriminant into the unsquared
inequality needed for the logistic comparison.  The variables satisfy
`s≥4`, `d≥0`, and `d²=s(s-4)`, exactly the relations of the reciprocal sum and
gap on the left half of the transition interval.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Real.transitionScalarCore (s : ℝ) : ℝ :=
  s ^ 3 - 4 * s ^ 2 + 4

def Real.transitionScalarGapTerm (s d : ℝ) : ℝ :=
  2 * (s - 1) * d

def Real.transitionScalarCurvatureRatio (s d : ℝ) : ℝ :=
  (2 * d * s * (s - 1)) / (s ^ 2 * (s - 2) ^ 2)

theorem Real.transitionScalarCore_eq_square_mul_shift_add_four
    (s : ℝ) :
    Real.transitionScalarCore s = s ^ 2 * (s - 4) + 4 := by
  unfold Real.transitionScalarCore
  calc
    s ^ 3 - 4 * s ^ 2 + 4 = s ^ 2 * s - 4 * s ^ 2 + 4 :=
      congrArg (fun value : ℝ => value - 4 * s ^ 2 + 4)
        (pow_succ s 2)
    _ = s ^ 2 * s - s ^ 2 * 4 + 4 :=
      congrArg (fun value : ℝ => s ^ 2 * s - value + 4)
        (mul_comm 4 (s ^ 2))
    _ = s ^ 2 * (s - 4) + 4 :=
      congrArg (fun value : ℝ => value + 4)
        (mul_sub (s ^ 2) s 4).symm

theorem Real.transitionScalarCore_nonneg
    {s : ℝ}
    (hs : 4 ≤ s) :
    0 ≤ Real.transitionScalarCore s := by
  have hsSquare : 0 ≤ s ^ 2 := sq_nonneg s
  have hshift : 0 ≤ s - 4 := sub_nonneg.mpr hs
  have hproduct : 0 ≤ s ^ 2 * (s - 4) :=
    mul_nonneg hsSquare hshift
  have hfour : (0 : ℝ) ≤ 4 := Nat.cast_nonneg 4
  exact Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (Real.transitionScalarCore_eq_square_mul_shift_add_four s).symm
    (add_nonneg hproduct hfour)

theorem Real.transitionScalarGapTerm_nonneg
    {s d : ℝ}
    (hs : 4 ≤ s)
    (hd : 0 ≤ d) :
    0 ≤ Real.transitionScalarGapTerm s d := by
  unfold Real.transitionScalarGapTerm
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg 2)
      (le_of_lt (Real.transitionScalar_sub_one_pos hs)))
    hd

theorem Real.transitionScalarGapTerm_sq
    (s d : ℝ) :
    Real.transitionScalarGapTerm s d ^ 2 =
      4 * (s - 1) ^ 2 * d ^ 2 := by
  unfold Real.transitionScalarGapTerm
  calc
    (2 * (s - 1) * d) ^ 2 =
        (2 * (s - 1) * d) * (2 * (s - 1) * d) :=
      pow_two _
    _ = (2 * 2) * ((s - 1) * (s - 1)) * (d * d) := by
      exact
        (mul_assoc (2 * (s - 1)) d (2 * (s - 1) * d)).trans
          (congrArg (fun value : ℝ => 2 * (s - 1) * value)
            ((mul_assoc d 2 ((s - 1) * d)).symm.trans
              (congrArg (fun value : ℝ => value * ((s - 1) * d))
                (mul_comm d 2)))).trans
          ((mul_assoc (2 * (s - 1)) 2 ((s - 1) * d)).symm.trans
            (congrArg (fun value : ℝ => value * ((s - 1) * d))
              ((mul_assoc 2 (s - 1) 2).trans
                (congrArg (fun value : ℝ => 2 * value)
                  (mul_comm (s - 1) 2))).trans
              (mul_assoc 2 2 (s - 1)).symm)).trans
          (mul_assoc ((2 * 2) * (s - 1)) (s - 1) d).trans
          (congrArg (fun value : ℝ => value * d)
            (mul_assoc (2 * 2) (s - 1) (s - 1))).trans
          (mul_assoc (2 * 2) ((s - 1) * (s - 1)) (d * d)).symm
    _ = 4 * (s - 1) ^ 2 * d ^ 2 := by
      exact congrArg₂ (fun first second : ℝ => first * second)
        (congrArg₂ (fun first second : ℝ => first * second)
          (show (2 : ℝ) * 2 = 4 from rfl)
          (pow_two (s - 1)).symm)
        (pow_two d).symm

theorem Real.transitionRawDiscriminant_eq_core_sq_sub_gap_sq
    {s d : ℝ}
    (hdSquare : d ^ 2 = s * (s - 4)) :
    Real.transitionCurvatureRawDiscriminant s =
      Real.transitionScalarCore s ^ 2 -
        Real.transitionScalarGapTerm s d ^ 2 := by
  unfold Real.transitionCurvatureRawDiscriminant
  unfold Real.transitionScalarCore
  have hgap := Real.transitionScalarGapTerm_sq s d
  exact congrArg₂ (fun first second : ℝ => first - second)
    rfl
    (Eq.trans hgap
      (congrArg (fun value : ℝ => 4 * (s - 1) ^ 2 * value)
        hdSquare))

theorem Real.transitionScalarGapTerm_le_core
    {s d : ℝ}
    (hs : 4 ≤ s)
    (hd : 0 ≤ d)
    (hdSquare : d ^ 2 = s * (s - 4)) :
    Real.transitionScalarGapTerm s d ≤
      Real.transitionScalarCore s := by
  have hraw := Real.transitionCurvatureRawDiscriminant_nonneg hs
  have hidentity :=
    Real.transitionRawDiscriminant_eq_core_sq_sub_gap_sq hdSquare
  have hsquares :
      Real.transitionScalarGapTerm s d ^ 2 ≤
        Real.transitionScalarCore s ^ 2 := by
    have hdifference :
        0 ≤ Real.transitionScalarCore s ^ 2 -
          Real.transitionScalarGapTerm s d ^ 2 :=
      Eq.subst (motive := fun value : ℝ => 0 ≤ value)
        hidentity.symm hraw
    exact sub_nonneg.mp hdifference
  exact le_of_sq_le_sq hsquares
    (Real.transitionScalarCore_nonneg hs)

theorem Real.transitionScalarCore_add_four_sub_one_eq_energySquare
    (s : ℝ) :
    Real.transitionScalarCore s + 4 * (s - 1) =
      s * (s - 2) ^ 2 := by
  unfold Real.transitionScalarCore
  calc
    s ^ 3 - 4 * s ^ 2 + 4 + 4 * (s - 1) =
        s ^ 3 - 4 * s ^ 2 + 4 + (4 * s - 4) :=
      congrArg (fun value : ℝ => s ^ 3 - 4 * s ^ 2 + 4 + value)
        ((mul_sub 4 s 1).trans
          (congrArg₂ (fun first second : ℝ => first - second)
            rfl (mul_one 4)))
    _ = s ^ 3 - 4 * s ^ 2 + 4 * s := by
      exact
        (add_assoc (s ^ 3 - 4 * s ^ 2) 4 (4 * s - 4)).trans
          (congrArg (fun value : ℝ => s ^ 3 - 4 * s ^ 2 + value)
            ((add_sub_assoc 4 (4 * s) 4).trans
              (congrArg (fun value : ℝ => value - 4)
                (add_comm 4 (4 * s))).trans
              (add_sub_cancel_right (4 * s) 4)))
    _ = s * (s ^ 2 - 4 * s + 4) := by
      exact ((mul_sub s (s ^ 2) (4 * s)).trans
        (congrArg (fun value : ℝ => value + 4 * s)
          (congrArg₂ (fun first second : ℝ => first - second)
            (pow_succ s 2).symm (mul_assoc s 4 s).trans
              (congrArg (fun value : ℝ => value * s) (mul_comm s 4))))).trans
        (mul_add s (s ^ 2 - 4 * s) 4).symm)
    _ = s * (s - 2) ^ 2 := by
      have hinner : s ^ 2 - 4 * s + 4 = (s - 2) ^ 2 := by
        calc
        s ^ 2 - 4 * s + 4 = s * s - 2 * s - (s * 2 - 4) := by
          exact congrArg₂ (fun first second : ℝ => first - second)
            (congrArg₂ (fun first second : ℝ => first - second)
              (pow_two s) (congrArg (fun value : ℝ => value * s)
                (show (4 : ℝ) = 2 + 2 from rfl)).trans
                (add_mul 2 2 s))
            rfl
        _ = (s - 2) * (s - 2) :=
          (sub_mul s 2 (s - 2)).symm
        _ = (s - 2) ^ 2 := (pow_two (s - 2)).symm
      exact congrArg (fun value : ℝ => s * value) hinner

theorem Real.transitionScalar_unsquared_comparison
    {s d : ℝ}
    (hs : 4 ≤ s)
    (hd : 0 ≤ d)
    (hdSquare : d ^ 2 = s * (s - 4)) :
    2 * (s - 1) * (d + 2) ≤ s * (s - 2) ^ 2 := by
  have hgap :=
    Real.transitionScalarGapTerm_le_core hs hd hdSquare
  unfold Real.transitionScalarGapTerm at hgap
  have hadd := add_le_add_right hgap (4 * (s - 1))
  have hleft :
      2 * (s - 1) * d + 4 * (s - 1) =
        2 * (s - 1) * (d + 2) := by
    calc
      2 * (s - 1) * d + 4 * (s - 1) =
          2 * (s - 1) * d + (2 * (s - 1)) * 2 := by
        congrArg (fun value : ℝ => 2 * (s - 1) * d + value)
          ((mul_assoc 2 2 (s - 1)).symm.trans
            (congrArg (fun value : ℝ => value * (s - 1))
              (show (2 : ℝ) * 2 = 4 from rfl)).symm.trans
            (mul_comm (4 : ℝ) (s - 1)))
      _ = 2 * (s - 1) * (d + 2) :=
        (mul_add (2 * (s - 1)) d 2).symm
  have hright :=
    Real.transitionScalarCore_add_four_sub_one_eq_energySquare s
  exact le_trans (le_of_eq hleft.symm)
    (le_trans hadd (le_of_eq hright))

end
end LFunctions
end Boundary

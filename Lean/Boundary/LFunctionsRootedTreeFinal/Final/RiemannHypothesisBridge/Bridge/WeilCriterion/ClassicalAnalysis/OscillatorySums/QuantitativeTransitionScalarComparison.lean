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
  have htwoSquare : (2 : ℝ) ^ 2 = 4 := by
    exact Eq.trans (pow_two (2 : ℝ))
      (Real.transition_nat_cast_mul 2 2 4 rfl)
  calc
    (2 * (s - 1) * d) ^ 2 =
        (2 * (s - 1)) ^ 2 * d ^ 2 :=
      mul_pow (2 * (s - 1)) d 2
    _ = (2 ^ 2 * (s - 1) ^ 2) * d ^ 2 :=
      congrArg (fun value : ℝ => value * d ^ 2)
        (mul_pow 2 (s - 1) 2)
    _ = (4 * (s - 1) ^ 2) * d ^ 2 :=
      congrArg (fun value : ℝ => value * (s - 1) ^ 2 * d ^ 2)
        htwoSquare
    _ = 4 * (s - 1) ^ 2 * d ^ 2 := rfl

theorem Real.transitionRawDiscriminant_eq_core_sq_sub_gap_sq
    {s d : ℝ}
    (hdSquare : d ^ 2 = s * (s - 4)) :
    Real.transitionCurvatureRawDiscriminant s =
      Real.transitionScalarCore s ^ 2 -
        Real.transitionScalarGapTerm s d ^ 2 := by
  unfold Real.transitionCurvatureRawDiscriminant
  unfold Real.transitionScalarCore
  have hgap := Real.transitionScalarGapTerm_sq s d
  have hgapSubstituted :
      Real.transitionScalarGapTerm s d ^ 2 =
        4 * (s - 1) ^ 2 * (s * (s - 4)) :=
    Eq.trans hgap
      (congrArg (fun value : ℝ => 4 * (s - 1) ^ 2 * value)
        hdSquare)
  have hgapRaw :
      Real.transitionScalarGapTerm s d ^ 2 =
        4 * (s - 1) ^ 2 * s * (s - 4) :=
    Eq.trans hgapSubstituted
      (mul_assoc (4 * (s - 1) ^ 2) s (s - 4)).symm
  exact congrArg₂ (fun first second : ℝ => first - second)
    rfl hgapRaw.symm

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
        hidentity hraw
    exact sub_nonneg.mp hdifference
  exact le_of_sq_le_sq hsquares
    (Real.transitionScalarCore_nonneg hs)

theorem Real.transition_sub_double_add_eq_sub_sub
    (a b c : ℝ) :
    a - (b + b) + c = (a - b) - (b - c) := by
  calc
    a - (b + b) + c = (a + -(b + b)) + c :=
      congrArg (fun value : ℝ => value + c)
        (sub_eq_add_neg a (b + b))
    _ = (a + (-b + -b)) + c :=
      congrArg (fun value : ℝ => (a + value) + c)
        (neg_add_rev b b)
    _ = ((a + -b) + -b) + c :=
      congrArg (fun value : ℝ => value + c)
        (add_assoc a (-b) (-b)).symm
    _ = (a + -b) + (-b + c) :=
      add_assoc (a + -b) (-b) c
    _ = (a + -b) + (c + -b) :=
      congrArg (fun value : ℝ => (a + -b) + value)
        (add_comm (-b) c)
    _ = (a - b) + (c - b) :=
      congrArg₂ (fun first second : ℝ => first + second)
        (sub_eq_add_neg a b).symm (sub_eq_add_neg c b).symm
    _ = (a - b) + -(b - c) :=
      congrArg (fun value : ℝ => (a - b) + value)
        (neg_sub b c).symm
    _ = (a - b) - (b - c) :=
      (sub_eq_add_neg (a - b) (b - c)).symm

theorem Real.transition_sub_two_square_expansion
    (s : ℝ) :
    s ^ 2 - 4 * s + 4 = (s - 2) ^ 2 := by
  have htwoPlusTwo : (2 : ℝ) + 2 = 4 :=
    Real.transition_nat_cast_add 2 2 4 rfl
  have hfourMul : 4 * s = 2 * s + 2 * s := by
    exact Eq.trans
      (congrArg (fun coefficient : ℝ => coefficient * s)
        htwoPlusTwo.symm)
      (add_mul 2 2 s)
  have htwoMulTwo : (2 : ℝ) * 2 = 4 :=
    Real.transition_nat_cast_mul 2 2 4 rfl
  have hpolynomialToProduct :
      s ^ 2 - 4 * s + 4 = (s - 2) * (s - 2) := by
    calc
      s ^ 2 - 4 * s + 4 = s * s - (2 * s + 2 * s) + 4 :=
        congrArg₂ (fun first second : ℝ => first - second + 4)
          (pow_two s) hfourMul
      _ = (s * s - 2 * s) - (2 * s - 4) :=
        Real.transition_sub_double_add_eq_sub_sub (s * s) (2 * s) 4
      _ = (s * s - 2 * s) - (s * 2 - 4) :=
        congrArg (fun value : ℝ => (s * s - 2 * s) - (value - 4))
          (mul_comm 2 s)
      _ = (s * s - s * 2) - (2 * s - 2 * 2) :=
        congrArg₂ (fun first second : ℝ => first - second)
          (congrArg (fun value : ℝ => s * s - value)
            (mul_comm 2 s))
          (Eq.trans
            (congrArg (fun value : ℝ => value - 4)
              (mul_comm s 2))
            (congrArg (fun value : ℝ => 2 * s - value)
              htwoMulTwo.symm))
      _ = s * (s - 2) - 2 * (s - 2) :=
        congrArg₂ (fun first second : ℝ => first - second)
          (mul_sub s s 2).symm (mul_sub 2 s 2).symm
      _ = (s - 2) * (s - 2) :=
        (sub_mul s 2 (s - 2)).symm
  exact Eq.trans hpolynomialToProduct (pow_two (s - 2)).symm

theorem Real.transitionScalarCore_add_four_sub_one_eq_energySquare
    (s : ℝ) :
    Real.transitionScalarCore s + 4 * (s - 1) =
      s * (s - 2) ^ 2 := by
  unfold Real.transitionScalarCore
  have hfourLinear :
      (4 : ℝ) + 4 * (s - 1) = 4 * s := by
    calc
      (4 : ℝ) + 4 * (s - 1) = 4 + (4 * s - 4) :=
        congrArg (fun value : ℝ => 4 + value)
          (Eq.trans (mul_sub 4 s 1)
            (congrArg₂ (fun first second : ℝ => first - second)
              rfl (mul_one 4)))
      _ = (4 * s - 4) + 4 := add_comm 4 (4 * s - 4)
      _ = 4 * s := sub_add_cancel (4 * s) 4
  have hcube : s ^ 3 = s * s ^ 2 := by
    exact Eq.trans (pow_succ s 2) (mul_comm (s ^ 2) s)
  have hfourSquare : 4 * s ^ 2 = s * (4 * s) := by
    calc
      4 * s ^ 2 = 4 * (s * s) :=
        congrArg (fun value : ℝ => 4 * value) (pow_two s)
      _ = (4 * s) * s := (mul_assoc 4 s s).symm
      _ = (s * 4) * s :=
        congrArg (fun value : ℝ => value * s) (mul_comm 4 s)
      _ = s * (4 * s) := mul_assoc s 4 s
  have hfactor :
      s ^ 3 - 4 * s ^ 2 + 4 * s =
        s * (s ^ 2 - 4 * s + 4) := by
    calc
      s ^ 3 - 4 * s ^ 2 + 4 * s =
          s * s ^ 2 - s * (4 * s) + s * 4 :=
        congrArg₂ (fun first second : ℝ => first + second)
          (congrArg₂ (fun first second : ℝ => first - second)
            hcube hfourSquare)
          (mul_comm 4 s)
      _ = s * (s ^ 2 - 4 * s) + s * 4 :=
        congrArg (fun value : ℝ => value + s * 4)
          (mul_sub s (s ^ 2) (4 * s)).symm
      _ = s * (s ^ 2 - 4 * s + 4) :=
        (mul_add s (s ^ 2 - 4 * s) 4).symm
  calc
    s ^ 3 - 4 * s ^ 2 + 4 + 4 * (s - 1) =
        s ^ 3 - 4 * s ^ 2 + (4 + 4 * (s - 1)) :=
      add_assoc (s ^ 3 - 4 * s ^ 2) 4 (4 * (s - 1))
    _ = s ^ 3 - 4 * s ^ 2 + 4 * s :=
      congrArg (fun value : ℝ => s ^ 3 - 4 * s ^ 2 + value)
        hfourLinear
    _ = s * (s ^ 2 - 4 * s + 4) := hfactor
    _ = s * (s - 2) ^ 2 :=
      congrArg (fun value : ℝ => s * value)
        (Real.transition_sub_two_square_expansion s)

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
  have htwoMulTwo : (2 : ℝ) * 2 = 4 :=
    Real.transition_nat_cast_mul 2 2 4 rfl
  have hfourFactor :
      4 * (s - 1) = (2 * (s - 1)) * 2 := by
    calc
      4 * (s - 1) = (2 * 2) * (s - 1) :=
        congrArg (fun value : ℝ => value * (s - 1))
          htwoMulTwo.symm
      _ = 2 * (2 * (s - 1)) :=
        mul_assoc 2 2 (s - 1)
      _ = (2 * (s - 1)) * 2 :=
        mul_comm 2 (2 * (s - 1))
  have hleft :
      2 * (s - 1) * d + 4 * (s - 1) =
        2 * (s - 1) * (d + 2) := by
    calc
      2 * (s - 1) * d + 4 * (s - 1) =
          2 * (s - 1) * d + (2 * (s - 1)) * 2 :=
        congrArg (fun value : ℝ => 2 * (s - 1) * d + value)
          hfourFactor
      _ = 2 * (s - 1) * (d + 2) :=
        (mul_add (2 * (s - 1)) d 2).symm
  have hright :=
    Real.transitionScalarCore_add_four_sub_one_eq_energySquare s
  have htransportLeft :
      2 * (s - 1) * (d + 2) ≤
        2 * (s - 1) * d + 4 * (s - 1) :=
    le_of_eq hleft.symm
  have htransportRight :
      Real.transitionScalarCore s + 4 * (s - 1) ≤
        s * (s - 2) ^ 2 :=
    le_of_eq hright
  exact le_trans htransportLeft (le_trans hadd htransportRight)

end
end LFunctions
end Boundary

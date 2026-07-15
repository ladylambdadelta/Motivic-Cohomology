import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.QuantitativeTransitionSecondDerivative

/-!
# Second derivatives of the affine logarithmic collars

The affine collar maps have slopes `3` and `-3`, so the second derivatives
carry the common factor `9`.  The block cutoff second derivative is the usual
three-term product formula.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Real.quantitativeLogarithmicLeftCutoffSecondDerivative
    (a : ℤ) (x : ℝ) : ℝ :=
  9 * Real.smoothTransitionSecondDerivative
    (3 * (x - (a : ℝ)) + 1)

def Real.quantitativeLogarithmicRightCutoffSecondDerivative
    (b : ℤ) (x : ℝ) : ℝ :=
  9 * Real.smoothTransitionSecondDerivative
    (3 * ((b : ℝ) - x) + 1)

def Real.quantitativeLogarithmicBlockCutoffExplicitSecondDerivative
    (a b : ℤ) (x : ℝ) : ℝ :=
  Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x *
      Real.quantitativeLogarithmicRightCutoff b x +
    2 * Real.quantitativeLogarithmicLeftCutoffDerivative a x *
      Real.quantitativeLogarithmicRightCutoffDerivative b x +
    Real.quantitativeLogarithmicLeftCutoff a x *
      Real.quantitativeLogarithmicRightCutoffSecondDerivative b x

/-- The second derivative of the quantitative logarithmic block cutoff.

This definition belongs with the explicit collar calculus.  Downstream amplitude
owners consume it but do not own the derivative construction. -/
def Real.quantitativeLogarithmicBlockCutoffSecondDerivative
    (a b : ℤ) (x : ℝ) : ℝ :=
  deriv (Real.quantitativeLogarithmicBlockCutoffDerivative a b) x

theorem Real.quantitativeCutoff_three_mul_three :
    (3 : ℝ) * 3 = 9 :=
  Real.transitionSecondDerivative_natCast_mul 3 3 9
    (show (3 : ℕ) * 3 = 9 from rfl)

theorem Real.hasDerivAt_quantitativeLogarithmicLeftCutoffDerivative_explicit
    (a : ℤ) (x : ℝ) :
    HasDerivAt
      (Real.quantitativeLogarithmicLeftCutoffDerivative a)
      (Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x)
      x := by
  unfold Real.quantitativeLogarithmicLeftCutoffDerivative
  unfold Real.quantitativeLogarithmicLeftCutoffSecondDerivative
  have hshift := (hasDerivAt_id x).sub_const (a : ℝ)
  have hscaled := hshift.const_mul 3
  have hinner :
      HasDerivAt (fun y : ℝ => 3 * (y - (a : ℝ)) + 1) 3 x := by
    have hadd := hscaled.add_const 1
    exact Eq.subst
      (motive := fun value : ℝ =>
        HasDerivAt (fun y : ℝ => 3 * (y - (a : ℝ)) + 1) value x)
      (mul_one 3) hadd
  have houter := Real.hasDerivAt_smoothTransitionDerivative
    (3 * (x - (a : ℝ)) + 1)
  have hcomposition := houter.comp x hinner
  have hconstant := hcomposition.const_mul 3
  have hvalue :
      3 * (Real.smoothTransitionSecondDerivative
          (3 * (x - (a : ℝ)) + 1) * 3) =
        9 * Real.smoothTransitionSecondDerivative
          (3 * (x - (a : ℝ)) + 1) := by
    let value := Real.smoothTransitionSecondDerivative
      (3 * (x - (a : ℝ)) + 1)
    calc
      3 * (value * 3) = (3 * 3) * value := by
        exact
          (congrArg (fun v : ℝ => 3 * v) (mul_comm value 3)).trans
            (mul_assoc 3 3 value).symm
      _ = 9 * value :=
        congrArg (fun coefficient : ℝ => coefficient * value)
          Real.quantitativeCutoff_three_mul_three
  exact Eq.subst
    (motive := fun value : ℝ =>
      HasDerivAt
        (Real.quantitativeLogarithmicLeftCutoffDerivative a) value x)
    hvalue hconstant

theorem Real.hasDerivAt_quantitativeLogarithmicRightCutoffDerivative_explicit
    (b : ℤ) (x : ℝ) :
    HasDerivAt
      (Real.quantitativeLogarithmicRightCutoffDerivative b)
      (Real.quantitativeLogarithmicRightCutoffSecondDerivative b x)
      x := by
  unfold Real.quantitativeLogarithmicRightCutoffDerivative
  unfold Real.quantitativeLogarithmicRightCutoffSecondDerivative
  have hsub := (hasDerivAt_const x (b : ℝ)).sub (hasDerivAt_id x)
  have hscaled := hsub.const_mul 3
  have hinner :
      HasDerivAt (fun y : ℝ => 3 * ((b : ℝ) - y) + 1) (-3) x := by
    have hadd := hscaled.add_const 1
    exact Eq.subst
      (motive := fun value : ℝ =>
        HasDerivAt (fun y : ℝ => 3 * ((b : ℝ) - y) + 1) value x)
      Real.three_mul_zero_sub_one_eq_neg_three hadd
  have houter := Real.hasDerivAt_smoothTransitionDerivative
    (3 * ((b : ℝ) - x) + 1)
  have hcomposition := houter.comp x hinner
  have hconstant := hcomposition.const_mul (-3)
  have hvalue :
      (-3) * (Real.smoothTransitionSecondDerivative
          (3 * ((b : ℝ) - x) + 1) * (-3)) =
        9 * Real.smoothTransitionSecondDerivative
          (3 * ((b : ℝ) - x) + 1) := by
    let value := Real.smoothTransitionSecondDerivative
      (3 * ((b : ℝ) - x) + 1)
    calc
      (-3) * (value * (-3)) = ((-3) * (-3)) * value := by
        exact
          (congrArg (fun v : ℝ => (-3) * v) (mul_comm value (-3))).trans
            (mul_assoc (-3) (-3) value).symm
      _ = 9 * value :=
        congrArg (fun coefficient : ℝ => coefficient * value)
          ((neg_mul_neg 3 3).trans Real.quantitativeCutoff_three_mul_three)
  exact Eq.subst
    (motive := fun value : ℝ =>
      HasDerivAt
        (Real.quantitativeLogarithmicRightCutoffDerivative b) value x)
    hvalue hconstant

theorem Real.hasDerivAt_quantitativeLogarithmicBlockCutoffDerivative_explicit
    (a b : ℤ) (x : ℝ) :
    HasDerivAt
      (Real.quantitativeLogarithmicBlockCutoffDerivative a b)
      (Real.quantitativeLogarithmicBlockCutoffExplicitSecondDerivative a b x)
      x := by
  unfold Real.quantitativeLogarithmicBlockCutoffDerivative
  unfold Real.quantitativeLogarithmicBlockCutoffExplicitSecondDerivative
  have hleft := Real.hasDerivAt_quantitativeLogarithmicLeftCutoff a x
  have hright := Real.hasDerivAt_quantitativeLogarithmicRightCutoff b x
  have hleftDerivative :=
    Real.hasDerivAt_quantitativeLogarithmicLeftCutoffDerivative_explicit a x
  have hrightDerivative :=
    Real.hasDerivAt_quantitativeLogarithmicRightCutoffDerivative_explicit b x
  have hfirst := hleftDerivative.mul hright
  have hsecond := hleft.mul hrightDerivative
  have hsum := hfirst.add hsecond
  have hvalue :
      (Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x *
          Real.quantitativeLogarithmicRightCutoff b x +
        Real.quantitativeLogarithmicLeftCutoffDerivative a x *
          Real.quantitativeLogarithmicRightCutoffDerivative b x) +
      (Real.quantitativeLogarithmicLeftCutoffDerivative a x *
          Real.quantitativeLogarithmicRightCutoffDerivative b x +
        Real.quantitativeLogarithmicLeftCutoff a x *
          Real.quantitativeLogarithmicRightCutoffSecondDerivative b x) =
      Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x *
          Real.quantitativeLogarithmicRightCutoff b x +
        2 * Real.quantitativeLogarithmicLeftCutoffDerivative a x *
          Real.quantitativeLogarithmicRightCutoffDerivative b x +
        Real.quantitativeLogarithmicLeftCutoff a x *
          Real.quantitativeLogarithmicRightCutoffSecondDerivative b x := by
    let first := Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x *
      Real.quantitativeLogarithmicRightCutoff b x
    let cross := Real.quantitativeLogarithmicLeftCutoffDerivative a x *
      Real.quantitativeLogarithmicRightCutoffDerivative b x
    let last := Real.quantitativeLogarithmicLeftCutoff a x *
      Real.quantitativeLogarithmicRightCutoffSecondDerivative b x
    have hdouble : cross + cross = 2 * cross := (two_mul cross).symm
    have hcollect :
        (first + cross) + (cross + last) =
          first + (cross + (cross + last)) :=
      add_assoc first cross (cross + last)
    have hcrossReassociate :
        cross + (cross + last) = (cross + cross) + last :=
      (add_assoc cross cross last).symm
    have hcrossDouble :
        (cross + cross) + last = (2 * cross) + last :=
      congrArg (fun value : ℝ => value + last) hdouble
    have hfinalReassociate :
        first + ((2 * cross) + last) =
          (first + 2 * cross) + last :=
      (add_assoc first (2 * cross) last).symm
    have hcrossPublic :
        2 * cross =
          2 * Real.quantitativeLogarithmicLeftCutoffDerivative a x *
            Real.quantitativeLogarithmicRightCutoffDerivative b x :=
      (mul_assoc 2
        (Real.quantitativeLogarithmicLeftCutoffDerivative a x)
        (Real.quantitativeLogarithmicRightCutoffDerivative b x)).symm
    have hpublic :
        (first + 2 * cross) + last =
          Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x *
              Real.quantitativeLogarithmicRightCutoff b x +
            2 * Real.quantitativeLogarithmicLeftCutoffDerivative a x *
              Real.quantitativeLogarithmicRightCutoffDerivative b x +
            Real.quantitativeLogarithmicLeftCutoff a x *
              Real.quantitativeLogarithmicRightCutoffSecondDerivative b x :=
      congrArg (fun middle : ℝ => (first + middle) + last) hcrossPublic
    exact
      hcollect.trans
        ((congrArg (fun value : ℝ => first + value)
          (hcrossReassociate.trans hcrossDouble)).trans
          (hfinalReassociate.trans hpublic))
  exact Eq.subst
    (motive := fun value : ℝ =>
      HasDerivAt
        (Real.quantitativeLogarithmicBlockCutoffDerivative a b) value x)
    hvalue hsum

theorem Real.quantitativeLogarithmicBlockCutoffSecondDerivative_eq_explicit
    (a b : ℤ) (x : ℝ) :
    Real.quantitativeLogarithmicBlockCutoffSecondDerivative a b x =
      Real.quantitativeLogarithmicBlockCutoffExplicitSecondDerivative a b x := by
  unfold Real.quantitativeLogarithmicBlockCutoffSecondDerivative
  exact
    (Real.hasDerivAt_quantitativeLogarithmicBlockCutoffDerivative_explicit
      a b x).deriv

theorem Real.abs_quantitativeLogarithmicLeftCutoffSecondDerivative_le
    (a : ℤ) (x : ℝ) :
    |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x| ≤
      9 * (6400 * (Real.exp 2) ^ 4) := by
  unfold Real.quantitativeLogarithmicLeftCutoffSecondDerivative
  have hproduct := abs_mul 9
    (Real.smoothTransitionSecondDerivative
      (3 * (x - (a : ℝ)) + 1))
  have hnineAbs : |(9 : ℝ)| = 9 := abs_of_nonneg (Nat.cast_nonneg 9)
  exact le_trans (le_of_eq hproduct)
    (mul_le_mul
      (le_of_eq hnineAbs)
      (Real.abs_smoothTransitionSecondDerivative_le_explicit
        (3 * (x - (a : ℝ)) + 1))
      (abs_nonneg _) (Nat.cast_nonneg 9))

theorem Real.abs_quantitativeLogarithmicRightCutoffSecondDerivative_le
    (b : ℤ) (x : ℝ) :
    |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x| ≤
      9 * (6400 * (Real.exp 2) ^ 4) := by
  unfold Real.quantitativeLogarithmicRightCutoffSecondDerivative
  have hproduct := abs_mul 9
    (Real.smoothTransitionSecondDerivative
      (3 * ((b : ℝ) - x) + 1))
  have hnineAbs : |(9 : ℝ)| = 9 := abs_of_nonneg (Nat.cast_nonneg 9)
  exact le_trans (le_of_eq hproduct)
    (mul_le_mul
      (le_of_eq hnineAbs)
      (Real.abs_smoothTransitionSecondDerivative_le_explicit
        (3 * ((b : ℝ) - x) + 1))
      (abs_nonneg _) (Nat.cast_nonneg 9))

end
end LFunctions
end Boundary

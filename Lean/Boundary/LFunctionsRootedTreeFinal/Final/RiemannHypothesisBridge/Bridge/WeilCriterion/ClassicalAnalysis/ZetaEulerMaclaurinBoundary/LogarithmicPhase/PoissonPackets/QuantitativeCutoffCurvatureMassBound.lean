import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.QuantitativeCutoffSecondDerivativeSupport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeCutoffVariationBound

/-!
# Fixed curvature mass of the quantitative cutoff

Each collar second derivative is supported on an interval of width one third.
The mixed first-derivative product vanishes on ordered blocks.  Consequently
the full cutoff curvature mass is bounded by a universal constant.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped Interval

def Real.quantitativeTransitionCurvatureBound : ℝ :=
  6400 * (Real.exp 2) ^ 4

def Real.quantitativeLogarithmicCollarCurvatureBound : ℝ :=
  9 * Real.quantitativeTransitionCurvatureBound

def Real.quantitativeLogarithmicBlockCurvatureMassBound : ℝ :=
  6 * Real.quantitativeTransitionCurvatureBound

theorem Real.quantitativeTransitionCurvatureBound_nonneg :
    0 ≤ Real.quantitativeTransitionCurvatureBound := by
  unfold Real.quantitativeTransitionCurvatureBound
  exact mul_nonneg (Nat.cast_nonneg 6400) (pow_nonneg (Real.exp_pos 2).le 4)

theorem Real.quantitativeLogarithmicCollarCurvatureBound_nonneg :
    0 ≤ Real.quantitativeLogarithmicCollarCurvatureBound := by
  unfold Real.quantitativeLogarithmicCollarCurvatureBound
  exact mul_nonneg (Nat.cast_nonneg 9)
    Real.quantitativeTransitionCurvatureBound_nonneg

theorem Real.quantitativeLogarithmicBlockCurvatureMassBound_nonneg :
    0 ≤ Real.quantitativeLogarithmicBlockCurvatureMassBound := by
  unfold Real.quantitativeLogarithmicBlockCurvatureMassBound
  exact mul_nonneg (Nat.cast_nonneg 6)
    Real.quantitativeTransitionCurvatureBound_nonneg

theorem Real.abs_quantitativeLogarithmicLeftCutoffSecondDerivative_le_collarBound
    (a : ℤ) (x : ℝ) :
    |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x| ≤
      Real.quantitativeLogarithmicCollarCurvatureBound := by
  unfold Real.quantitativeLogarithmicCollarCurvatureBound
  unfold Real.quantitativeTransitionCurvatureBound
  exact Real.abs_quantitativeLogarithmicLeftCutoffSecondDerivative_le a x

theorem Real.abs_quantitativeLogarithmicRightCutoffSecondDerivative_le_collarBound
    (b : ℤ) (x : ℝ) :
    |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x| ≤
      Real.quantitativeLogarithmicCollarCurvatureBound := by
  unfold Real.quantitativeLogarithmicCollarCurvatureBound
  unfold Real.quantitativeTransitionCurvatureBound
  exact Real.abs_quantitativeLogarithmicRightCutoffSecondDerivative_le b x

theorem Real.continuous_quantitativeLogarithmicLeftCutoffSecondDerivative
    (a : ℤ) :
    Continuous (Real.quantitativeLogarithmicLeftCutoffSecondDerivative a) := by
  have hfirst :=
    (contDiff_infty_iff_deriv.mp
      (Real.contDiff_quantitativeLogarithmicLeftCutoff a)).2
  have hsecond := (contDiff_infty_iff_deriv.mp hfirst).2.continuous
  have hfunction :
      deriv (deriv (Real.quantitativeLogarithmicLeftCutoff a)) =
        Real.quantitativeLogarithmicLeftCutoffSecondDerivative a := by
    funext x
    have hfirstDerivative :=
      Real.deriv_quantitativeLogarithmicLeftCutoff a x
    have heventual :
        deriv (Real.quantitativeLogarithmicLeftCutoff a) =ᶠ[nhds x]
          Real.quantitativeLogarithmicLeftCutoffDerivative a := by
      exact Filter.Eventually.of_forall
        (fun y => Real.deriv_quantitativeLogarithmicLeftCutoff a y)
    exact heventual.deriv_eq.trans
      (Real.hasDerivAt_quantitativeLogarithmicLeftCutoffDerivative_explicit
        a x).deriv
  exact Eq.subst
    (motive := fun function : ℝ → ℝ => Continuous function)
    hfunction hsecond

theorem Real.continuous_quantitativeLogarithmicRightCutoffSecondDerivative
    (b : ℤ) :
    Continuous (Real.quantitativeLogarithmicRightCutoffSecondDerivative b) := by
  have hfirst :=
    (contDiff_infty_iff_deriv.mp
      (Real.contDiff_quantitativeLogarithmicRightCutoff b)).2
  have hsecond := (contDiff_infty_iff_deriv.mp hfirst).2.continuous
  have hfunction :
      deriv (deriv (Real.quantitativeLogarithmicRightCutoff b)) =
        Real.quantitativeLogarithmicRightCutoffSecondDerivative b := by
    funext x
    have heventual :
        deriv (Real.quantitativeLogarithmicRightCutoff b) =ᶠ[nhds x]
          Real.quantitativeLogarithmicRightCutoffDerivative b := by
      exact Filter.Eventually.of_forall
        (fun y => Real.deriv_quantitativeLogarithmicRightCutoff b y)
    exact heventual.deriv_eq.trans
      (Real.hasDerivAt_quantitativeLogarithmicRightCutoffDerivative_explicit
        b x).deriv
  exact Eq.subst
    (motive := fun function : ℝ → ℝ => Continuous function)
    hfunction hsecond

theorem Real.integral_abs_quantitativeLogarithmicLeftCutoffSecondDerivative_le
    (a b : ℤ)
    (hab : a ≤ b) :
    (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
        Complex.logarithmicPhaseQuantitativeSupportRight b,
      |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x|) ≤
      3 * Real.quantitativeTransitionCurvatureBound := by
  let left := Complex.logarithmicPhaseQuantitativeSupportLeft a
  let core := (a : ℝ)
  let right := Complex.logarithmicPhaseQuantitativeSupportRight b
  have hleftCore : left ≤ core := by
    unfold left
    unfold core
    unfold Complex.logarithmicPhaseQuantitativeSupportLeft
    exact sub_le_self (a : ℝ) (le_of_lt Real.one_div_three_pos)
  have hcoreRight : core ≤ right := by
    unfold core
    unfold right
    unfold Complex.logarithmicPhaseQuantitativeSupportRight
    exact le_trans (Int.cast_le.mpr hab)
      (le_add_of_nonneg_right (le_of_lt Real.one_div_three_pos))
  have hdensityContinuous : Continuous
      (fun x : ℝ =>
        |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x|) :=
    (Real.continuous_quantitativeLogarithmicLeftCutoffSecondDerivative a).abs
  have hleftIntegrable : IntervalIntegrable
      (fun x : ℝ =>
        |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x|)
      volume left core :=
    hdensityContinuous.intervalIntegrable left core
  have hrightIntegrable : IntervalIntegrable
      (fun x : ℝ =>
        |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x|)
      volume core right :=
    hdensityContinuous.intervalIntegrable core right
  have hrightZero :
      (∫ x in core..right,
        |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x|) = 0 := by
    have hzeroFunction :
        (∫ x in core..right,
          |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x|) =
          ∫ _x in core..right, (0 : ℝ) :=
      intervalIntegral.integral_congr
        (fun x hx => by
          have hminimum : min core right = core := min_eq_left hcoreRight
          have hxCore : core ≤ x :=
            Eq.subst (motive := fun value : ℝ => value ≤ x)
              hminimum hx.1
          exact
            (congrArg abs
              (Real.quantitativeLogarithmicLeftCutoffSecondDerivative_eq_zero_of_core_le
                a hxCore)).trans abs_zero)
    exact hzeroFunction.trans intervalIntegral.integral_zero
  have hsplit :
      (∫ x in left..right,
        |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x|) =
        (∫ x in left..core,
          |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x|) +
        ∫ x in core..right,
          |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x| :=
    (intervalIntegral.integral_add_adjacent_intervals
      hleftIntegrable hrightIntegrable).symm
  have hleftBound :
      (∫ x in left..core,
        |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x|) ≤
        (core - left) * Real.quantitativeLogarithmicCollarCurvatureBound := by
    have hconstant : IntervalIntegrable
        (fun _x : ℝ => Real.quantitativeLogarithmicCollarCurvatureBound)
        volume left core := continuous_const.intervalIntegrable left core
    have hmono := intervalIntegral.integral_mono_on hleftCore
      hleftIntegrable
      hconstant
      (fun x hx =>
        Real.abs_quantitativeLogarithmicLeftCutoffSecondDerivative_le_collarBound
          a x)
    exact le_trans hmono
      (le_of_eq
        ((intervalIntegral.integral_const
          Real.quantitativeLogarithmicCollarCurvatureBound).trans
          (Algebra.id.smul_eq_mul
            (core - left)
            Real.quantitativeLogarithmicCollarCurvatureBound)))
  have hwidth : core - left = 1 / 3 := by
    unfold core
    unfold left
    unfold Complex.logarithmicPhaseQuantitativeSupportLeft
    calc
      (a : ℝ) - ((a : ℝ) - 1 / 3) =
          (a : ℝ) + -((a : ℝ) - 1 / 3) :=
        sub_eq_add_neg _ _
      _ = (a : ℝ) + (-(a : ℝ) + 1 / 3) :=
        congrArg (fun value : ℝ => (a : ℝ) + value)
          ((neg_sub _ _).trans
            ((sub_eq_add_neg _ _).trans (add_comm _ _)))
      _ = ((a : ℝ) + -(a : ℝ)) + 1 / 3 :=
        (add_assoc _ _ _).symm
      _ = 0 + 1 / 3 :=
        congrArg (fun value : ℝ => value + 1 / 3) (add_neg_cancel _)
      _ = 1 / 3 := zero_add _
  have hnormalize :
      (core - left) * Real.quantitativeLogarithmicCollarCurvatureBound =
        3 * Real.quantitativeTransitionCurvatureBound := by
    unfold Real.quantitativeLogarithmicCollarCurvatureBound
    exact (congrArg
      (fun value : ℝ => value * (9 * Real.quantitativeTransitionCurvatureBound))
      hwidth).trans <| by
        have hthreeNe : (3 : ℝ) ≠ 0 :=
          ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2))
        have hnine : (9 : ℝ) = 3 * 3 := by
          exact
            (congrArg (fun value : ℕ => (value : ℝ))
              (show (9 : ℕ) = 3 * 3 from rfl)).trans
              (Nat.cast_mul 3 3)
        calc
          (1 / 3 : ℝ) * (9 * Real.quantitativeTransitionCurvatureBound) =
            ((1 / 3 : ℝ) * 9) * Real.quantitativeTransitionCurvatureBound :=
              (mul_assoc _ _ _).symm
          _ = 3 * Real.quantitativeTransitionCurvatureBound := by
            exact congrArg
              (fun value : ℝ => value * Real.quantitativeTransitionCurvatureBound)
              (show (1 / 3 : ℝ) * 9 = 3 by
                calc
                  (1 / 3 : ℝ) * 9 = (1 / 3 : ℝ) * (3 * 3) :=
                    congrArg (fun value : ℝ => (1 / 3 : ℝ) * value) hnine
                  _ = ((1 / 3 : ℝ) * 3) * 3 :=
                    (mul_assoc _ _ _).symm
                  _ = 1 * 3 :=
                    congrArg (fun value : ℝ => value * 3)
                      (one_div_mul_cancel hthreeNe)
                  _ = 3 := one_mul 3)
  have htotal :
      (∫ x in left..right,
        |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x|) =
        (∫ x in left..core,
          |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x|) + 0 :=
    hsplit.trans
      (congrArg
        (fun value : ℝ =>
          (∫ x in left..core,
            |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x|) + value)
        hrightZero)
  exact le_trans (le_of_eq (htotal.trans (add_zero _)))
    (le_trans hleftBound (le_of_eq hnormalize))

theorem Real.integral_abs_quantitativeLogarithmicRightCutoffSecondDerivative_le
    (a b : ℤ)
    (hab : a ≤ b) :
    (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
        Complex.logarithmicPhaseQuantitativeSupportRight b,
      |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x|) ≤
      3 * Real.quantitativeTransitionCurvatureBound := by
  let left := Complex.logarithmicPhaseQuantitativeSupportLeft a
  let core := (b : ℝ)
  let right := Complex.logarithmicPhaseQuantitativeSupportRight b
  have hleftCore : left ≤ core := by
    unfold left
    unfold core
    unfold Complex.logarithmicPhaseQuantitativeSupportLeft
    exact le_trans
      (sub_le_self (a : ℝ) (le_of_lt Real.one_div_three_pos))
      (Int.cast_le.mpr hab)
  have hcoreRight : core ≤ right := by
    unfold core
    unfold right
    unfold Complex.logarithmicPhaseQuantitativeSupportRight
    exact le_add_of_nonneg_right (le_of_lt Real.one_div_three_pos)
  have hdensityContinuous : Continuous
      (fun x : ℝ =>
        |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x|) :=
    (Real.continuous_quantitativeLogarithmicRightCutoffSecondDerivative b).abs
  have hleftIntegrable : IntervalIntegrable
      (fun x : ℝ =>
        |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x|)
      volume left core :=
    hdensityContinuous.intervalIntegrable left core
  have hrightIntegrable : IntervalIntegrable
      (fun x : ℝ =>
        |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x|)
      volume core right :=
    hdensityContinuous.intervalIntegrable core right
  have hleftZero :
      (∫ x in left..core,
        |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x|) = 0 := by
    have hzeroFunction :
        (∫ x in left..core,
          |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x|) =
          ∫ _x in left..core, (0 : ℝ) :=
      intervalIntegral.integral_congr
        (fun x hx => by
          have hmaximum : max left core = core := max_eq_right hleftCore
          have hxCore : x ≤ core :=
            Eq.subst (motive := fun value : ℝ => x ≤ value)
              hmaximum hx.2
          exact
            (congrArg abs
              (Real.quantitativeLogarithmicRightCutoffSecondDerivative_eq_zero_of_le_core
                b hxCore)).trans abs_zero)
    exact hzeroFunction.trans intervalIntegral.integral_zero
  have hsplit :
      (∫ x in left..right,
        |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x|) =
        (∫ x in left..core,
          |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x|) +
        ∫ x in core..right,
          |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x| :=
    (intervalIntegral.integral_add_adjacent_intervals
      hleftIntegrable hrightIntegrable).symm
  have hrightBound :
      (∫ x in core..right,
        |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x|) ≤
        (right - core) * Real.quantitativeLogarithmicCollarCurvatureBound := by
    have hconstant : IntervalIntegrable
        (fun _x : ℝ => Real.quantitativeLogarithmicCollarCurvatureBound)
        volume core right := continuous_const.intervalIntegrable core right
    have hmono := intervalIntegral.integral_mono_on hcoreRight
      hrightIntegrable hconstant
      (fun x hx =>
        Real.abs_quantitativeLogarithmicRightCutoffSecondDerivative_le_collarBound
          b x)
    exact le_trans hmono
      (le_of_eq
        ((intervalIntegral.integral_const
          Real.quantitativeLogarithmicCollarCurvatureBound).trans
          (Algebra.id.smul_eq_mul
            (right - core)
            Real.quantitativeLogarithmicCollarCurvatureBound)))
  have hwidth : right - core = 1 / 3 := by
    unfold right
    unfold core
    unfold Complex.logarithmicPhaseQuantitativeSupportRight
    exact add_sub_cancel_left (b : ℝ) (1 / 3)
  have hnormalize :
      (right - core) * Real.quantitativeLogarithmicCollarCurvatureBound =
        3 * Real.quantitativeTransitionCurvatureBound := by
    unfold Real.quantitativeLogarithmicCollarCurvatureBound
    exact (congrArg
      (fun value : ℝ => value * (9 * Real.quantitativeTransitionCurvatureBound))
      hwidth).trans <| by
        have hthreeNe : (3 : ℝ) ≠ 0 :=
          ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2))
        have hnine : (9 : ℝ) = 3 * 3 := by
          exact
            (congrArg (fun value : ℕ => (value : ℝ))
              (show (9 : ℕ) = 3 * 3 from rfl)).trans
              (Nat.cast_mul 3 3)
        calc
          (1 / 3 : ℝ) * (9 * Real.quantitativeTransitionCurvatureBound) =
            ((1 / 3 : ℝ) * 9) * Real.quantitativeTransitionCurvatureBound :=
              (mul_assoc _ _ _).symm
          _ = 3 * Real.quantitativeTransitionCurvatureBound := by
            exact congrArg
              (fun value : ℝ => value * Real.quantitativeTransitionCurvatureBound)
              (show (1 / 3 : ℝ) * 9 = 3 by
                calc
                  (1 / 3 : ℝ) * 9 = (1 / 3 : ℝ) * (3 * 3) :=
                    congrArg (fun value : ℝ => (1 / 3 : ℝ) * value) hnine
                  _ = ((1 / 3 : ℝ) * 3) * 3 :=
                    (mul_assoc _ _ _).symm
                  _ = 1 * 3 :=
                    congrArg (fun value : ℝ => value * 3)
                      (one_div_mul_cancel hthreeNe)
                  _ = 3 := one_mul 3)
  have htotal :
      (∫ x in left..right,
        |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x|) =
        0 + (∫ x in core..right,
          |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x|) :=
    hsplit.trans
      (congrArg
        (fun value : ℝ => value +
          ∫ x in core..right,
            |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x|)
        hleftZero)
  exact le_trans (le_of_eq (htotal.trans (zero_add _)))
    (le_trans hrightBound (le_of_eq hnormalize))

theorem Real.abs_quantitativeLogarithmicBlockCutoffSecondDerivative_le_collars
    (a b : ℤ)
    (hab : a ≤ b)
    (x : ℝ) :
    |Real.quantitativeLogarithmicBlockCutoffSecondDerivative a b x| ≤
      |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x| +
        |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x| := by
  have hexplicit :=
    Real.quantitativeLogarithmicBlockCutoffSecondDerivative_eq_explicit a b x
  unfold Real.quantitativeLogarithmicBlockCutoffExplicitSecondDerivative at hexplicit
  have hcross :=
    Real.quantitativeLogarithmicCollarDerivative_product_eq_zero a b hab x
  have hcrossScaled :
      2 * Real.quantitativeLogarithmicLeftCutoffDerivative a x *
        Real.quantitativeLogarithmicRightCutoffDerivative b x = 0 := by
    exact (mul_assoc 2 _ _).trans
      ((congrArg (fun value : ℝ => 2 * value) hcross).trans (mul_zero 2))
  have hnormalized :
      Real.quantitativeLogarithmicBlockCutoffSecondDerivative a b x =
        Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x *
            Real.quantitativeLogarithmicRightCutoff b x +
          Real.quantitativeLogarithmicLeftCutoff a x *
            Real.quantitativeLogarithmicRightCutoffSecondDerivative b x := by
    exact hexplicit.trans <| by
      exact
        (congrArg
          (fun value : ℝ =>
            Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x *
                Real.quantitativeLogarithmicRightCutoff b x + value +
              Real.quantitativeLogarithmicLeftCutoff a x *
                Real.quantitativeLogarithmicRightCutoffSecondDerivative b x)
          hcrossScaled).trans
          (congrArg
            (fun value : ℝ => value +
              Real.quantitativeLogarithmicLeftCutoff a x *
                Real.quantitativeLogarithmicRightCutoffSecondDerivative b x)
            (add_zero
              (Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x *
                Real.quantitativeLogarithmicRightCutoff b x)))
  have htriangle := abs_add
    (Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x *
      Real.quantitativeLogarithmicRightCutoff b x)
    (Real.quantitativeLogarithmicLeftCutoff a x *
      Real.quantitativeLogarithmicRightCutoffSecondDerivative b x)
  have hrightCutoffAbs :
      |Real.quantitativeLogarithmicRightCutoff b x| ≤ 1 :=
    le_trans
      (le_of_eq (abs_of_nonneg
        (Real.quantitativeLogarithmicRightCutoff_nonneg b x)))
      (Real.quantitativeLogarithmicRightCutoff_le_one b x)
  have hleftCutoffAbs :
      |Real.quantitativeLogarithmicLeftCutoff a x| ≤ 1 :=
    le_trans
      (le_of_eq (abs_of_nonneg
        (Real.quantitativeLogarithmicLeftCutoff_nonneg a x)))
      (Real.quantitativeLogarithmicLeftCutoff_le_one a x)
  have hfirst :
      |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x *
          Real.quantitativeLogarithmicRightCutoff b x| ≤
        |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x| := by
    exact le_trans (le_of_eq (abs_mul _ _))
      (le_trans
        (mul_le_mul_of_nonneg_left hrightCutoffAbs (abs_nonneg _))
        (le_of_eq (mul_one _)))
  have hsecond :
      |Real.quantitativeLogarithmicLeftCutoff a x *
          Real.quantitativeLogarithmicRightCutoffSecondDerivative b x| ≤
        |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x| := by
    exact le_trans (le_of_eq (abs_mul _ _))
      (le_trans
        (mul_le_mul_of_nonneg_right hleftCutoffAbs (abs_nonneg _))
        (le_of_eq (one_mul _)))
  exact le_trans (le_of_eq (congrArg abs hnormalized))
    (le_trans htriangle (add_le_add hfirst hsecond))

theorem Complex.logarithmicPhaseQuantitativeCutoffCurvatureMass_le_universal
    (a b : ℤ)
    (hab : a ≤ b) :
    Complex.logarithmicPhaseQuantitativeCutoffCurvatureMass a b ≤
      Real.quantitativeLogarithmicBlockCurvatureMassBound := by
  let left := Complex.logarithmicPhaseQuantitativeSupportLeft a
  let right := Complex.logarithmicPhaseQuantitativeSupportRight b
  have hleftRight :=
    Complex.logarithmicPhaseQuantitativeSupportLeft_le_right a b hab
  have hblock :=
    Complex.intervalIntegrable_logarithmicPhaseQuantitativeCutoffCurvatureDensity
      a b left right
  have hleftContinuous : Continuous
      (fun x : ℝ =>
        |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x|) :=
    (Real.continuous_quantitativeLogarithmicLeftCutoffSecondDerivative a).abs
  have hrightContinuous : Continuous
      (fun x : ℝ =>
        |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x|) :=
    (Real.continuous_quantitativeLogarithmicRightCutoffSecondDerivative b).abs
  have hleftIntegrable : IntervalIntegrable
      (fun x : ℝ =>
        |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x|)
      volume left right :=
    hleftContinuous.intervalIntegrable left right
  have hrightIntegrable : IntervalIntegrable
      (fun x : ℝ =>
        |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x|)
      volume left right :=
    hrightContinuous.intervalIntegrable left right
  have hcollars : IntervalIntegrable
      (fun x : ℝ =>
        |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x| +
          |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x|)
      volume left right :=
    hleftIntegrable.add hrightIntegrable
  have hmono := intervalIntegral.integral_mono_on hleftRight hblock hcollars
    (fun x hx =>
      Real.abs_quantitativeLogarithmicBlockCutoffSecondDerivative_le_collars
        a b hab x)
  have hadd := intervalIntegral.integral_add
    hleftIntegrable hrightIntegrable
  have hleft :=
    Real.integral_abs_quantitativeLogarithmicLeftCutoffSecondDerivative_le
      a b hab
  have hright :=
    Real.integral_abs_quantitativeLogarithmicRightCutoffSecondDerivative_le
      a b hab
  have hsum := add_le_add hleft hright
  have hnormalize :
      3 * Real.quantitativeTransitionCurvatureBound +
          3 * Real.quantitativeTransitionCurvatureBound =
        Real.quantitativeLogarithmicBlockCurvatureMassBound := by
    unfold Real.quantitativeLogarithmicBlockCurvatureMassBound
    exact
      (add_mul 3 3 Real.quantitativeTransitionCurvatureBound).symm.trans
        (congrArg
          (fun value : ℝ => value * Real.quantitativeTransitionCurvatureBound)
          (show (3 : ℝ) + 3 = 6 by
            exact (Nat.cast_add 3 3).symm.trans
              (congrArg (fun value : ℕ => (value : ℝ))
                (show (3 + 3 : ℕ) = 6 from rfl))))
  unfold Complex.logarithmicPhaseQuantitativeCutoffCurvatureMass
  exact le_trans hmono
    (le_trans (le_of_eq hadd)
      (le_trans hsum (le_of_eq hnormalize)))

end
end LFunctions
end Boundary

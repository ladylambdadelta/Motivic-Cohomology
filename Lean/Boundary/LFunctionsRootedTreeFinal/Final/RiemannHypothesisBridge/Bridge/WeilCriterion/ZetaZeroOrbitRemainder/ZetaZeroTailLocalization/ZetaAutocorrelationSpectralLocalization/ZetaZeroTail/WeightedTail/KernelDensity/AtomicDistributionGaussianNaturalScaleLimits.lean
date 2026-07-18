import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionGaussianGeometry
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Group
import Mathlib.Order.Filter.AtTopBot.Ring

/-!
# Natural-scale Gaussian limits

This owner isolates the real-variable limit calculation used by completed-zero
Gaussian localization.  The statements contain no zero-set geometry.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- The positive natural scale tends to positive infinity. -/
theorem naturalScaleReal_tendsto_atTop :
    Filter.Tendsto
      (fun n : ℕ => (n : ℝ) + 1)
      Filter.atTop
      Filter.atTop :=
  Filter.tendsto_atTop_add_const_right
    (l := Filter.atTop)
    1
    tendsto_natCast_atTop_atTop

/-- The square of the positive natural scale tends to positive infinity. -/
theorem naturalScaleReal_square_tendsto_atTop :
    Filter.Tendsto
      (fun n : ℕ => ((n : ℝ) + 1) ^ 2)
      Filter.atTop
      Filter.atTop :=
  (Filter.tendsto_pow_atTop two_ne_zero).comp naturalScaleReal_tendsto_atTop

/-- Rewriting a negative quadratic coefficient as a positive decay rate. -/
theorem naturalScale_quadratic_div_four_eq_neg_rate
    (quadratic rate : ℝ)
    (hrate : rate = -(quadratic / 4))
    (n : ℕ) :
    ((((n : ℝ) + 1) ^ 2 / 4) * quadratic) =
      -(rate * ((n : ℝ) + 1) ^ 2) := by
  have hdivideReassociate :
      (((n : ℝ) + 1) ^ 2 / 4) * quadratic =
        (((n : ℝ) + 1) ^ 2) * (quadratic / 4) :=
    Eq.trans
      (div_mul_eq_mul_div
        (((n : ℝ) + 1) ^ 2)
        4
        quadratic)
      (mul_div_assoc (((n : ℝ) + 1) ^ 2) quadratic 4)
  have hrateDefinition : quadratic / 4 = -rate :=
    (Eq.trans
      (congrArg Neg.neg hrate)
      (neg_neg (quadratic / 4))).symm
  exact Eq.trans hdivideReassociate
    (Eq.trans
      (congrArg
        (fun value : ℝ => ((n : ℝ) + 1) ^ 2 * value)
        hrateDefinition)
      (Eq.trans
        (mul_neg (((n : ℝ) + 1) ^ 2) rate)
        (congrArg Neg.neg
          (mul_comm (((n : ℝ) + 1) ^ 2) rate))))

/-- A Gaussian exponential at a positive natural-square rate tends to zero. -/
theorem naturalScaleGaussianExponential_tendsto_zero
    (rate : ℝ)
    (hrate : 0 < rate) :
    Filter.Tendsto
      (fun n : ℕ =>
        Real.exp (-(rate * ((n : ℝ) + 1) ^ 2)))
      Filter.atTop
      (nhds 0) := by
  have hrateScaleSquareAtTop :
      Filter.Tendsto
        (fun n : ℕ => rate * ((n : ℝ) + 1) ^ 2)
        Filter.atTop
        Filter.atTop :=
    naturalScaleReal_square_tendsto_atTop.const_mul_atTop hrate
  exact
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      hrateScaleSquareAtTop

/-- Multiplying the natural-scale Gaussian exponential by a fixed real factor
preserves convergence to zero. -/
theorem naturalScaleScaledGaussianExponential_tendsto_zero
    (baseNorm quadratic rate : ℝ)
    (hrate : rate = -(quadratic / 4))
    (hratePositive : 0 < rate) :
    Filter.Tendsto
      (fun n : ℕ =>
        baseNorm * Real.exp
          ((((n : ℝ) + 1) ^ 2 / 4) * quadratic))
      Filter.atTop
      (nhds 0) := by
  have hexponentialLimit :=
    naturalScaleGaussianExponential_tendsto_zero rate hratePositive
  have hrawLimit :
      Filter.Tendsto
        (fun n : ℕ =>
          baseNorm * Real.exp (-(rate * ((n : ℝ) + 1) ^ 2)))
        Filter.atTop
        (nhds (baseNorm * 0)) :=
    Filter.Tendsto.const_mul baseNorm hexponentialLimit
  have hrawZeroLimit :
      Filter.Tendsto
        (fun n : ℕ =>
          baseNorm * Real.exp (-(rate * ((n : ℝ) + 1) ^ 2)))
        Filter.atTop
        (nhds 0) :=
    Eq.mp
      (congrArg
        (fun limit : ℝ =>
          Filter.Tendsto
            (fun n : ℕ =>
              baseNorm * Real.exp (-(rate * ((n : ℝ) + 1) ^ 2)))
            Filter.atTop
            (nhds limit))
        (mul_zero baseNorm))
      hrawLimit
  have hfunctionEquality :
      (fun n : ℕ =>
        baseNorm * Real.exp
          ((((n : ℝ) + 1) ^ 2 / 4) * quadratic)) =
        (fun n : ℕ =>
          baseNorm * Real.exp (-(rate * ((n : ℝ) + 1) ^ 2))) := by
    funext n
    exact congrArg
      (fun value : ℝ => baseNorm * Real.exp value)
      (naturalScale_quadratic_div_four_eq_neg_rate
        quadratic rate hrate n)
  exact Eq.mpr
    (congrArg
      (fun sequence : ℕ → ℝ =>
        Filter.Tendsto sequence Filter.atTop (nhds 0))
      hfunctionEquality)
    hrawZeroLimit

/-- Convergence to zero transports across an explicit equality of real sequences. -/
theorem realSequence_tendsto_zero_of_eq
    (left right : ℕ → ℝ)
    (hequality : left = right)
    (hright :
      Filter.Tendsto right Filter.atTop (nhds 0)) :
    Filter.Tendsto left Filter.atTop (nhds 0) := by
  have hproposition :
      Filter.Tendsto left Filter.atTop (nhds 0) =
        Filter.Tendsto right Filter.atTop (nhds 0) :=
    congrArg
      (fun sequence : ℕ → ℝ =>
        Filter.Tendsto sequence Filter.atTop (nhds 0))
      hequality
  exact Eq.mpr hproposition hright

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary

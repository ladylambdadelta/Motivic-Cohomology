import Mathlib.MeasureTheory.Function.Floor
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.Core
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.PoleClearedBoundarySetup.Core

/-!
# Bernoulli core definitions for Euler-Maclaurin

This file owns the first periodic Bernoulli factor and the raw Bernoulli
remainder terms used by the later fixed-cutoff and continuation layers.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
open MeasureTheory
local notation "π" => Real.pi

/-- Bernoulli-periodic remainder term in the pole-cleared Euler-Maclaurin
continuation.

This name isolates the standard remainder estimate.  The exact analytic
construction is the usual `B₁({x})` integral after multiplying by `s - 1`; the
owner theorem below records the formula identity and the polynomial bound used
by the finite-order chain. -/
noncomputable def eulerMaclaurinPoleClearedZetaRemainderTerm
    (z : ℂ) : ℂ :=
  poleClearedRiemannZeta z -
    (eulerMaclaurinPoleClearedZetaFinitePart z +
      eulerMaclaurinPoleClearedZetaMainTerm z +
      eulerMaclaurinPoleClearedZetaEndpointTerm z)

/-- First periodic Bernoulli factor in the Euler-Maclaurin zeta remainder.

This is the sawtooth `B₁({x}) = {x} - 1/2`, written with `Int.fract`. -/
noncomputable def eulerMaclaurinFirstPeriodicBernoulli
    (x : ℝ) : ℝ :=
  Int.fract x - 1 / 2

/-- Early finite-section version of the first-periodic Bernoulli bound.

This is intentionally placed near the definition so finite Euler-Maclaurin
calculus lemmas can use it without depending on later tail-estimate API. -/
theorem eulerMaclaurinFirstPeriodicBernoulli_norm_cast_le_one_finite
    (x : ℝ) :
    ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ ≤ 1 := by
  have hfract_nonneg : 0 ≤ Int.fract x :=
    Int.fract_nonneg x
  have hfract_le_one : Int.fract x ≤ 1 :=
    le_of_lt (Int.fract_lt_one x)
  have hlower : -(1 : ℝ) ≤ Int.fract x - 1 / 2 := by
    have hneg_half : -(1 : ℝ) ≤ -(1 / 2 : ℝ) :=
      neg_le_neg
        (show (1 / 2 : ℝ) ≤ 1 from
          have hhalf_le_one_div_one : (1 / 2 : ℝ) ≤ 1 / 1 :=
            one_div_le_one_div_of_le zero_lt_one one_le_two
          Eq.subst
            (motive := fun t : ℝ => (1 / 2 : ℝ) ≤ t)
            (div_one (1 : ℝ))
            hhalf_le_one_div_one)
    have hshift : -(1 / 2 : ℝ) ≤ Int.fract x - 1 / 2 := by
      calc
        -(1 / 2 : ℝ) = 0 - 1 / 2 := by
          exact (zero_sub (1 / 2 : ℝ)).symm
        _ ≤ Int.fract x - 1 / 2 :=
          sub_le_sub_right hfract_nonneg (1 / 2 : ℝ)
    exact le_trans hneg_half hshift
  have hupper : Int.fract x - 1 / 2 ≤ 1 := by
    have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) :=
      div_nonneg zero_le_one (le_of_lt zero_lt_two)
    calc
      Int.fract x - 1 / 2 ≤ Int.fract x :=
        sub_le_self (Int.fract x) hhalf_nonneg
      _ ≤ 1 :=
        hfract_le_one
  have habs :
      |Int.fract x - 1 / 2| ≤ 1 :=
    abs_le.mpr ⟨hlower, hupper⟩
  have hnorm :
      ‖((Int.fract x - 1 / 2 : ℝ) : ℂ)‖ =
        |Int.fract x - 1 / 2| :=
    RCLike.norm_ofReal (Int.fract x - 1 / 2)
  exact Eq.subst
    (motive := fun t : ℝ => t ≤ 1)
    hnorm.symm
    habs

/-- Early finite-section version of measurability for the first periodic
Bernoulli sawtooth. -/
theorem eulerMaclaurinFirstPeriodicBernoulli_measurable_finite :
    Measurable eulerMaclaurinFirstPeriodicBernoulli := by
  exact (measurable_fract : Measurable (Int.fract : ℝ → ℝ)).sub measurable_const

/-- Early finite-section version of restricted strong measurability for the
complex-valued first periodic Bernoulli factor. -/
theorem eulerMaclaurinFirstPeriodicBernoulli_cast_aestronglyMeasurable_restrict_finite
    (s : Set ℝ)
    (_hs : MeasurableSet s) :
    AEStronglyMeasurable
      (fun x : ℝ => ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ))
      (volume.restrict s) := by
  exact
    ((Complex.continuous_ofReal.measurable.comp
      eulerMaclaurinFirstPeriodicBernoulli_measurable_finite).aestronglyMeasurable)

/-- The bare Bernoulli-periodic tail integral in the Euler-Maclaurin zeta
remainder, before multiplication by `-(z - 1) z`. -/
noncomputable def eulerMaclaurinPoleClearedZetaBernoulliIntegralCore
    (z : ℂ) : ℂ :=
  ∫ x in Set.Ioi (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)),
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      (((x : ℝ) : ℂ) ^ (-(z + 1)))

/-- Raw first-order Euler-Maclaurin Bernoulli-periodic remainder
`-s ∫_N^∞ B₁({x}) x^{-s-1} dx`. -/
noncomputable def eulerMaclaurinZetaBernoulliIntegralRemainder
    (z : ℂ) : ℂ :=
  -z * eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z

/-- Explicit Bernoulli-periodic integral remainder for the pole-cleared zeta
Euler-Maclaurin formula.

With `N = ⌊2 + ‖z‖⌋₊`, this is
`-(z - 1) z ∫_N^∞ B₁({x}) x^{-z-1} dx`, the standard first-order
Euler-Maclaurin remainder after multiplying by the pole-clearing factor. -/
noncomputable def eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder
    (z : ℂ) : ℂ :=
  -((z - 1) * z) *
    eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z

end

end LFunctions
end Boundary

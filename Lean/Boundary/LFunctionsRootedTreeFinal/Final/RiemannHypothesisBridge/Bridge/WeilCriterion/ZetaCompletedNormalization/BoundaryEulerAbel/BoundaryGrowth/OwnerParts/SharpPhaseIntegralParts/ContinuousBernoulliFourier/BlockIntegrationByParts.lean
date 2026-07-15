import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.SharpPhaseIntegralParts.ContinuousBernoulliFourier.QuadraticPrimitive
import Mathlib.MeasureTheory.Integral.FundThmCalculus

/-!
# Unit-block Bernoulli integration by parts

This file owns the exact integration-by-parts identity converting a first
Bernoulli factor into the zero-endpoint quadratic primitive.  It is stated for
an arbitrary complex phase so the logarithmic-phase specialization remains a
thin downstream application.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

/-- The complexification of the zero-endpoint quadratic Bernoulli primitive. -/
noncomputable def eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitiveComplex
    (u : ℝ) : ℂ :=
  (eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive u : ℂ)

/-- The complexified quadratic primitive has the expected affine derivative. -/
theorem hasDerivAt_eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitiveComplex
    (u : ℝ) :
    HasDerivAt
      eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitiveComplex
      ((u - 1 / 2 : ℝ) : ℂ)
      u := by
  have hreal :=
    hasDerivAt_eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive u
  exact hreal.ofReal_comp

/-- The complex affine Bernoulli coordinate is interval integrable on the
unit interval. -/
theorem eulerMaclaurinFirstPeriodicBernoulliAffineComplex_intervalIntegrable :
    IntervalIntegrable
      (fun u : ℝ => ((u - 1 / 2 : ℝ) : ℂ))
      volume
      0
      1 := by
  have haffine_real : Continuous (fun u : ℝ => u - 1 / 2) :=
    continuous_id.sub continuous_const
  have haffine_complex :
      Continuous (fun u : ℝ => ((u - 1 / 2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp haffine_real
  exact haffine_complex.intervalIntegrable 0 1

/-- Exact unit-block integration by parts with the zero-endpoint Bernoulli
primitive.  No boundary simplification is hidden in this theorem. -/
theorem eulerMaclaurinFirstPeriodicBernoulli_unitBlock_integrationByParts
    (phase phaseDerivative : ℝ → ℂ)
    (hphase :
      ∀ u ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt phase (phaseDerivative u) u)
    (hphaseDerivative :
      IntervalIntegrable phaseDerivative volume 0 1) :
    (∫ u in (0 : ℝ)..1,
        phase u * ((u - 1 / 2 : ℝ) : ℂ)) =
      phase 1 *
          eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitiveComplex 1 -
        phase 0 *
          eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitiveComplex 0 -
        ∫ u in (0 : ℝ)..1,
          phaseDerivative u *
            eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitiveComplex u := by
  have hprimitive :
      ∀ u ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt
          eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitiveComplex
          ((u - 1 / 2 : ℝ) : ℂ)
          u :=
    fun u _hu =>
      hasDerivAt_eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitiveComplex u
  exact intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hphase
    hprimitive
    hphaseDerivative
    eulerMaclaurinFirstPeriodicBernoulliAffineComplex_intervalIntegrable

/-- Because the chosen primitive vanishes at both unit endpoints, the generic
integration-by-parts identity has no block boundary term. -/
theorem eulerMaclaurinFirstPeriodicBernoulli_unitBlock_integrationByParts_zeroBoundary
    (phase phaseDerivative : ℝ → ℂ)
    (hphase :
      ∀ u ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt phase (phaseDerivative u) u)
    (hphaseDerivative :
      IntervalIntegrable phaseDerivative volume 0 1) :
    (∫ u in (0 : ℝ)..1,
        phase u * ((u - 1 / 2 : ℝ) : ℂ)) =
      -∫ u in (0 : ℝ)..1,
        phaseDerivative u *
          eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitiveComplex u := by
  have hibp :=
    eulerMaclaurinFirstPeriodicBernoulli_unitBlock_integrationByParts
      phase phaseDerivative hphase hphaseDerivative
  have hprimitive_one :
      eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitiveComplex 1 = 0 := by
    have hreal :
        eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive 1 = 0 := by
      exact eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive_one
    exact Complex.ofReal_eq_zero.mpr hreal
  have hprimitive_zero :
      eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitiveComplex 0 = 0 := by
    have hreal :
        eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive 0 = 0 := by
      exact eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive_zero
    exact Complex.ofReal_eq_zero.mpr hreal
  have hboundary_one :
      phase 1 *
          eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitiveComplex 1 =
        0 :=
    Eq.trans
      (congrArg (fun z : ℂ => phase 1 * z) hprimitive_one)
      (mul_zero (phase 1))
  have hboundary_zero :
      phase 0 *
          eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitiveComplex 0 =
        0 :=
    Eq.trans
      (congrArg (fun z : ℂ => phase 0 * z) hprimitive_zero)
      (mul_zero (phase 0))
  calc
    (∫ u in (0 : ℝ)..1,
        phase u * ((u - 1 / 2 : ℝ) : ℂ)) =
        phase 1 *
            eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitiveComplex 1 -
          phase 0 *
            eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitiveComplex 0 -
          ∫ u in (0 : ℝ)..1,
            phaseDerivative u *
              eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitiveComplex u :=
      hibp
    _ = 0 - 0 -
          ∫ u in (0 : ℝ)..1,
            phaseDerivative u *
              eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitiveComplex u :=
      congrArg₂ Sub.sub
        (congrArg₂ Sub.sub hboundary_one hboundary_zero)
        rfl
    _ = -∫ u in (0 : ℝ)..1,
          phaseDerivative u *
            eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitiveComplex u := by
      exact Eq.trans (congrArg (fun z : ℂ => z -
        ∫ u in (0 : ℝ)..1,
          phaseDerivative u *
            eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitiveComplex u)
        (sub_self 0)) (zero_sub _)

end
end LFunctions
end Boundary

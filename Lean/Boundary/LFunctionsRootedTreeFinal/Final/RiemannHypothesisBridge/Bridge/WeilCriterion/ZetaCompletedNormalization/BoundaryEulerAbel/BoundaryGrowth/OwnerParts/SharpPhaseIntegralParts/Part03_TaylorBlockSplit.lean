import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.SharpPhaseIntegralParts.Part02_TaylorBlockIntegrability

/-!
# Boundary growth sharp phase integral: finite Taylor split

This file is a semantic split of `BoundaryGrowth.OwnerParts.Part08_SharpPhaseIntegral`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- Exact finite split of the Bernoulli-weighted phase-increment block sum into
its Taylor-linear and nonlinear Taylor-remainder pieces.

The local integral split carries the integrability work; this theorem is only
the finite summation assembly. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementBlockSum_eq_linearBlockSum_add_remainderBlockSum
    (t : ℝ)
    {K : ℕ} :
    (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K,
      ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I))))) =
      boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementLinearBlockSum t K +
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementRemainderBlockSum t K := by
  have hlocal :
      ∀ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K,
        (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I))))) =
          (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              boundaryLineOnePointRealParam_phaseIncrementLinearIntegrand t n x) +
            (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                boundaryLineOnePointRealParam_phaseIncrementRemainderIntegrand t n x) := by
    intro n hn
    exact
      boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementIntegral_eq_linear_integral_add_remainder_integral
        t hn
  have hsum :
      (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I))))) =
        (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              boundaryLineOnePointRealParam_phaseIncrementLinearIntegrand t n x) +
          (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K,
            ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                boundaryLineOnePointRealParam_phaseIncrementRemainderIntegrand t n x) := by
    exact Eq.trans
      (Finset.sum_congr rfl hlocal)
      Finset.sum_add_distrib
  exact hsum

end
end LFunctions
end Boundary

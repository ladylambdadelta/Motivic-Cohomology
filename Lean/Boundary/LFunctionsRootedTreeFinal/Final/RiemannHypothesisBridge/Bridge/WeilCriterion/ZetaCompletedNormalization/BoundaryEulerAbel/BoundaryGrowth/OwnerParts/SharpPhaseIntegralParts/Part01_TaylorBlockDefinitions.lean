import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.Part07_PostCutoffDefect

/-!
# Boundary growth sharp phase integral: Taylor block definitions

This file is a semantic split of `BoundaryGrowth.OwnerParts.Part08_SharpPhaseIntegral`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- The Taylor-linear part of the finite Bernoulli-weighted phase-increment
block sum after the canonical cutoff. -/
noncomputable def boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementLinearBlockSum
    (t : ℝ) (K : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K,
    ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        (((((-(t : ℂ) * Complex.I) /
              (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I))) *
            ((x : ℂ) -
              (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ))))

/-- The nonlinear Taylor-remainder part of the finite Bernoulli-weighted
phase-increment block sum after the canonical cutoff. -/
noncomputable def boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementRemainderBlockSum
    (t : ℝ) (K : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K,
    ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I) -
          ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I)) -
          ((((-(t : ℂ) * Complex.I) /
              (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I))) *
            ((x : ℂ) -
              (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ))))

end LFunctions
end Boundary

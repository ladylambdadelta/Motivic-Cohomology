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

/-- The Taylor-linear logarithmic-phase increment on the unit block ending at
`n`. -/
noncomputable def boundaryLineOnePointRealParam_phaseIncrementLinearIntegrand
    (t : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  let a : ℂ := (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)
  let leftPhase : ℂ := a ^ (-(t : ℂ) * Complex.I)
  ((-(t : ℂ) * Complex.I) / a) * leftPhase * ((x : ℂ) - a)

/-- The nonlinear remainder after subtracting the left-endpoint value and its
Taylor-linear increment. -/
noncomputable def boundaryLineOnePointRealParam_phaseIncrementRemainderIntegrand
    (t : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  let a : ℂ := (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)
  let phase : ℂ := ((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)
  let leftPhase : ℂ := a ^ (-(t : ℂ) * Complex.I)
  let linear : ℂ :=
    boundaryLineOnePointRealParam_phaseIncrementLinearIntegrand t n x
  (phase - leftPhase) - linear

/-- The Taylor-linear part of the finite Bernoulli-weighted phase-increment
block sum after the canonical cutoff. -/
noncomputable def boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementLinearBlockSum
    (t : ℝ) (K : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K,
    ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        boundaryLineOnePointRealParam_phaseIncrementLinearIntegrand t n x

/-- The nonlinear Taylor-remainder part of the finite Bernoulli-weighted
phase-increment block sum after the canonical cutoff. -/
noncomputable def boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementRemainderBlockSum
    (t : ℝ) (K : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K,
    ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        boundaryLineOnePointRealParam_phaseIncrementRemainderIntegrand t n x

end
end LFunctions
end Boundary

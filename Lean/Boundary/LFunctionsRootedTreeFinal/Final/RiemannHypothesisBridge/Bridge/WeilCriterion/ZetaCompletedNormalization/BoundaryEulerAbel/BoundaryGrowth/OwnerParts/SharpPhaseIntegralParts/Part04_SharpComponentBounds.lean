import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.SharpPhaseIntegralParts.ContinuousBernoulliVdc

/-!
# Boundary growth sharp phase integral: sharp component bounds

This file is a semantic split of `BoundaryGrowth.OwnerParts.Part08_SharpPhaseIntegral`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- Combined sharp finite zero-mean Dirichlet estimate for the Bernoulli-weighted
global phase integral after the canonical cutoff.

This is the true analytic sink in the sharp phase-integral layer.  The estimate
uses cancellation of the combined Taylor-linear and nonlinear Taylor-remainder
pieces after the one-interval Bernoulli zero-mean subtraction; the two pieces are
not separately owned by artificial half-bounds. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_globalPhaseIntegral_norm_le_sharp_ownerDirichlet_core
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {K : ℕ}
    (hK : ⌊2 + ‖t‖⌋₊ ≤ K) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((K : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      Real.sqrt (1 + ‖t‖) * Real.log (2 + K) := by
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_continuousVdc_postCutoff
      t ht hK

/-- Combined sharp finite zero-mean Dirichlet estimate for the Bernoulli-weighted
phase-increment block sum.

The finite block sum is transported to the single global Bernoulli phase integral
using the already proved one-interval zero-mean cancellation theorem. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementBlockSum_norm_le_sharp_ownerDirichlet_core
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {K : ℕ}
    (hK : ⌊2 + ‖t‖⌋₊ ≤ K) :
    ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K,
      ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I))))‖ ≤
      Real.sqrt (1 + ‖t‖) * Real.log (2 + K) := by
  have hglobal :
      ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((K : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
        Real.sqrt (1 + ‖t‖) * Real.log (2 + K) :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_globalPhaseIntegral_norm_le_sharp_ownerDirichlet_core
      t ht hK
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        ‖z‖ ≤ Real.sqrt (1 + ‖t‖) * Real.log (2 + K))
      (boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementBlockSum_eq_globalPhaseIntegral
        t).symm
      hglobal

/-- Public assembly of the sharp finite zero-mean block estimate.

The Taylor split remains available for downstream transport, but the sharp
Dirichlet cancellation is owned by the combined zero-mean theorem above rather
than by separate absolute estimates for the Taylor pieces. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementBlockSum_norm_le_sharp_of_linear_and_remainder
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {K : ℕ}
    (hK : ⌊2 + ‖t‖⌋₊ ≤ K) :
    ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K,
      ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I))))‖ ≤
      Real.sqrt (1 + ‖t‖) * Real.log (2 + K) := by
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementBlockSum_norm_le_sharp_ownerDirichlet_core
      t ht hK

end
end LFunctions
end Boundary

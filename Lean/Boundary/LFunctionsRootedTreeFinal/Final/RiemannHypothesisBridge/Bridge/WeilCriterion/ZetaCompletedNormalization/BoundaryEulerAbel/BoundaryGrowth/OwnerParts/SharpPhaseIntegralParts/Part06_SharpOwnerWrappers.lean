import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.SharpPhaseIntegralParts.Part05_GlobalSharpTransport

/-!
# Boundary growth sharp phase integral: owner wrappers

This file is a semantic split of `BoundaryGrowth.OwnerParts.Part08_SharpPhaseIntegral`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- Resonance-safe sharp estimate for the global Bernoulli-weighted logarithmic
phase integral after the canonical cutoff.

This is the analytic owner statement behind the Taylor-linear/remainder block
surface below.  The proof is by the bounded-variation Dirichlet argument for
`B₁(x) x^{-it}` on the post-cutoff interval, not by separate absolute bounds
for the linear and nonlinear Taylor pieces. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_globalPhaseIntegral_single_sharp_core
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {K : ℕ}
    (hK : ⌊2 + ‖t‖⌋₊ ≤ K) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((K : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      Real.sqrt (1 + ‖t‖) * Real.log (2 + K) := by
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_globalPhaseIntegral_single_sharp_ownerDirichlet
      t ht hK

/-- Sharp estimate for the combined Taylor-linear and nonlinear remainder block
sum after the canonical cutoff.

The Taylor split identifies the two displayed pieces; the sharp cancellation
is owned by the finite zero-mean Dirichlet estimate above. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementLinear_add_remainderBlockSum_norm_le_sharp_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {K : ℕ}
    (hK : ⌊2 + ‖t‖⌋₊ ≤ K) :
    ‖boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementLinearBlockSum
        t K +
      boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementRemainderBlockSum
        t K‖ ≤
      Real.sqrt (1 + ‖t‖) * Real.log (2 + K) := by
  let L : ℂ :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementLinearBlockSum
      t K
  let R : ℂ :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementRemainderBlockSum
      t K
  let B : ℝ := Real.sqrt (1 + ‖t‖) * Real.log (2 + K)
  let S : ℂ :=
    ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K,
      ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I))))
  have hS :
      ‖S‖ ≤ B :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementBlockSum_norm_le_sharp_ownerDirichlet
      t ht hK
  have hsplit :
      S = L + R :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementBlockSum_eq_linearBlockSum_add_remainderBlockSum
      t
  exact
    Eq.subst
      (motive := fun z : ℂ => ‖z‖ ≤ B)
      hsplit
      hS

/-- Assembly of the finite phase-increment estimate from the Taylor-linear and
nonlinear Taylor-remainder block estimates. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementBlockSum_norm_le_sharp_of_linear_remainder
    (t : ℝ)
    {K : ℕ}
    (hcombined :
      ‖boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementLinearBlockSum
          t K +
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementRemainderBlockSum
          t K‖ ≤
        Real.sqrt (1 + ‖t‖) * Real.log (2 + K)) :
    ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K,
      ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I))))‖ ≤
      Real.sqrt (1 + ‖t‖) * Real.log (2 + K) := by
  let L : ℂ :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementLinearBlockSum
      t K
  let R : ℂ :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementRemainderBlockSum
      t K
  let B : ℝ := Real.sqrt (1 + ‖t‖) * Real.log (2 + K)
  have hsplit :
      (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I))))) =
        L + R :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementBlockSum_eq_linearBlockSum_add_remainderBlockSum
      t
  exact
    Eq.subst
      (motive := fun z : ℂ => ‖z‖ ≤ B)
      hsplit.symm
      hcombined

/-- Sharp terminal estimate for the global Bernoulli-weighted logarithmic
phase integral after the canonical cutoff. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementBlockSum_norm_le_sharp_ownerGap
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
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementBlockSum_norm_le_sharp_ownerDirichlet
      t ht hK

/-- Transport from the finite zero-mean phase-increment block estimate to the
global Bernoulli-weighted logarithmic phase integral. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_globalPhaseIntegral_single_sharp_of_phaseIncrementBlockSum
    (t : ℝ)
    {K : ℕ}
    (hphase :
      ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I))))‖ ≤
        Real.sqrt (1 + ‖t‖) * Real.log (2 + K)) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((K : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      Real.sqrt (1 + ‖t‖) * Real.log (2 + K) := by
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        ‖z‖ ≤ Real.sqrt (1 + ‖t‖) * Real.log (2 + K))
      (boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementBlockSum_eq_globalPhaseIntegral
        t)
      hphase

/-- Sharp terminal estimate for the global Bernoulli-weighted logarithmic
phase integral after the canonical cutoff. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_globalPhaseIntegral_single_sharp_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {K : ℕ}
    (hK : ⌊2 + ‖t‖⌋₊ ≤ K) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((K : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      Real.sqrt (1 + ‖t‖) * Real.log (2 + K) := by
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_globalPhaseIntegral_single_sharp_ownerDirichlet
      t ht hK

/-- Sharp terminal-family estimate for the global Bernoulli-weighted
logarithmic phase integral after the canonical cutoff. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_globalPhaseIntegral_family_sharp_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∀ K : ℕ,
      ⌊2 + ‖t‖⌋₊ ≤ K →
      K ≤ M →
        ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((K : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
          Real.sqrt (1 + ‖t‖) * Real.log (2 + K) := by
  intro K hK hKM
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_globalPhaseIntegral_single_sharp_ownerGap
      t ht hK

end
end LFunctions
end Boundary

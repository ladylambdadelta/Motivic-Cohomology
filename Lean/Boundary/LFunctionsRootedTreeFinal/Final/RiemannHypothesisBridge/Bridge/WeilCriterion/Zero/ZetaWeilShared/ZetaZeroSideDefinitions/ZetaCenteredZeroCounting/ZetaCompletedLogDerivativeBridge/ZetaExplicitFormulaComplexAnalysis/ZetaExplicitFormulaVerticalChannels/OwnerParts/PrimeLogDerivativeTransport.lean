import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeVerticalAnalyticEstimates
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeLeftReflectedCompletedValue
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.InverseGammaScheduledNormalization
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.InverseGammaOneSidedValues

/-!
# Prime vertical-channel transport estimate

This file owns the analytic estimate that the scheduled prime logarithmic-
derivative vertical-channel remainder vanishes.  The projection layer consumes
this theorem but does not own its proof.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open LSeries ArithmeticFunction
open MeasureTheory
open scoped ArithmeticFunction
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Algebraic extraction of the prime vertical-channel limit from its two
canonical analytic sub-estimates.

The right face is first normalized to the von Mangoldt Dirichlet-series
integral; the left face is an off-critical transport tail.  This lemma contains
only the finite-height channel identity and `Tendsto` subtraction. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_of_rightVonMangoldt_and_leftPrime
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hright :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            L ↗Λ
                (zetaCompletedExplicitFormulaRightPath
                  (F.rectangle (h.height_schedule.height u)) t) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaRightPath
                  (F.rectangle (h.height_schedule.height u)) t - 1 / 2))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)))
    (hleft :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            explicitFormulaPrimeLogDerivative
                (zetaCompletedExplicitFormulaLeftPath
                  (F.rectangle (h.height_schedule.height u)) t) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaLeftPath
                  (F.rectangle (h.height_schedule.height u)) t - 1 / 2))
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  let P : ℂ := zetaCompletedExplicitFormulaPrimeContribution f
  have hsub :
      Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            L ↗Λ
                (zetaCompletedExplicitFormulaRightPath
                  (F.rectangle (h.height_schedule.height u)) t) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaRightPath
                  (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) -
            ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            explicitFormulaPrimeLogDerivative
                (zetaCompletedExplicitFormulaLeftPath
                  (F.rectangle (h.height_schedule.height u)) t) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaLeftPath
                  (F.rectangle (h.height_schedule.height u)) t - 1 / 2))
        atTop
        (𝓝 (P - 0)) :=
    hright.sub hleft
  have htarget : P - 0 = P := by
    exact sub_zero P
  have hchannel_fun :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel
          f F (h.height_schedule.height u)) =
      (fun u : ℝ =>
        (∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          L ↗Λ
              (zetaCompletedExplicitFormulaRightPath
                (F.rectangle (h.height_schedule.height u)) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath
                (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) -
          ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          explicitFormulaPrimeLogDerivative
              (zetaCompletedExplicitFormulaLeftPath
                (F.rectangle (h.height_schedule.height u)) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath
                (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) := by
    funext u
    exact
      zetaCompletedExplicitFormulaPrimeVerticalChannel_eq_rightVonMangoldtIntegral_sub_left
        f F (h.height_schedule.height u)
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 P))
    hchannel_fun.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            (∫ t in Set.Icc
                (-(F.rectangle (h.height_schedule.height u)).T)
                (F.rectangle (h.height_schedule.height u)).T,
              L ↗Λ
                  (zetaCompletedExplicitFormulaRightPath
                    (F.rectangle (h.height_schedule.height u)) t) *
                zetaCompletedExplicitFormulaPhi f
                  (zetaCompletedExplicitFormulaRightPath
                    (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) -
              ∫ t in Set.Icc
                (-(F.rectangle (h.height_schedule.height u)).T)
                (F.rectangle (h.height_schedule.height u)).T,
              explicitFormulaPrimeLogDerivative
                  (zetaCompletedExplicitFormulaLeftPath
                    (F.rectangle (h.height_schedule.height u)) t) *
                zetaCompletedExplicitFormulaPhi f
                  (zetaCompletedExplicitFormulaLeftPath
                    (F.rectangle (h.height_schedule.height u)) t - 1 / 2))
          atTop
          (𝓝 z))
      htarget
      hsub)

/-- Algebraic extraction of the prime vertical-channel limit from the named
scheduled right von Mangoldt integral and named left prime tail. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_of_scheduledRightVonMangoldt_and_scheduledLeftPrime
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hright :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral
            f F h u)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)))
    (hleft :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
            f F h u)
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  let P : ℂ := zetaCompletedExplicitFormulaPrimeContribution f
  have hsub :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral
              f F h u -
            zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
              f F h u)
        atTop
        (𝓝 (P - 0)) :=
    hright.sub hleft
  have htarget : P - 0 = P :=
    sub_zero P
  have hchannel_fun :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel
          f F (h.height_schedule.height u)) =
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral
            f F h u -
          zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
            f F h u) := by
    funext u
    exact
      zetaCompletedExplicitFormulaPrimeVerticalChannel_eq_scheduledRightVonMangoldt_sub_scheduledLeft
        f F h u
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 P))
    hchannel_fun.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral
                f F h u -
              zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
                f F h u)
          atTop
          (𝓝 z))
      htarget
      hsub)

/-- Algebraic extraction of the scheduled right von Mangoldt limit from the
prime vertical-channel limit and the scheduled left prime-tail limit.

This is the reverse assembly direction used after the contour-level prime
channel has been proved independently: the finite-height identity
`prime = right - left` gives `right = prime + left`, so the right scheduled
von Mangoldt integral inherits the prime contribution value. -/
theorem zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral_tendsto_of_primeChannel_and_scheduledLeftPrime
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hprime :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeVerticalChannel
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)))
    (hleft :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
            f F h u)
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral
          f F h u)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  let P : ℂ := zetaCompletedExplicitFormulaPrimeContribution f
  have hsum :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeVerticalChannel
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
              f F h u)
        atTop
        (𝓝 (P + 0)) :=
    hprime.add hleft
  have htarget : P + 0 = P :=
    add_zero P
  have hright_fun :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral
          f F h u) =
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel
            f F (h.height_schedule.height u) +
          zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
            f F h u) := by
    funext u
    let R : ℂ :=
      zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral
        f F h u
    let L : ℂ :=
      zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
        f F h u
    let C : ℂ :=
      zetaCompletedExplicitFormulaPrimeVerticalChannel
        f F (h.height_schedule.height u)
    have hdecomp : C = R - L :=
      zetaCompletedExplicitFormulaPrimeVerticalChannel_eq_scheduledRightVonMangoldt_sub_scheduledLeft
        f F h u
    change R = C + L
    calc
      R = (R - L) + L := by
        exact (sub_add_cancel R L).symm
      _ = C + L := by
        exact congrArg (fun z : ℂ => z + L) hdecomp.symm
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 P))
    hright_fun.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaPrimeVerticalChannel
                f F (h.height_schedule.height u) +
              zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
                f F h u)
          atTop
          (𝓝 z))
      htarget
      hsum)

/-- Algebraic extraction of the scheduled left prime-tail limit from the prime
vertical-channel limit and the scheduled right von Mangoldt limit.

This is the companion to
`zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral_tendsto_of_primeChannel_and_scheduledLeftPrime`.
The finite-height identity `prime = right - left` is rewritten as
`left = right - prime`; no analytic input is introduced here. -/
theorem zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral_tendsto_of_scheduledRightVonMangoldt_and_primeChannel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (R P : ℂ)
    (hright :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral
            f F h u)
        atTop
        (𝓝 R))
    (hprime :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeVerticalChannel
            f F (h.height_schedule.height u))
        atTop
        (𝓝 P)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
          f F h u)
      atTop
      (𝓝 (R - P)) := by
  have hsub :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral
              f F h u -
            zetaCompletedExplicitFormulaPrimeVerticalChannel
              f F (h.height_schedule.height u))
        atTop
        (𝓝 (R - P)) :=
    hright.sub hprime
  have hleft_fun :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
          f F h u) =
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral
            f F h u -
          zetaCompletedExplicitFormulaPrimeVerticalChannel
            f F (h.height_schedule.height u)) := by
    funext u
    let R_u : ℂ :=
      zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral
        f F h u
    let L_u : ℂ :=
      zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
        f F h u
    let P_u : ℂ :=
      zetaCompletedExplicitFormulaPrimeVerticalChannel
        f F (h.height_schedule.height u)
    have hdecomp : P_u = R_u - L_u :=
      zetaCompletedExplicitFormulaPrimeVerticalChannel_eq_scheduledRightVonMangoldt_sub_scheduledLeft
        f F h u
    change L_u = R_u - P_u
    calc
      L_u = R_u - (R_u - L_u) := by
        exact (sub_sub_self R_u L_u).symm
      _ = R_u - P_u := by
        exact congrArg (fun z : ℂ => R_u - z) hdecomp.symm
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 (R - P)))
      hleft_fun.symm
      hsub

/-- Algebraic extraction of the prime vertical-channel limit when the left
scheduled logarithmic-derivative integral carries the negative of a
complementary contribution.

This is the honest recombination shape for a `right - left` finite-height
channel: if the right scheduled integral tends to `R`, the left scheduled
integral tends to `-C`, and `R + C` is the public prime contribution, then the
concrete prime vertical channel tends to the public contribution. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_of_scheduledRight_and_negativeComplementLeft
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (R C : ℂ)
    (hrecombine : R + C = zetaCompletedExplicitFormulaPrimeContribution f)
    (hright :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral
            f F h u)
        atTop
        (𝓝 R))
    (hleft :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
            f F h u)
        atTop
        (𝓝 (-C))) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  let P : ℂ := zetaCompletedExplicitFormulaPrimeContribution f
  have hsub :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral
            f F h u -
            zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
              f F h u)
        atTop
        (𝓝 (R - (-C))) :=
    hright.sub hleft
  have hlimit_add : R - (-C) = R + C := by
    calc
      R - (-C) = R + -(-C) := by
        exact sub_eq_add_neg R (-C)
      _ = R + C := by
        exact congrArg (fun z : ℂ => R + z) (neg_neg C)
  have hlimit_prime : R - (-C) = P :=
    Eq.trans hlimit_add hrecombine
  have hchannel_fun :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel
          f F (h.height_schedule.height u)) =
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral
          f F h u -
          zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
            f F h u) := by
    funext u
    exact
      zetaCompletedExplicitFormulaPrimeVerticalChannel_eq_scheduledRightVonMangoldt_sub_scheduledLeft
        f F h u
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 P))
      hchannel_fun.symm
      (Eq.subst
        (motive := fun z : ℂ =>
          Tendsto
            (fun u : ℝ =>
              zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral
                f F h u -
                zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
                  f F h u)
            atTop
            (𝓝 z))
        hlimit_prime
        hsub)

/-- Prime vertical-channel convergence from the proved right one-sided
von Mangoldt inversion and a reflected/complement left-channel limit.

The only analytic input here is the left scheduled logarithmic-derivative
limit to the negative complementary natural contribution.  The right
one-sided limit and the arithmetic recombination with the complement are
already owned upstream. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_of_negativeComplementLeft
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hleft :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
            f F h u)
        atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f)))) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  have hright :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral
            f F h u)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f)) :=
    explicitFormulaScheduledScalar_tendsto_of_forall_eq
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral
          f F h u)
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t)
      (zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f)
      (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernelIntegral_tendsto_primeNaturalOneSidedContribution_direct_ownerInversion
        f F h)
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral_eq_affineKernelIntegral
          f F h u)
  have hrecombine :
      zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f +
          zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f =
        zetaCompletedExplicitFormulaPrimeContribution f :=
    zetaCompletedExplicitFormulaPrimeNaturalOneSided_add_complementContribution_eq_primeContribution
      f
  exact
    zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_of_scheduledRight_and_negativeComplementLeft
      f F h
      (zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f)
      (zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f)
      hrecombine hright hleft

/-- Prime vertical-channel convergence from reflected completed and
inverse-Gamma component values, using scheduled-window assembly directly.

This avoids routing through a separate whole-line value for the unsplit left
logarithmic-derivative kernel.  The analytic content is exactly the two
component values and the factor-bound data needed to exhaust their scheduled
windows. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_of_reflectedCompleted_and_inverseGamma_values_factor_bound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (B : ℝ)
    (hB_nonneg : 0 ≤ B)
    (hfactor_meas :
      AEStronglyMeasurable
        (fun t : ℝ =>
          - completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaRightAffineLine F (-t)))
        (volume : Measure ℝ))
    (hleft_bound :
      ∀ t : ℝ,
        ‖completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          B * (1 + ‖t‖))
    (V G : ℂ)
    (hreflected_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F t) = V)
    (hinverse_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t) = G)
    (hcomponent :
      V - G =
        -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  have hleft :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
            f F h u)
        atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f))) :=
    zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral_tendsto_neg_complement_of_reflectedCompleted_and_inverseGamma_values_factor_bound
      f F h hregular hcoh B hB_nonneg hfactor_meas hleft_bound
      V G hreflected_value hinverse_value hcomponent
  exact
    zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_of_negativeComplementLeft
      f F h hleft

/-- Prime vertical-channel convergence from a whole-line left affine-kernel
value equal to the negative complementary natural prime contribution.

This is the owner-level shape expected from the missing left/reflected contour
proof when the complement is carried by the left logarithmic-derivative side. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_of_leftIntegral_eq_negativeComplement
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (E : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ E.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖))
    (hleft_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) =
        -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  have hleft :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
            f F h u)
        atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f))) :=
    zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral_tendsto_of_integral_eq
      f F h hregular E hline_mem BG hBG_nonneg hinverseGamma_bound
      (-(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f))
      hleft_value
  exact
    zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_of_negativeComplementLeft
      f F h hleft

/-- Prime vertical-channel convergence from reflected-left component values.

This is the non-circular assembly shape for the remaining prime proof.  The
analytic work is reduced to the reflected completed component and the left
inverse-Gamma component; this theorem only combines those values with the
existing left-kernel exhaustion and the arithmetic prime recombination. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_of_reflectedLeftComponentValues
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (E : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ E.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖))
    (hreflected :
      Integrable
        (zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F)
        (volume : Measure ℝ))
    (hinverse :
      Integrable
        (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F)
        (volume : Measure ℝ))
    (V G : ℂ)
    (hreflected_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F t) = V)
    (hinverse_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t) = G)
    (hcomponent :
      V - G =
        -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  have hleft_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) =
        -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) :=
    zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_integral_eq_negativeComplement_of_reflectedCompleted_and_inverseGamma_values
      f F hreflected hinverse V G hreflected_value hinverse_value hcomponent
  exact
    zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_of_leftIntegral_eq_negativeComplement
      f F h hregular E hline_mem BG hBG_nonneg hinverseGamma_bound
      hleft_value

/-- Vertically regular form of the reflected-left component-value assembly for
the prime channel.

This wrapper supplies the zero-excised carrier data, the completed
log-derivative bound, and the inverse-Gamma integrability from the vertically
regular contour package.  The only remaining analytic inputs are the two
whole-line component values and their arithmetic difference. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_of_verticallyRegular_reflectedLeftComponentValues
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (V G : ℂ)
    (hreflected_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F.toContourFamily t) = V)
    (hinverse_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
          f F.toContourFamily t) = G)
    (hcomponent :
      V - G =
        -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel
          f F.toContourFamily (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  let E : CompletedZetaZeroExcisedStrip
      (1 - F.toContourFamily.c) (1 - F.toContourFamily.c) :=
    zetaCompletedExplicitFormulaLeftAffineLineZeroExcisedStrip_of_verticallyRegular
      F
  have hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F.toContourFamily t ∈
          E.carrier :=
    zetaCompletedExplicitFormulaLeftAffineLine_mem_zeroExcisedStrip_of_verticallyRegular
      F
  have hregular :
      zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
        F.toContourFamily :=
    zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
      F
  match
    zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_gammaBinetCoherence_owner
      F.toContourFamily hregular hcoh with
  | ⟨BG, hBG_nonneg, hinverseGamma_bound⟩ =>
      have hreflected :
          Integrable
            (zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
              f F.toContourFamily)
            (volume : Measure ℝ) :=
        zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integrable_of_verticallyRegular
          f F h
      have hinverse :
          Integrable
            (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
              f F.toContourFamily)
            (volume : Measure ℝ) :=
        zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_integrable
          f F.toContourFamily h hregular hcoh
      exact
        zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_of_reflectedLeftComponentValues
          f F.toContourFamily h hregular E hline_mem
          BG hBG_nonneg hinverseGamma_bound hreflected hinverse
          V G hreflected_value hinverse_value hcomponent

/-- Vertically regular prime-channel assembly from a reflected completed value
and a right inverse-Gamma value.

The inverse-Gamma owner normalization supplies the left inverse-Gamma value
from the right value and the completed archimedean-plus-correction difference
normalization.  This theorem therefore leaves only the reflected completed
value, the right inverse-Gamma value, and their arithmetic recombination as
inputs for the prime complement branch. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_of_verticallyRegular_reflectedLeft_and_rightInverseGamma_values
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (V R : ℂ)
    (hreflected_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F.toContourFamily t) = V)
    (hright_inverse_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
          f F.toContourFamily t) = R)
    (hcomponent :
      V -
          (R -
            (zetaCompletedExplicitFormulaArchimedeanContribution f +
              zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) =
        -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel
          f F.toContourFamily (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  have hinverse_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
          f F.toContourFamily t) =
        R -
          (zetaCompletedExplicitFormulaArchimedeanContribution f +
            zetaCompletedExplicitFormulaCorrectionStandardContourContribution f) :=
    zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_integral_eq_rightValue_sub_archimedean_add_correction_of_verticallyRegular_gammaBinet
      f F h hcoh R hright_inverse_value
  exact
    zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_of_verticallyRegular_reflectedLeftComponentValues
      f F h hcoh V
      (R -
        (zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f))
      hreflected_value hinverse_value hcomponent

/-- Vertically regular prime-channel assembly from a reflected completed value
and the one-sided left inverse-Gamma owner value.

This is the non-circular consumer of `InverseGammaOneSidedValues` for the
prime complement branch.  It avoids deriving the left inverse-Gamma component
from the right-minus-left inverse-Gamma normalization, so the remaining prime
analytic input is the reflected completed value and its scalar recombination
with the one-sided inverse-Gamma value. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_of_verticallyRegular_reflectedLeft_and_leftOneSidedInverseGammaValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (V : ℂ)
    (hreflected_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F.toContourFamily t) = V)
    (hcomponent :
      V -
          (-(zetaCompletedExplicitFormulaPhi f 0) +
            (((2 * (Real.pi : ℂ) * Complex.I) *
              (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I)) =
        -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel
          f F.toContourFamily (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  have hinverse_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
          f F.toContourFamily t) =
        -(zetaCompletedExplicitFormulaPhi f 0) +
          (((2 * (Real.pi : ℂ) * Complex.I) *
            (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I) :=
    zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_integral_eq_negPhiZero_add_correctionLeftValue_ownerOneSidedValues
      f F h hcoh
  exact
    zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_of_verticallyRegular_reflectedLeftComponentValues
      f F h hcoh V
      (-(zetaCompletedExplicitFormulaPhi f 0) +
        (((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I))
      hreflected_value hinverse_value hcomponent

/-- Vertically regular prime-channel convergence from the reflected completed
value owner theorem and the one-sided inverse-Gamma owner theorem. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_of_verticallyRegular_reflectedCompletedValue_owner
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hscalar : zetaCompletedExplicitFormulaPrimeNaturalScalarHermitian f) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel
          f F.toContourFamily (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  let V : ℂ :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedValue f
  have hreflected_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F.toContourFamily t) = V :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_eq_ownerReflectedCompletedValue
      f F h hcoh hscalar
  have hcomponent :
      V -
          (-(zetaCompletedExplicitFormulaPhi f 0) +
            (((2 * (Real.pi : ℂ) * Complex.I) *
              (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I)) =
        -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) := by
    exact
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedValue_sub_leftOneSidedInverseGammaValue
        f
  exact
    zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_of_verticallyRegular_reflectedLeft_and_leftOneSidedInverseGammaValue
      f F h hcoh V hreflected_value hcomponent

/-- Consistency check for the two possible left-prime value normalizations.

If the same unsplit left affine logarithmic-derivative kernel has both the
residue-free value `0` and the complement-carrying value `-C`, then that
complement contribution must vanish.  This theorem is intentionally algebraic:
it records why the final prime proof cannot use both target normalizations for
the same kernel unless a further analytic split has separated the
residue-free tail from the complement term. -/
theorem zetaCompletedExplicitFormulaPrimeLeft_zero_and_negativeComplement_values_force_complement_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hzero :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) =
        0)
    (hneg :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) =
        -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f)) :
    zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f = 0 := by
  let L : ℂ :=
    ∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t
  let C : ℂ := zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f
  have hC_neg_zero : -C = 0 := by
    calc
      -C = L := by
        exact hneg.symm
      _ = 0 := by
        exact hzero
  calc
    C = -(-C) := by
      exact (neg_neg C).symm
    _ = -0 := by
      exact congrArg Neg.neg hC_neg_zero
    _ = 0 := by
      exact neg_zero

/-- The currently proved right one-sided inversion plus a residue-free left
tail proves only the one-sided natural prime contribution.

This theorem records the exact strength of the existing ingredients.  It is not
the final prime-channel theorem because the public contribution is the
symmetric natural contribution. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeNaturalOneSidedContribution_of_leftIntegral_eq_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (E : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ E.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖))
    (hleft_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) =
        0) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f)) := by
  have hright :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral
            f F h u)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f)) :=
    explicitFormulaScheduledScalar_tendsto_of_forall_eq
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral
          f F h u)
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t)
      (zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f)
      (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernelIntegral_tendsto_primeNaturalOneSidedContribution_direct_ownerInversion
        f F h)
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral_eq_affineKernelIntegral
          f F h u)
  have hleft :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
            f F h u)
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral_tendsto_zero_of_zeroExcisedLine_inverseGamma_bound_and_integral_eq_zero
      f F h hregular E hline_mem BG hBG_nonneg hinverseGamma_bound
      hleft_value
  have hsub :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral
            f F h u -
            zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
              f F h u)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f - 0)) :=
    hright.sub hleft
  have hlimit :
      zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f - 0 =
        zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f :=
    sub_zero (zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f)
  have hchannel_fun :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel
          f F (h.height_schedule.height u)) =
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral
          f F h u -
          zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
            f F h u) := by
    funext u
    exact
      zetaCompletedExplicitFormulaPrimeVerticalChannel_eq_scheduledRightVonMangoldt_sub_scheduledLeft
        f F h u
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        Tendsto φ atTop
          (𝓝 (zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f)))
      hchannel_fun.symm
      (Eq.subst
        (motive := fun z : ℂ =>
          Tendsto
            (fun u : ℝ =>
              zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral
                f F h u -
                zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
                  f F h u)
            atTop
            (𝓝 z))
        hlimit
        hsub)

/-- Prime vertical-channel convergence from the currently exposed honest
kernel-value inputs.

This theorem is deliberately not the final unconditional owner theorem: the
right input is a full prime-kernel value theorem, not the proved one-sided
right von Mangoldt value alone, and the left input is the genuine whole-line
residue-free contour value.  It packages only the already proved scheduling and
finite-height channel algebra. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_of_zeroExcisedLine_inverseGamma_bound_and_kernel_values
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (E : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ E.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖))
    (hright_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t) =
        zetaCompletedExplicitFormulaPrimeContribution f)
    (hleft_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) =
        0) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  have hright :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral
            f F h u)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) :=
    zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral_tendsto_primeContribution_of_integral_eq
      f F h hright_value
  have hleft :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
            f F h u)
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral_tendsto_zero_of_zeroExcisedLine_inverseGamma_bound_and_integral_eq_zero
      f F h hregular E hline_mem BG hBG_nonneg hinverseGamma_bound hleft_value
  exact
    zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_of_scheduledRightVonMangoldt_and_scheduledLeftPrime
      f F h hright hleft

/-- Vertically regular specialization of the honest kernel-value prime
vertical-channel assembly.  The vertically regular owner supplies the
left-line zero-excision and inverse-Gamma growth data; the two whole-line
kernel values remain the analytic inputs. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_of_verticallyRegular_gammaBinet_kernel_value_inputs
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hright_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaPrimeContribution f)
    (hleft_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel
          f F.toContourFamily t) =
        0) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel
          f F.toContourFamily (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  let E : CompletedZetaZeroExcisedStrip
      (1 - F.toContourFamily.c) (1 - F.toContourFamily.c) :=
    zetaCompletedExplicitFormulaLeftAffineLineZeroExcisedStrip_of_verticallyRegular
      F
  have hregular :
      zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
        F.toContourFamily :=
    zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
      F
  have hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F.toContourFamily t ∈
          E.carrier :=
    zetaCompletedExplicitFormulaLeftAffineLine_mem_zeroExcisedStrip_of_verticallyRegular
      F
  match
    zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_gammaBinetCoherence_owner
      F.toContourFamily hregular hcoh with
  | ⟨BG, hBG_nonneg, hinverseGamma_bound⟩ =>
      exact
        zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_of_zeroExcisedLine_inverseGamma_bound_and_kernel_values
          f F.toContourFamily h hregular E hline_mem
          BG hBG_nonneg hinverseGamma_bound hright_value hleft_value

/-- Prime-channel convergence is the algebraic consequence of vanishing of the
transport remainder.  The analytic content is the remainder estimate, not this
rewriting step. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_of_transportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (htransport :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
            f F (h.height_schedule.height u))
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  let P : ℂ := zetaCompletedExplicitFormulaPrimeContribution f
  let R : ℝ → ℂ := fun u : ℝ =>
    zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
      f F (h.height_schedule.height u)
  have hsum :
      Tendsto (fun u : ℝ => P + R u) atTop (𝓝 (P + 0)) :=
    tendsto_const_nhds.add htransport
  have htarget : P + 0 = P :=
    add_zero P
  have hsum_target :
      Tendsto (fun u : ℝ => P + R u) atTop (𝓝 P) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto (fun u : ℝ => P + R u) atTop (𝓝 z))
      htarget
      hsum
  have hchannel :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel
          f F (h.height_schedule.height u)) =
        fun u : ℝ => P + R u := by
    funext u
    let C : ℂ :=
      zetaCompletedExplicitFormulaPrimeVerticalChannel
        f F (h.height_schedule.height u)
    change C = P + (C - P)
    exact (add_sub_cancel_left P C).symm
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 P))
      hchannel.symm
      hsum_target

/-- Prime transport-remainder decay is the algebraic consequence of prime
vertical-channel convergence.

This duplicate of the downstream projection-layer algebra is kept here to
avoid importing the projection owner back into the prime transport owner.  It
uses only the definition
`transportRemainder T = primeVerticalChannel T - primeContribution`. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder_tendsto_zero_of_primeChannel_tendsto_ownerPrimeLogDerivativeTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hchannel :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeVerticalChannel
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f))) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  let P : ℂ := zetaCompletedExplicitFormulaPrimeContribution f
  let C : ℝ → ℂ := fun u : ℝ =>
    zetaCompletedExplicitFormulaPrimeVerticalChannel
      f F (h.height_schedule.height u)
  have hsub :
      Tendsto (fun u : ℝ => C u - P) atTop (𝓝 (P - P)) :=
    hchannel.sub tendsto_const_nhds
  have hzero :
      P - P = 0 :=
    sub_self P
  have hsub_zero :
      Tendsto (fun u : ℝ => C u - P) atTop (𝓝 0) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto (fun u : ℝ => C u - P) atTop (𝓝 z))
      hzero
      hsub
  have hremainder_fun :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
          f F (h.height_schedule.height u)) =
        fun u : ℝ => C u - P := by
    funext u
    rfl
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
      hremainder_fun.symm
      hsub_zero

/-- Vertically regular scheduled-left complement limit.

This proves the scheduled left prime logarithmic-derivative packet limit in
the concrete vertically regular owner package from the already-owned
reflected-completed prime-channel theorem and the proved right one-sided
von Mangoldt inversion.  The general arbitrary-contour theorem below is the
remaining extension problem; this theorem records that no further algebra is
missing in the vertically regular branch. -/
theorem zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral_tendsto_neg_complement_of_verticallyRegular_reflectedCompletedValue_owner
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hscalar : zetaCompletedExplicitFormulaPrimeNaturalScalarHermitian f) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
          f F.toContourFamily h u)
      atTop
      (𝓝 (-(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f))) := by
  let R : ℂ := zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f
  let C : ℂ := zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f
  let P : ℂ := zetaCompletedExplicitFormulaPrimeContribution f
  have hright :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral
            f F.toContourFamily h u)
        atTop
        (𝓝 R) :=
    explicitFormulaScheduledScalar_tendsto_of_forall_eq
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral
          f F.toContourFamily h u)
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
              (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
              (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
            f F.toContourFamily t)
      R
      (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernelIntegral_tendsto_primeNaturalOneSidedContribution_direct_ownerInversion
        f F.toContourFamily h)
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral_eq_affineKernelIntegral
          f F.toContourFamily h u)
  have hprime :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeVerticalChannel
            f F.toContourFamily (h.height_schedule.height u))
        atTop
        (𝓝 P) :=
    zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_of_verticallyRegular_reflectedCompletedValue_owner
      f F h hcoh hscalar
  have hleft :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
            f F.toContourFamily h u)
        atTop
        (𝓝 (R - P)) :=
    zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral_tendsto_of_scheduledRightVonMangoldt_and_primeChannel
      f F.toContourFamily h R P hright hprime
  have hrecombine :
      R + C = P :=
    zetaCompletedExplicitFormulaPrimeNaturalOneSided_add_complementContribution_eq_primeContribution
      f
  have htarget :
      R - P = -C := by
    calc
      R - P = R - (R + C) := by
        exact congrArg (fun z : ℂ => R - z) hrecombine.symm
      _ = R + -(R + C) := by
        exact sub_eq_add_neg R (R + C)
      _ = R + (-R + -C) := by
        exact congrArg (fun z : ℂ => R + z) (neg_add R C)
      _ = (R + -R) + -C := by
        exact (add_assoc R (-R) (-C)).symm
      _ = 0 + -C := by
        exact congrArg (fun z : ℂ => z + -C) (add_right_neg R)
      _ = -C := by
        exact zero_add (-C)
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
              f F.toContourFamily h u)
          atTop
          (𝓝 z))
      htarget
      hleft

/-- General scheduled-left complement extraction from a completed prime-channel
limit.

This is the contour-family version of the algebra used in the vertically
regular branch.  It keeps the analytic obligation honest: to use this theorem
one must already have proved the general prime vertical-channel limit by some
independent owner theorem, and the conclusion is then just
`left = right - prime` plus the one-sided/complement recombination. -/
theorem zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral_tendsto_neg_complement_of_primeChannel_ownerPrimeLogDerivativeTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hprime :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeVerticalChannel
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f))) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
          f F h u)
      atTop
      (𝓝 (-(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f))) := by
  let R : ℂ := zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f
  let C : ℂ := zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f
  let P : ℂ := zetaCompletedExplicitFormulaPrimeContribution f
  have hright :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral
            f F h u)
        atTop
        (𝓝 R) :=
    explicitFormulaScheduledScalar_tendsto_of_forall_eq
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral
          f F h u)
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t)
      R
      (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernelIntegral_tendsto_primeNaturalOneSidedContribution_direct_ownerInversion
        f F h)
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral_eq_affineKernelIntegral
          f F h u)
  have hleft :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
            f F h u)
        atTop
        (𝓝 (R - P)) :=
    zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral_tendsto_of_scheduledRightVonMangoldt_and_primeChannel
      f F h R P hright hprime
  have hrecombine :
      R + C = P :=
    zetaCompletedExplicitFormulaPrimeNaturalOneSided_add_complementContribution_eq_primeContribution
      f
  have htarget :
      R - P = -C := by
    calc
      R - P = R - (R + C) := by
        exact congrArg (fun z : ℂ => R - z) hrecombine.symm
      _ = R + -(R + C) := by
        exact sub_eq_add_neg R (R + C)
      _ = R + (-R + -C) := by
        exact congrArg (fun z : ℂ => R + z) (neg_add R C)
      _ = (R + -R) + -C := by
        exact (add_assoc R (-R) (-C)).symm
      _ = 0 + -C := by
        exact congrArg (fun z : ℂ => z + -C) (add_right_neg R)
      _ = -C := by
        exact zero_add (-C)
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
              f F h u)
          atTop
          (𝓝 z))
      htarget
      hleft

/-- Transport the vertically regular scheduled-left complement theorem across
an equality of underlying contour families.

This is the honest bridge between the proved vertically regular branch and a
general `ExplicitFormulaContourFamily` package.  It does not manufacture
vertical regularity from the analytic package; callers must provide the
vertically regular owner object whose projection is the given contour family. -/
theorem zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral_tendsto_neg_complement_of_verticallyRegular_toContourFamily_eq
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaContourFamily)
    (Fv : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hscalar : zetaCompletedExplicitFormulaPrimeNaturalScalarHermitian f)
    (hF : Fv.toContourFamily = F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
          f F h u)
      atTop
      (𝓝 (-(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f))) := by
  let Target : (F' : ExplicitFormulaContourFamily) →
      ExplicitFormulaFamilyAnalyticPackage f F' → Prop :=
    fun F' h' =>
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
            f F' h' u)
        atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f)))
  have hv :
      Target Fv.toContourFamily :=
    fun hv_package =>
      zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral_tendsto_neg_complement_of_verticallyRegular_reflectedCompletedValue_owner
        f Fv hv_package hcoh hscalar
  have htransport :
      Target F :=
    Eq.subst
      (motive := Target)
      hF
      hv
  exact htransport h

/-- Vertically regular wrapper around the prime-channel owner theorem, proved
through the reflected completed-left component and the scalar-Hermitian
natural-prime normalization.

This wrapper deliberately avoids the overbroad general transport-remainder
leaf: in the current API the honest reflected-complement value theorem is
available under the vertically regular and scalar-Hermitian hypotheses. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_of_verticallyRegular_gammaBinet_owner
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hscalar : zetaCompletedExplicitFormulaPrimeNaturalScalarHermitian f) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel
          f F.toContourFamily (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  exact
    zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_of_verticallyRegular_reflectedCompletedValue_owner
      f F h hcoh hscalar

/-- Vertically regular prime-channel convergence from the structural two-face
natural-time normalization. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_of_verticallyRegular_gammaBinet_owner_of_timeSummand_eq_twoFace
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (htwoFace :
      ∀ n : ℕ,
        zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n =
          zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel
          f F.toContourFamily (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  have hscalar : zetaCompletedExplicitFormulaPrimeNaturalScalarHermitian f :=
    zetaCompletedExplicitFormulaPrimeNaturalScalarHermitian_of_timeSummand_eq_twoFaceBoundarySample
      f htwoFace
  exact
    zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_of_verticallyRegular_gammaBinet_owner
      f F h hcoh hscalar

/-- Vertically regular transport-remainder form of the prime channel estimate.
This wrapper delegates to the scalar-Hermitian vertically regular owner wrapper. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder_tendsto_zero_of_verticallyRegular_gammaBinet_owner
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hscalar : zetaCompletedExplicitFormulaPrimeNaturalScalarHermitian f) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
          f F.toContourFamily (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder_tendsto_zero_of_primeChannel_tendsto_ownerPrimeLogDerivativeTransport
      f F.toContourFamily h
      (zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_of_verticallyRegular_gammaBinet_owner
        f F h hcoh hscalar)

/-- Vertically regular prime-channel transport-remainder convergence from the
structural two-face natural-time normalization. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder_tendsto_zero_of_verticallyRegular_gammaBinet_owner_of_timeSummand_eq_twoFace
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (htwoFace :
      ∀ n : ℕ,
        zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n =
          zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
          f F.toContourFamily (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  have hscalar : zetaCompletedExplicitFormulaPrimeNaturalScalarHermitian f :=
    zetaCompletedExplicitFormulaPrimeNaturalScalarHermitian_of_timeSummand_eq_twoFaceBoundarySample
      f htwoFace
  exact
    zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder_tendsto_zero_of_verticallyRegular_gammaBinet_owner
      f F h hcoh hscalar

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

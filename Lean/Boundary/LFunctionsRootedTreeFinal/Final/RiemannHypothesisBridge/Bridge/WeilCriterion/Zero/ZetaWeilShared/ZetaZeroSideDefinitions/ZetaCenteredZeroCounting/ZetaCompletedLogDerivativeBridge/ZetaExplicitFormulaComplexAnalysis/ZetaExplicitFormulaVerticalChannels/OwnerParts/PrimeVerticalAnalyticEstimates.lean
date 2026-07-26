import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeScheduledChannels
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeAffineKernelEstimates
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ScheduledKernelLimitTransport

/-!
# Prime vertical analytic estimates

This file assembles the scheduled prime vertical-channel estimates from the
affine prime-kernel estimates and the scheduled-channel normal forms.
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

/-- The right von Mangoldt vertical integral converges to the completed prime
contribution once a genuine full prime-kernel value theorem is supplied.

The right affine kernel alone proves only the one-sided natural contribution.
The hypothesis here is intentionally explicit until the reflected/complement
prime branch is constructed and assembled with the right branch. -/
theorem zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral_tendsto_primeContribution
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t) =
        zetaCompletedExplicitFormulaPrimeContribution f) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral
          f F h u)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  let K : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t
  have hkernel :
      Tendsto K atTop (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) :=
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernelIntegral_tendsto_primeContribution_of_integral_eq
      f F h hvalue
  exact
    explicitFormulaScheduledScalar_tendsto_of_forall_eq
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral f F h u)
      K
      (zetaCompletedExplicitFormulaPrimeContribution f)
      hkernel
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral_eq_affineKernelIntegral
          f F h u)

/-- The scheduled right von Mangoldt vertical integral converges to the
completed prime contribution once the right affine kernel has been identified
with the prime-distribution contribution. -/
theorem zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral_tendsto_primeContribution_of_integral_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t) =
        zetaCompletedExplicitFormulaPrimeContribution f) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral
          f F h u)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  let K : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t
  have hkernel :
      Tendsto K atTop (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) :=
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernelIntegral_tendsto_primeContribution_of_integral_eq
      f F h hvalue
  exact
    explicitFormulaScheduledScalar_tendsto_of_forall_eq
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral f F h u)
      K
      (zetaCompletedExplicitFormulaPrimeContribution f)
      hkernel
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral_eq_affineKernelIntegral
          f F h u)

/-- The left prime logarithmic-derivative vertical tail vanishes by the
kernel-level tail decay theorem. -/
theorem zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral_tendsto_zero
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
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) =
        0) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
          f F h u)
      atTop
      (𝓝 0) := by
  let K : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t
  have hkernel : Tendsto K atTop (𝓝 0) :=
    zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernelIntegral_tendsto_zero
      f F h hregular E hline_mem BG hBG_nonneg hinverseGamma_bound hvalue
  exact
    explicitFormulaScheduledScalar_tendsto_of_forall_eq
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral f F h u)
      K
      0
      hkernel
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral_eq_affineKernelIntegral
          f F h u)

/-- The scheduled left prime logarithmic-derivative vertical integral converges
to any separately proved whole-line affine-kernel value. -/
theorem zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral_tendsto_of_integral_eq
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
    (value : ℂ)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) =
        value) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
          f F h u)
      atTop
      (𝓝 value) := by
  let K : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t
  have hkernel_integral :
      Tendsto K atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t)) :=
    zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernelIntegral_tendsto_integral_of_zeroExcisedLine_inverseGamma_bound
      f F h hregular E hline_mem BG hBG_nonneg hinverseGamma_bound
  have hkernel : Tendsto K atTop (𝓝 value) :=
    Eq.subst
      (motive := fun z : ℂ => Tendsto K atTop (𝓝 z))
      hvalue
      hkernel_integral
  exact
    explicitFormulaScheduledScalar_tendsto_of_forall_eq
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral f F h u)
      K
      value
      hkernel
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral_eq_affineKernelIntegral
          f F h u)

/-- The scheduled left prime logarithmic-derivative vertical tail vanishes from
the honest whole-line majorant hypotheses and the separately proved left-tail
zero value. -/
theorem zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral_tendsto_zero_of_zeroExcisedLine_inverseGamma_bound_and_integral_eq_zero
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
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) =
        0) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
          f F h u)
      atTop
      (𝓝 0) := by
  let K : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t
  have hkernel : Tendsto K atTop (𝓝 0) :=
    zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernelIntegral_tendsto_zero_of_zeroExcisedLine_inverseGamma_bound_and_integral_eq_zero
      f F h hregular E hline_mem BG hBG_nonneg hinverseGamma_bound hvalue
  exact
    explicitFormulaScheduledScalar_tendsto_of_forall_eq
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral f F h u)
      K
      0
      hkernel
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral_eq_affineKernelIntegral
          f F h u)

/-- Combined prime vertical-channel analytic estimates. -/
theorem zetaCompletedExplicitFormulaPrimeScheduledEstimates_tendsto
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
            zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral
              f F h u)
          atTop
          (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) ∧
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
              f F h u)
          atTop
          (𝓝 0) :=
  And.intro
    (zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral_tendsto_primeContribution
      f F h hright_value)
    (zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral_tendsto_zero
      f F h hregular E hline_mem BG hBG_nonneg hinverseGamma_bound hleft_value)

/-- Combined prime vertical-channel analytic estimates from the honest
kernel-level value and left-tail hypotheses. -/
theorem zetaCompletedExplicitFormulaPrimeScheduledEstimates_tendsto_of_kernel_values
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
            zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral
              f F h u)
          atTop
          (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) ∧
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
              f F h u)
          atTop
          (𝓝 0) :=
  And.intro
    (zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral_tendsto_primeContribution_of_integral_eq
      f F h hright_value)
    (zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral_tendsto_zero_of_zeroExcisedLine_inverseGamma_bound_and_integral_eq_zero
      f F h hregular E hline_mem BG hBG_nonneg hinverseGamma_bound hleft_value)

/-- Combined prime scheduled estimates for a vertically regular contour family,
with the auxiliary left-line zero-excision and inverse-Gamma bounds supplied by
their owner lemmas.  The only remaining analytic inputs are the two whole-line
kernel value identities. -/
theorem zetaCompletedExplicitFormulaPrimeScheduledEstimates_tendsto_of_verticallyRegular_gammaBinet_kernel_values
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
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
            zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral
              f F.toContourFamily h u)
          atTop
          (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) ∧
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
              f F.toContourFamily h u)
          atTop
          (𝓝 0) := by
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
    zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_unconditional_owner
      F.toContourFamily hregular with
  | ⟨BG, hBG_nonneg, hinverseGamma_bound⟩ =>
      exact
        zetaCompletedExplicitFormulaPrimeScheduledEstimates_tendsto_of_kernel_values
          f F.toContourFamily h hregular E hline_mem
          BG hBG_nonneg hinverseGamma_bound hright_value hleft_value

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeLogDerivativeTransport

/-!
# Raw prime two-face target
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The whole left prime affine kernel has the actual negative reflected-face
value, without identifying that face with an arithmetic complement. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_integral_eq_neg_reflectedBoundary_ownerRawTwoFace
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel
        f F.toContourFamily t) =
      -(zetaCompletedExplicitFormulaPrimeNaturalReflectedBoundaryContribution f) := by
  let reflectedValue : ℂ :=
    ∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t
  let inverseValue : ℂ :=
    zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f
  have hreflectedIntegrable :
      Integrable
        (zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integrable_of_verticallyRegular
      f F h
  have hregular :
      zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F.toContourFamily :=
    zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular F
  have hinverseIntegrable :
      Integrable
        (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_integrable
      f F.toContourFamily h hregular hcoh
  have hinverseValue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
          f F.toContourFamily t) = inverseValue :=
    zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_integral_eq_negPhiZero_add_correctionLeftValue_ownerOneSidedValues
      f F.toContourFamily h hcoh
  have hreflectedInverseValue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel_integral_eq_leftOneSidedInverseGammaValue_owner
      f F.toContourFamily h hcoh
  have hreflectedDifference :
      reflectedValue - inverseValue =
        -(zetaCompletedExplicitFormulaPrimeNaturalReflectedBoundaryContribution f) :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_reflectedBoundary_of_reflectedInverseGammaValue
      f F h hcoh hreflectedInverseValue
  have hsplit :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel
          f F.toContourFamily t) =
        reflectedValue -
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
              f F.toContourFamily t :=
    zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_integral_eq_reflectedCompleted_sub_inverseGamma
      f F.toContourFamily hreflectedIntegrable hinverseIntegrable
  exact Eq.trans hsplit
    (Eq.trans
      (congrArg (fun value : ℂ => reflectedValue - value) hinverseValue)
      hreflectedDifference)

/-- Scheduled exhaustion of the actual negative reflected left prime face. -/
theorem zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral_tendsto_neg_reflectedBoundary_ownerRawTwoFace
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
          f F.toContourFamily h u)
      atTop
      (𝓝 (-(zetaCompletedExplicitFormulaPrimeNaturalReflectedBoundaryContribution f))) := by
  let E : CompletedZetaZeroExcisedStrip
      (1 - F.toContourFamily.c) (1 - F.toContourFamily.c) :=
    zetaCompletedExplicitFormulaLeftAffineLineZeroExcisedStrip_of_verticallyRegular F
  have hlineMem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F.toContourFamily t ∈ E.carrier :=
    zetaCompletedExplicitFormulaLeftAffineLine_mem_zeroExcisedStrip_of_verticallyRegular F
  have hregular :
      zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F.toContourFamily :=
    zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular F
  have hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel
          f F.toContourFamily t) =
        -(zetaCompletedExplicitFormulaPrimeNaturalReflectedBoundaryContribution f) :=
    zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_integral_eq_neg_reflectedBoundary_ownerRawTwoFace
      f F h hcoh
  exact
    match
      zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_gammaBinetCoherence_owner
        F.toContourFamily hregular hcoh with
    | ⟨bound, hboundNonnegative, hbound⟩ =>
        zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral_tendsto_of_integral_eq
          f F.toContourFamily h hregular E hlineMem
          bound hboundNonnegative hbound
          (-(zetaCompletedExplicitFormulaPrimeNaturalReflectedBoundaryContribution f))
          hvalue

/-- The raw scheduled prime vertical channel converges to the actual sum of
its right and reflected Mellin faces. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_twoFaceBoundaryContribution_ownerRawTwoFace
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel
          f F.toContourFamily (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution f)) := by
  have hright :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral
            f F.toContourFamily h u)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f)) :=
    explicitFormulaScheduledScalar_tendsto_of_forall_eq
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral
          f F.toContourFamily h u)
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
            f F.toContourFamily t)
      (zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f)
      (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernelIntegral_tendsto_primeNaturalOneSidedContribution_direct_ownerInversion
        f F.toContourFamily h)
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral_eq_affineKernelIntegral
          f F.toContourFamily h u)
  have hleft :=
    zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral_tendsto_neg_reflectedBoundary_ownerRawTwoFace
      f F h hcoh
  have hsub := hright.sub hleft
  have htarget :
      zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f -
          (-(zetaCompletedExplicitFormulaPrimeNaturalReflectedBoundaryContribution f)) =
        zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution f := by
    calc
      zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f -
          (-(zetaCompletedExplicitFormulaPrimeNaturalReflectedBoundaryContribution f)) =
          zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f +
            zetaCompletedExplicitFormulaPrimeNaturalReflectedBoundaryContribution f := by
        exact sub_neg_eq_add
          (zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f)
          (zetaCompletedExplicitFormulaPrimeNaturalReflectedBoundaryContribution f)
      _ = zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution f := by
        exact
          (zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution_eq_oneSided_add_reflectedBoundaryContribution
            f).symm
  have hchannel :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral
              f F.toContourFamily h u -
          zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
              f F.toContourFamily h u) =
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel
          f F.toContourFamily (h.height_schedule.height u)) := by
    exact funext (fun u : ℝ =>
      (zetaCompletedExplicitFormulaPrimeVerticalChannel_eq_scheduledRightVonMangoldt_sub_scheduledLeft
        f F.toContourFamily h u).symm)
  exact Eq.subst
    (motive := fun values : ℝ → ℂ =>
      Tendsto values atTop
        (𝓝 (zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution f)))
    hchannel
    (Eq.subst
      (motive := fun target : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral
                  f F.toContourFamily h u -
              zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
                  f F.toContourFamily h u)
          atTop (𝓝 target))
      htarget hsub)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

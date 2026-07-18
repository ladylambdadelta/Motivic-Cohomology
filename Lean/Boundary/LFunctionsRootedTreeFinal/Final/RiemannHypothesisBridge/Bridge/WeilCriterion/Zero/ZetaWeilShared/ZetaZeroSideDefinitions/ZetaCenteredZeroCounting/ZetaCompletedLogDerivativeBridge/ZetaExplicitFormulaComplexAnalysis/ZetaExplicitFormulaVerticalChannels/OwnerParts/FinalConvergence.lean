import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.CorrectionVerticalConvergence
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.InverseGammaScheduledNormalization
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeLeftLogDerivativeTail
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.TransportProjection

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

/-- Correction-channel analytic transport: the scheduled pole-face vertical integral
converges to the standard-contour correction boundary value. -/
theorem zetaCompletedExplicitFormulaCorrectionVerticalChannel_tendsto_correctionContribution_ownerChannelTransportAnalytic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hone :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c))) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaSelectedScheduledVerticalChannel
          f F h u ExplicitFormulaScheduledVerticalChannelProjection.correction)
      atTop
      (𝓝
        (explicitFormulaSelectedVerticalBoundaryChannel
          f ExplicitFormulaScheduledVerticalChannelProjection.correction)) := by
    have hconcrete :
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionVerticalChannel f F
              (h.height_schedule.height u))
          atTop
          (𝓝 (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) :=
      zetaCompletedExplicitFormulaCorrectionVerticalChannel_tendsto_correctionContribution_concrete_ownerChannelTransportAnalytic
        f F h hone
    have hpointwise :
        (fun u : ℝ =>
          explicitFormulaSelectedScheduledVerticalChannel
            f F h u ExplicitFormulaScheduledVerticalChannelProjection.correction) =
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionVerticalChannel f F
              (h.height_schedule.height u)) := by
      funext u
      exact explicitFormulaSelectedScheduledVerticalChannel_correction_eq f F h u
    have htarget :
        explicitFormulaSelectedVerticalBoundaryChannel
            f ExplicitFormulaScheduledVerticalChannelProjection.correction =
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f :=
      explicitFormulaSelectedVerticalBoundaryChannel_correction_eq f
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop
        (𝓝
          (explicitFormulaSelectedVerticalBoundaryChannel
            f ExplicitFormulaScheduledVerticalChannelProjection.correction)))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionVerticalChannel f F
              (h.height_schedule.height u))
          atTop
          (𝓝 z))
      htarget.symm
      hconcrete)

/-- Vertically regular prime-channel transport-remainder core theorem.

This is the non-circular final-convergence entry point for callers that own a
vertically regular contour family.  It delegates to the vertically regular
prime transport theorem with the scalar-Hermitian natural-prime normalization,
and does not use the arbitrary-contour prime extension leaf. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder_tendsto_zero_of_verticallyRegular_ownerChannelTransportCore
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
    zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder_tendsto_zero_of_verticallyRegular_gammaBinet_owner
      f F h hcoh hscalar

/-- Owner analytic theorem: the archimedean vertical-channel transport remainder vanishes
along the scheduled contour heights.  This is the Gamma/completion channel transport
estimate; the contribution limit is a formal consequence. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder_tendsto_zero_ownerChannelTransportCore
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t) =
        zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder_tendsto_zero_ownerArchimedeanTransport
      f F h hregular hcoh hvalue

/-- Owner analytic theorem: the correction vertical-channel transport remainder vanishes
along the scheduled contour heights.  This is the pole-face transport estimate; the
convergence to the correction contribution is a formal consequence. -/
theorem zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder_tendsto_zero_ownerChannelTransportCore
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hone :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c))) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  have hprojection :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
            f F (h.height_schedule.height u)
            ExplicitFormulaScheduledVerticalChannelProjection.correction)
        atTop
        (𝓝 0) :=
    explicitFormulaScheduledVerticalChannelProjectionTransportRemainder_tendsto_zero_of_selectedChannel_tendsto_boundary
      f F h ExplicitFormulaScheduledVerticalChannelProjection.correction
      (zetaCompletedExplicitFormulaCorrectionVerticalChannel_tendsto_correctionContribution_ownerChannelTransportAnalytic
        f F h hone)
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
          f F (h.height_schedule.height u)) =
        (fun u : ℝ =>
          explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
            f F (h.height_schedule.height u)
            ExplicitFormulaScheduledVerticalChannelProjection.correction) := by
    funext u
    exact
      (explicitFormulaScheduledVerticalChannelProjectionTransportRemainder_correction_eq
        f F (h.height_schedule.height u)).symm
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    hprojection

/-- Prime vertical-channel convergence from its scheduled transport-remainder estimate. -/
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
        zetaCompletedExplicitFormulaPrimeVerticalChannel f F
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  exact
    explicitFormulaScheduledVerticalChannel_tendsto_boundaryContribution_of_tendsto_transportRemainder
      (zetaCompletedExplicitFormulaPrimeContribution f)
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel f F
          (h.height_schedule.height u))
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel_eq_contribution_add_transportRemainder
          f F (h.height_schedule.height u))
      htransport

/-- Archimedean vertical-channel convergence from its scheduled transport-remainder
estimate. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_of_transportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (htransport :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
            f F (h.height_schedule.height u))
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  exact
    explicitFormulaScheduledVerticalChannel_tendsto_boundaryContribution_of_tendsto_transportRemainder
      (zetaCompletedExplicitFormulaArchimedeanContribution f)
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F
          (h.height_schedule.height u))
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel_eq_contribution_add_transportRemainder
          f F (h.height_schedule.height u))
      htransport

/-- Correction vertical-channel convergence from its scheduled standard-contour
transport-remainder estimate. -/
theorem zetaCompletedExplicitFormulaCorrectionVerticalChannel_tendsto_correctionContribution_of_transportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
      (htransport :
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
              f F (h.height_schedule.height u))
          atTop
          (𝓝 0)) :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionVerticalChannel f F
            (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) := by
    exact
      explicitFormulaScheduledVerticalChannel_tendsto_boundaryContribution_of_tendsto_transportRemainder
        (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannel f F
          (h.height_schedule.height u))
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannel_eq_contribution_add_transportRemainder
          f F (h.height_schedule.height u))
      htransport

/-- Owner theorem: the archimedean vertical channel converges to the completed
archimedean contribution along the scheduled contour heights. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_ownerChannelTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t) =
        zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  exact
    zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_of_transportRemainder
      f F h
      (zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder_tendsto_zero_ownerChannelTransportCore
        f F h hregular hcoh hvalue)

/-- Owner theorem: the pole-correction vertical channel converges to the
standard-contour correction boundary value along the scheduled contour heights. -/
theorem zetaCompletedExplicitFormulaCorrectionVerticalChannel_tendsto_correctionContribution_ownerChannelTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
      (h : ExplicitFormulaFamilyAnalyticPackage f F)
      (hone :
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
              f F (h.height_schedule.height u))
          atTop
          (𝓝 (zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c))) :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionVerticalChannel f F
            (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionVerticalChannel_tendsto_correctionContribution_of_transportRemainder
      f F h
      (zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder_tendsto_zero_ownerChannelTransportCore
        f F h hone)

/-- The archimedean transport remainder vanishes once the archimedean channel has been
transported to its completed contribution. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder_tendsto_zero_ownerChannelTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t) =
        zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder_tendsto_zero_ownerChannelTransportCore
      f F h hregular hcoh hvalue

/-- The correction transport remainder vanishes once the correction channel has been
transported to its completed contribution. -/
theorem zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder_tendsto_zero_ownerChannelTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hone :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c))) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder_tendsto_zero_ownerChannelTransportCore
      f F h hone

/-- Final prime-channel convergence for a vertically regular contour family,
delegated to the prime-channel owner theorem. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_of_verticallyRegular_gammaBinet_ownerChannelTransport
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
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) :=
  zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_of_verticallyRegular_gammaBinet_owner
    f F h hcoh hscalar

/-- Final prime-channel convergence from the structural two-face natural-time
normalization. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_of_verticallyRegular_gammaBinet_ownerChannelTransport_of_timeSummand_eq_twoFace
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
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) :=
  zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_of_verticallyRegular_gammaBinet_owner_of_timeSummand_eq_twoFace
    f F h hcoh htwoFace

/-- Final archimedean-channel convergence for a vertically regular contour
family.  The remaining analytic input is the whole-line inverse-Gamma value
identity. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_of_verticallyRegular_gammaBinet_integral_eq_ownerChannelTransport
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel
          f F.toContourFamily (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) :=
  zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_of_verticallyRegular_gammaBinet_integral_eq
    f F h hcoh hvalue

/-- Final transport-remainder package for the three vertical channels on a
vertically regular contour.  This theorem intentionally exposes the remaining
analytic leaves rather than hiding them in a downstream prerequisite. -/
theorem zetaCompletedExplicitFormulaVerticalChannelTransportRemainders_tendsto_zero_of_verticallyRegular_gammaBinet_owner
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hscalar : zetaCompletedExplicitFormulaPrimeNaturalScalarHermitian f)
    (hinverseGamma_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)
    (hone :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            f F.toContourFamily (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue
          f F.toContourFamily.c))) :
      Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
              f F.toContourFamily (h.height_schedule.height u))
          atTop
          (𝓝 0) ∧
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
              f F.toContourFamily (h.height_schedule.height u))
          atTop
          (𝓝 0) ∧
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
              f F.toContourFamily (h.height_schedule.height u))
          atTop
          (𝓝 0) :=
  And.intro
    (zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder_tendsto_zero_of_verticallyRegular_gammaBinet_owner
      f F h hcoh hscalar)
    (And.intro
      (zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder_tendsto_zero_of_verticallyRegular_gammaBinet_integral_eq
        f F h hcoh hinverseGamma_value)
      (zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder_tendsto_zero_ownerChannelTransport
        f F.toContourFamily h hone))

/-- Final transport-remainder package from the structural two-face natural-time
normalization. -/
theorem zetaCompletedExplicitFormulaVerticalChannelTransportRemainders_tendsto_zero_of_verticallyRegular_gammaBinet_owner_of_timeSummand_eq_twoFace
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (htwoFace :
      ∀ n : ℕ,
        zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n =
          zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n)
    (hinverseGamma_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)
    (hone :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            f F.toContourFamily (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue
          f F.toContourFamily.c))) :
      Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
              f F.toContourFamily (h.height_schedule.height u))
          atTop
          (𝓝 0) ∧
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
              f F.toContourFamily (h.height_schedule.height u))
          atTop
          (𝓝 0) ∧
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
              f F.toContourFamily (h.height_schedule.height u))
          atTop
          (𝓝 0) := by
  have hscalar : zetaCompletedExplicitFormulaPrimeNaturalScalarHermitian f :=
    zetaCompletedExplicitFormulaPrimeNaturalScalarHermitian_of_timeSummand_eq_twoFaceBoundarySample
      f htwoFace
  exact
    zetaCompletedExplicitFormulaVerticalChannelTransportRemainders_tendsto_zero_of_verticallyRegular_gammaBinet_owner
      f F h hcoh hscalar hinverseGamma_value hone

/-- Final transport-remainder package for a vertically regular contour, stated
against the scheduled analytic leaves.  The inverse-Gamma whole-line value is
derived by the affine-kernel exhaustion lemma; the right one-pole decay remains
an explicit independent input. -/
theorem zetaCompletedExplicitFormulaVerticalChannelTransportRemainders_tendsto_zero_of_verticallyRegular_gammaBinet_scheduled_leaves
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hscalar : zetaCompletedExplicitFormulaPrimeNaturalScalarHermitian f)
    (hinverseGamma_scheduled :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
              f F.toContourFamily t)
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaArchimedeanContribution f +
            zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)))
    (hone :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            f F.toContourFamily (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue
          f F.toContourFamily.c))) :
      Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
              f F.toContourFamily (h.height_schedule.height u))
          atTop
          (𝓝 0) ∧
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
              f F.toContourFamily (h.height_schedule.height u))
          atTop
          (𝓝 0) ∧
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
              f F.toContourFamily (h.height_schedule.height u))
          atTop
          (𝓝 0) := by
  have hinverseGamma_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f :=
    zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integral_eq_archimedean_add_correction_of_verticallyRegular_gammaBinet_scheduled_tendsto
      f F h hcoh hinverseGamma_scheduled
  exact
    zetaCompletedExplicitFormulaVerticalChannelTransportRemainders_tendsto_zero_of_verticallyRegular_gammaBinet_owner
      f F h hcoh hscalar hinverseGamma_value hone

/-- Scheduled-leaf final transport-remainder package from the structural
two-face natural-time normalization. -/
theorem zetaCompletedExplicitFormulaVerticalChannelTransportRemainders_tendsto_zero_of_verticallyRegular_gammaBinet_scheduled_leaves_of_timeSummand_eq_twoFace
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (htwoFace :
      ∀ n : ℕ,
        zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n =
          zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n)
    (hinverseGamma_scheduled :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
              f F.toContourFamily t)
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaArchimedeanContribution f +
            zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)))
    (hone :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            f F.toContourFamily (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue
          f F.toContourFamily.c))) :
      Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
              f F.toContourFamily (h.height_schedule.height u))
          atTop
          (𝓝 0) ∧
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
              f F.toContourFamily (h.height_schedule.height u))
          atTop
          (𝓝 0) ∧
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
              f F.toContourFamily (h.height_schedule.height u))
          atTop
          (𝓝 0) := by
  have hscalar : zetaCompletedExplicitFormulaPrimeNaturalScalarHermitian f :=
    zetaCompletedExplicitFormulaPrimeNaturalScalarHermitian_of_timeSummand_eq_twoFaceBoundarySample
      f htwoFace
  exact
    zetaCompletedExplicitFormulaVerticalChannelTransportRemainders_tendsto_zero_of_verticallyRegular_gammaBinet_scheduled_leaves
      f F h hcoh hscalar hinverseGamma_scheduled hone

/-- Final transport-remainder package consuming the true owner analytic leaves
for the vertically regular left-prime and inverse-Gamma channels.  The remaining
explicit input is the right one-pole decay estimate. -/
theorem zetaCompletedExplicitFormulaVerticalChannelTransportRemainders_tendsto_zero_of_verticallyRegular_gammaBinet_ownerLeaves
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hscalar : zetaCompletedExplicitFormulaPrimeNaturalScalarHermitian f)
    (hone :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            f F.toContourFamily (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue
          f F.toContourFamily.c))) :
      Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
              f F.toContourFamily (h.height_schedule.height u))
          atTop
          (𝓝 0) ∧
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
              f F.toContourFamily (h.height_schedule.height u))
          atTop
          (𝓝 0) ∧
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
              f F.toContourFamily (h.height_schedule.height u))
          atTop
          (𝓝 0) :=
  let hinverseGamma_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f :=
    zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integral_eq_archimedean_add_correction_of_verticallyRegular_gammaBinet_ownerNormalization
      f F h hcoh
  zetaCompletedExplicitFormulaVerticalChannelTransportRemainders_tendsto_zero_of_verticallyRegular_gammaBinet_owner
    f F h hcoh hscalar hinverseGamma_value hone

/-- Owner-leaf final transport-remainder package from the structural two-face
natural-time normalization. -/
theorem zetaCompletedExplicitFormulaVerticalChannelTransportRemainders_tendsto_zero_of_verticallyRegular_gammaBinet_ownerLeaves_of_timeSummand_eq_twoFace
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (htwoFace :
      ∀ n : ℕ,
        zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n =
          zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n)
    (hone :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            f F.toContourFamily (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue
          f F.toContourFamily.c))) :
      Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
              f F.toContourFamily (h.height_schedule.height u))
          atTop
          (𝓝 0) ∧
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
              f F.toContourFamily (h.height_schedule.height u))
          atTop
          (𝓝 0) ∧
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
              f F.toContourFamily (h.height_schedule.height u))
          atTop
          (𝓝 0) := by
  have hscalar : zetaCompletedExplicitFormulaPrimeNaturalScalarHermitian f :=
    zetaCompletedExplicitFormulaPrimeNaturalScalarHermitian_of_timeSummand_eq_twoFaceBoundarySample
      f htwoFace
  exact
    zetaCompletedExplicitFormulaVerticalChannelTransportRemainders_tendsto_zero_of_verticallyRegular_gammaBinet_ownerLeaves
      f F h hcoh hscalar hone

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

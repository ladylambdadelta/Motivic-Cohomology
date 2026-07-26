import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.HorizontalContour.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.ScheduleGeometry
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.HolographicTraceSeparationParts.DiagonalResidualFunctionalParts.TraceScalarPrimitives
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TomographyRoot.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeSpectralMajorantSummability
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part01
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaAnalyticPackage.ScheduledLogDerivControl

/-!
# Completed prime residual source coordinates

This file owns the source contour/time transport facts used to make the
completed prime residual scalar vanish.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The trace gap vanishes once the two completed prime trace presentations
have been reconstructed as the same scalar. -/
theorem completedPrimeTraceFunctionalGap_eq_zero_of_traceEquality
    (f : ZetaAdmissibleFunction)
    (htrace :
      Complex.re
          (zetaCompletedExplicitFormulaPrimePowerContribution
            (convolutionAutocorrelation f)) =
        Complex.re
          (zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
            (convolutionAutocorrelation f))) :
    completedPrimeTraceFunctionalGap f = 0 :=
  let hsub :
      Complex.re
          (zetaCompletedExplicitFormulaPrimePowerContribution
            (convolutionAutocorrelation f)) -
        Complex.re
          (zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
            (convolutionAutocorrelation f)) = 0 :=
    sub_eq_zero.mpr htrace
  Eq.trans (completedPrimeTraceFunctionalGap_eq f) hsub

/-- The complex scalar residual between the time/log prime trace and the
contour-realized spectral prime trace. -/
noncomputable def completedPrimeTraceResidualComplexScalar
    (f : ZetaAdmissibleFunction) : ℂ :=
  ((completedPrimeTraceTimeScalar f -
      completedPrimeTraceSpectralScalar f : ℝ) : ℂ)

/-- The complex trace residual unfolds to the coerced real scalar difference. -/
theorem completedPrimeTraceResidualComplexScalar_eq
    (f : ZetaAdmissibleFunction) :
    completedPrimeTraceResidualComplexScalar f =
      ((completedPrimeTraceTimeScalar f -
          completedPrimeTraceSpectralScalar f : ℝ) : ℂ) :=
  Eq.refl (completedPrimeTraceResidualComplexScalar f)

/-- Equality of the physical and spectral prime off-diagonal channels gives
equality of the two real prime trace scalar presentations. -/
theorem completedPrimeTraceTimeScalar_eq_spectralScalar_of_channelEquality
    (f : ZetaAdmissibleFunction)
    (hchannel :
      completedPrimeOffDiagonalChannel f =
        completedSpectralPrimeOffDiagonalChannel f) :
    completedPrimeTraceTimeScalar f =
      completedPrimeTraceSpectralScalar f :=
  let htime :
      completedPrimeTraceTimeScalar f =
        completedPrimeOffDiagonalChannel f :=
    (completedPrimeTraceTimeScalar_eq f).trans
      (completedPrimeOffDiagonalChannel_eq_primePowerContribution_re f).symm
  let hspectral :
      completedSpectralPrimeOffDiagonalChannel f =
        completedPrimeTraceSpectralScalar f :=
    (completedSpectralPrimeOffDiagonalChannel_eq_spectralSampleContribution_re
      f).trans
      (completedPrimeTraceSpectralScalar_eq f).symm
  htime.trans (hchannel.trans hspectral)

/-- A visible summed contour/time transport datum kills the real prime trace
scalar difference. -/
theorem completedPrimeTraceTimeScalar_eq_spectralScalar_of_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f) :
    completedPrimeTraceTimeScalar f =
      completedPrimeTraceSpectralScalar f :=
  let hchannel :
      completedPrimeOffDiagonalChannel f =
        completedSpectralPrimeOffDiagonalChannel f :=
    completedPrimeOffDiagonalChannel_eq_completedSpectralPrimeOffDiagonalChannel_ownerSummedDistributionTransport_core
      f
      D
  completedPrimeTraceTimeScalar_eq_spectralScalar_of_channelEquality
    f
    hchannel

/-- A real equality of the two prime trace scalar presentations kills the
complex residual scalar. -/
theorem completedPrimeTraceResidualComplexScalar_eq_zero_of_timeSpectralEquality
    (f : ZetaAdmissibleFunction)
    (hscalar :
      completedPrimeTraceTimeScalar f =
        completedPrimeTraceSpectralScalar f) :
    completedPrimeTraceResidualComplexScalar f = 0 :=
  let hsub :
      completedPrimeTraceTimeScalar f -
          completedPrimeTraceSpectralScalar f = 0 :=
    sub_eq_zero.mpr hscalar
  let hcoerced :
      ((completedPrimeTraceTimeScalar f -
          completedPrimeTraceSpectralScalar f : ℝ) : ℂ) = 0 :=
    congrArg
      (fun value : ℝ => (value : ℂ))
      hsub
  Eq.trans (completedPrimeTraceResidualComplexScalar_eq f) hcoerced

/-- A visible summed contour/time transport datum kills the complex residual
between the two completed prime trace presentations. -/
theorem completedPrimeTraceResidualComplexScalar_eq_zero_of_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f) :
    completedPrimeTraceResidualComplexScalar f = 0 :=
  completedPrimeTraceResidualComplexScalar_eq_zero_of_timeSpectralEquality
    f
    (completedPrimeTraceTimeScalar_eq_spectralScalar_of_summedTransport
      f
      D)

/-- Horizontal decay order for the trace-reconstruction source package. -/
def completedPrimeContourTransportHorizontalDecayOrder_traceReconstruction_source :
    ℕ :=
  0

/-- The trace-reconstruction source contour-schedule geometry. -/
noncomputable def completedPrimeContourTransportScheduleGeometry_traceReconstruction_source :
    CompletedPrimeContourTransportScheduleGeometry where
  height_schedule := completedPrimeContourTransportHeightSchedule_owner
  horizontal_decay_order :=
    completedPrimeContourTransportHorizontalDecayOrder_traceReconstruction_source

/-- The complex horizontal residue-window error is the sampled horizontal
top-minus-bottom contour difference, at the residual-coordinate source layer. -/
theorem explicitFormulaFamilyHorizontalResidueWindowError_eq_sampledHorizontalDifferenceComplex_traceReconstruction_source
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    explicitFormulaFamilyHorizontalResidueWindowError
        (convolutionAutocorrelation f)
        completedPrimeContourTransportFamily
        (completedPrimeContourTransportHeightSchedule_owner.height (N : ℝ)) =
      sampledHorizontalDifferenceComplex N f :=
  let htop :
      zetaCompletedExplicitFormulaTopLineIntegral
          (convolutionAutocorrelation f)
          (completedPrimeContourTransportFamily.rectangle
            (completedPrimeContourTransportHeightSchedule_owner.height (N : ℝ))) =
        sampledHorizontalTopIntegral N f :=
    (sampledHorizontalTopIntegral_eq_topLineIntegral N f).symm
  let hbottom :
      zetaCompletedExplicitFormulaBottomLineIntegral
          (convolutionAutocorrelation f)
          (completedPrimeContourTransportFamily.rectangle
            (completedPrimeContourTransportHeightSchedule_owner.height (N : ℝ))) =
        sampledHorizontalBottomIntegral N f :=
    (sampledHorizontalBottomIntegral_eq_bottomLineIntegral N f).symm
  let hsub :
      zetaCompletedExplicitFormulaTopLineIntegral
          (convolutionAutocorrelation f)
          (completedPrimeContourTransportFamily.rectangle
            (completedPrimeContourTransportHeightSchedule_owner.height (N : ℝ))) -
        zetaCompletedExplicitFormulaBottomLineIntegral
          (convolutionAutocorrelation f)
          (completedPrimeContourTransportFamily.rectangle
            (completedPrimeContourTransportHeightSchedule_owner.height (N : ℝ))) =
        sampledHorizontalTopIntegral N f -
          sampledHorizontalBottomIntegral N f :=
    congrArg₂ HSub.hSub htop hbottom
  Eq.trans hsub
    (sampledHorizontalDifferenceComplex_eq_top_sub_bottom N f).symm

/-- Scheduled horizontal decay for the completed prime horizontal
residue-window error, at the residual-coordinate source layer. -/
theorem explicitFormulaFamilyHorizontalResidueWindowError_tendsto_zero_traceReconstruction_source
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hHorizontal :
      ExplicitFormulaScheduledHorizontalLogDerivControl
        (convolutionAutocorrelation f)
        completedPrimeContourTransportFamily
        completedPrimeContourTransportHeightSchedule_owner) :
    Filter.Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyHorizontalResidueWindowError
          (convolutionAutocorrelation f)
          completedPrimeContourTransportFamily
          (completedPrimeContourTransportHeightSchedule_owner.height u))
      Filter.atTop
      (nhds 0) :=
  let S : CompletedPrimeContourTransportScheduleGeometry :=
    completedPrimeContourTransportScheduleGeometry_traceReconstruction_source
  let hheight :
      S.height_schedule = completedPrimeContourTransportHeightSchedule_owner :=
    Eq.refl completedPrimeContourTransportHeightSchedule_owner
  let hsched :
      Filter.Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyHorizontalResidueWindowError
            (convolutionAutocorrelation f)
            completedPrimeContourTransportFamily
            (S.height_schedule.height u))
        Filter.atTop
        (nhds 0) :=
    let h :
        ExplicitFormulaScheduledFamilyAnalyticPackage
          (convolutionAutocorrelation f)
          completedPrimeContourTransportFamily :=
      completedPrimeContourTransportScheduledFamilyAnalyticPackage
        S
        f
        hPhi
        hHorizontal
    explicitFormulaFamilyHorizontalResidueWindowError_tendsto_zero_of_scheduledPackage
      (convolutionAutocorrelation f)
      completedPrimeContourTransportFamily
      h
      S.horizontal_decay_order
  let hfun :
      (fun u : ℝ =>
        explicitFormulaFamilyHorizontalResidueWindowError
          (convolutionAutocorrelation f)
          completedPrimeContourTransportFamily
          (S.height_schedule.height u)) =
        (fun u : ℝ =>
          explicitFormulaFamilyHorizontalResidueWindowError
            (convolutionAutocorrelation f)
            completedPrimeContourTransportFamily
            (completedPrimeContourTransportHeightSchedule_owner.height u)) :=
    congrArg
      (fun schedule :
        ExplicitFormulaCofinalHeightSchedule completedPrimeContourTransportFamily =>
        fun u : ℝ =>
          explicitFormulaFamilyHorizontalResidueWindowError
            (convolutionAutocorrelation f)
            completedPrimeContourTransportFamily
            (schedule.height u))
      hheight
  Eq.subst
    (motive := fun window : ℝ → ℂ =>
      Filter.Tendsto window Filter.atTop (nhds 0))
    hfun
    hsched

/-- Source convergence of the complex sampled horizontal prime contour
boundary difference. -/
theorem sampledHorizontalDifferenceComplex_tendsto_zero_traceReconstruction_source
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hHorizontal :
      ExplicitFormulaScheduledHorizontalLogDerivControl
        (convolutionAutocorrelation f)
        completedPrimeContourTransportFamily
        completedPrimeContourTransportHeightSchedule_owner) :
    Filter.Tendsto
      (fun N : ℕ => sampledHorizontalDifferenceComplex N f)
      Filter.atTop
      (nhds 0) :=
  let hcomplex :
      Filter.Tendsto
        (fun N : ℕ =>
          explicitFormulaFamilyHorizontalResidueWindowError
            (convolutionAutocorrelation f)
            completedPrimeContourTransportFamily
            (completedPrimeContourTransportHeightSchedule_owner.height (N : ℝ)))
        Filter.atTop
        (nhds 0) :=
    (explicitFormulaFamilyHorizontalResidueWindowError_tendsto_zero_traceReconstruction_source
      f hPhi hHorizontal).comp tendsto_natCast_atTop_atTop
  let hfun :
      (fun N : ℕ => sampledHorizontalDifferenceComplex N f) =
        (fun N : ℕ =>
          explicitFormulaFamilyHorizontalResidueWindowError
            (convolutionAutocorrelation f)
            completedPrimeContourTransportFamily
            (completedPrimeContourTransportHeightSchedule_owner.height (N : ℝ))) :=
    funext
      (fun N : ℕ =>
      (explicitFormulaFamilyHorizontalResidueWindowError_eq_sampledHorizontalDifferenceComplex_traceReconstruction_source
        N
        f).symm)
  Eq.subst
    (motive := fun window : ℕ → ℂ =>
      Filter.Tendsto window Filter.atTop (nhds 0))
    hfun.symm
    hcomplex

/-- Source convergence of the sampled horizontal prime contour boundary
difference. -/
theorem sampledHorizontalDifference_tendsto_zero_traceReconstruction_source
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hHorizontal :
      ExplicitFormulaScheduledHorizontalLogDerivControl
        (convolutionAutocorrelation f)
        completedPrimeContourTransportFamily
        completedPrimeContourTransportHeightSchedule_owner) :
    Filter.Tendsto
      (fun N : ℕ => sampledHorizontalDifference N f)
      Filter.atTop
      (nhds 0) :=
  let hcomplex :
      Filter.Tendsto
        (fun N : ℕ => sampledHorizontalDifferenceComplex N f)
        Filter.atTop
        (nhds 0) :=
    sampledHorizontalDifferenceComplex_tendsto_zero_traceReconstruction_source
      f hPhi hHorizontal
  let hre :
      Filter.Tendsto
        (fun N : ℕ => Complex.re (sampledHorizontalDifferenceComplex N f))
        Filter.atTop
        (nhds (Complex.re 0)) :=
    ((RCLike.reCLM : ℂ →L[ℝ] ℝ).continuous.tendsto 0).comp hcomplex
  let hzero : Complex.re (0 : ℂ) = 0 :=
    Complex.zero_re
  let hfun :
      (fun N : ℕ => sampledHorizontalDifference N f) =
        (fun N : ℕ => Complex.re (sampledHorizontalDifferenceComplex N f)) :=
    funext
      (fun N : ℕ => sampledHorizontalDifference_eq_complex_re N f)
  Eq.subst
    (motive := fun window : ℕ → ℝ =>
      Filter.Tendsto window Filter.atTop (nhds 0))
    hfun.symm
    (Eq.subst
      (motive := fun limit : ℝ =>
        Filter.Tendsto
          (fun N : ℕ => Complex.re (sampledHorizontalDifferenceComplex N f))
          Filter.atTop
          (nhds limit))
      hzero
      hre)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

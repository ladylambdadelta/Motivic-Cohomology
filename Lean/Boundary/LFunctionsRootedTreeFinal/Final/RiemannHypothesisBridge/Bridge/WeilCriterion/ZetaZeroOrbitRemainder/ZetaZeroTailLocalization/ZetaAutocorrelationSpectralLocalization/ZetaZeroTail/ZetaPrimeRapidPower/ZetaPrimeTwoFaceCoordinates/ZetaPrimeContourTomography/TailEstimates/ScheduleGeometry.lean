import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.CoordinateLedger.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaAnalyticPackage.ScheduledConcreteLogDerivControl
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part01

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Geometric schedule data for the canonical prime contour-transport family.

This record contains only contour geometry.  In particular, it does not contain the
prime-distribution reconstruction that the contour argument is intended to prove. -/
structure CompletedPrimeContourTransportScheduleGeometry where
  height_schedule : ExplicitFormulaCofinalHeightSchedule completedPrimeContourTransportFamily
  horizontal_decay_order : ℕ

/-- Combined geometric schedule and finite reconstruction data. -/
structure CompletedPrimeContourTransportScheduledFamily extends
    CompletedPrimeContourTransportScheduleGeometry where
  summedTransport :
    ∀ f : ZetaAdmissibleFunction,
      CompletedSummedPrimeContourTimeTransport f

/-- Forget reconstruction data and retain only the contour geometry. -/
def CompletedPrimeContourTransportScheduledFamily.toScheduleGeometry
    (S : CompletedPrimeContourTransportScheduledFamily) :
    CompletedPrimeContourTransportScheduleGeometry :=
  S.toCompletedPrimeContourTransportScheduleGeometry

/-- Concrete separated factor-bound data on the completed-prime scheduled horizontal carrier. -/
structure CompletedPrimeContourTransportConcreteFactorData
    (S : CompletedPrimeContourTransportScheduleGeometry) where
  /-- Shared scheduled horizontal carrier. -/
  carrier :
    CompletedZetaZeroExcisedStrip
      (min completedPrimeContourTransportFamily.c
          (1 - completedPrimeContourTransportFamily.c))
      (max completedPrimeContourTransportFamily.c
          (1 - completedPrimeContourTransportFamily.c))
  /-- Top horizontal edge membership in the shared carrier. -/
  top_mem :
    ∀ u x : ℝ,
      x ∈ Set.uIcc completedPrimeContourTransportFamily.c
          (1 - completedPrimeContourTransportFamily.c) →
        zetaCompletedExplicitFormulaTopPath
          (completedPrimeContourTransportFamily.rectangle
            (S.height_schedule.height u)) x ∈ carrier.carrier
  /-- Bottom horizontal edge membership in the shared carrier. -/
  bottom_mem :
    ∀ u x : ℝ,
      x ∈ Set.uIcc completedPrimeContourTransportFamily.c
          (1 - completedPrimeContourTransportFamily.c) →
        zetaCompletedExplicitFormulaBottomPath
          (completedPrimeContourTransportFamily.rectangle
            (S.height_schedule.height u)) x ∈ carrier.carrier
  /-- Zeta-side bounds on the scheduled carrier. -/
  zeta_data :
    CompletedZetaZeroExcisedStrip.ZetaSideBoundData carrier
  /-- Inverse-Gamma bounds on the scheduled carrier. -/
  gamma_data :
    CompletedZetaZeroExcisedStrip.InverseGammaBoundData carrier

def CompletedPrimeContourTransportConcreteFactorData.ofFactorBoundData
    {S : CompletedPrimeContourTransportScheduleGeometry}
    (carrier :
      CompletedZetaZeroExcisedStrip
        (min completedPrimeContourTransportFamily.c
            (1 - completedPrimeContourTransportFamily.c))
        (max completedPrimeContourTransportFamily.c
            (1 - completedPrimeContourTransportFamily.c)))
    (top_mem :
      ∀ u x : ℝ,
        x ∈ Set.uIcc completedPrimeContourTransportFamily.c
            (1 - completedPrimeContourTransportFamily.c) →
          zetaCompletedExplicitFormulaTopPath
            (completedPrimeContourTransportFamily.rectangle
              (S.height_schedule.height u)) x ∈ carrier.carrier)
    (bottom_mem :
      ∀ u x : ℝ,
        x ∈ Set.uIcc completedPrimeContourTransportFamily.c
            (1 - completedPrimeContourTransportFamily.c) →
          zetaCompletedExplicitFormulaBottomPath
            (completedPrimeContourTransportFamily.rectangle
              (S.height_schedule.height u)) x ∈ carrier.carrier)
    (factor_data :
      CompletedZetaZeroExcisedStrip.FactorBoundData carrier) :
    CompletedPrimeContourTransportConcreteFactorData S :=
  { carrier := carrier
    top_mem := top_mem
    bottom_mem := bottom_mem
    zeta_data := factor_data.zetaSide
    gamma_data := factor_data.inverseGamma }

def CompletedPrimeContourTransportConcreteFactorData.toFactorBoundData
    {S : CompletedPrimeContourTransportScheduleGeometry}
    (D : CompletedPrimeContourTransportConcreteFactorData S) :
    CompletedZetaZeroExcisedStrip.FactorBoundData D.carrier :=
  CompletedZetaZeroExcisedStrip.FactorBoundData.ofParts
    D.zeta_data
    D.gamma_data

/-- Concrete factor data construct the scheduled horizontal log-derivative control. -/
def CompletedPrimeContourTransportConcreteFactorData.toScheduledHorizontalLogDerivControl
    {S : CompletedPrimeContourTransportScheduleGeometry}
    (D : CompletedPrimeContourTransportConcreteFactorData S)
    (f : ZetaAdmissibleFunction) :
    ExplicitFormulaScheduledHorizontalLogDerivControl
      (convolutionAutocorrelation f)
      completedPrimeContourTransportFamily
      S.height_schedule :=
  ExplicitFormulaScheduledHorizontalLogDerivControl.ofFactorBoundData
    D.carrier D.top_mem D.bottom_mem D.toFactorBoundData

/-- Scheduled contour data construct the visible summed prime distribution transport datum
consumed by the distribution-transport owner theorem. -/
def completedSummedPrimeContourTimeTransport_of_scheduledContourFamily
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction) :
    CompletedSummedPrimeContourTimeTransport f :=
  S.summedTransport f

/-- The scheduled-family transport stream has the time-window presentation. -/
theorem completedSummedPrimeContourTimeTransport_of_scheduledContourFamily_timeWindow
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction)
    (N : ℕ) :
    (completedSummedPrimeContourTimeTransport_of_scheduledContourFamily S f).timeWindow N =
      finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) :=
  (completedSummedPrimeContourTimeTransport_of_scheduledContourFamily
    S f).timeWindow_eq N

/-- The scheduled-family transport stream has the contour-window presentation. -/
theorem completedSummedPrimeContourTimeTransport_of_scheduledContourFamily_contourWindow
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction)
    (N : ℕ) :
    (completedSummedPrimeContourTimeTransport_of_scheduledContourFamily S f).contourWindow N =
      finitePrimeContourRealizedTimeDistributionWindow N (convolutionAutocorrelation f) :=
  (completedSummedPrimeContourTimeTransport_of_scheduledContourFamily
    S f).contourWindow_eq N

/-- Scheduled contour data route the completed prime distribution transport theorem through
the explicit finite-window reconstruction datum. -/
theorem completedPrimeDistributionTransport_timePairing_eq_contourRealizedPairing_of_scheduledContourFamily
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction) :
  completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
      completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f) :=
  completedPrimeDistributionTransport_timePairing_eq_contourRealizedPairing_ownerSummedTransport
    f
    (completedSummedPrimeContourTimeTransport_of_scheduledContourFamily S f)

/-- The scheduled contour-family object associated to prime contour transport data. -/
def CompletedPrimeContourTransportScheduleGeometry.toScheduledContourFamily
    (S : CompletedPrimeContourTransportScheduleGeometry) :
    ExplicitFormulaScheduledContourFamily :=
  { toContourFamily := completedPrimeContourTransportFamily
    height_schedule := S.height_schedule }

/-- The scheduled contour-family projection of prime transport data is the canonical
prime contour-transport family. -/
theorem CompletedPrimeContourTransportScheduleGeometry.toScheduledContourFamily_toContourFamily
    (S : CompletedPrimeContourTransportScheduleGeometry) :
    S.toScheduledContourFamily.toContourFamily =
      completedPrimeContourTransportFamily :=
  Eq.refl completedPrimeContourTransportFamily

/-- The scheduled contour-family object associated to prime transport data carries the
stored prime transport height schedule. -/
theorem CompletedPrimeContourTransportScheduleGeometry.toScheduledContourFamily_height_schedule
    (S : CompletedPrimeContourTransportScheduleGeometry) :
    S.toScheduledContourFamily.height_schedule =
      S.height_schedule :=
  Eq.refl S.height_schedule

/-- Family analytic package for the convolution autocorrelation and the completed prime
contour-transport family, using supplied scheduled contour data. -/
noncomputable def completedPrimeContourTransportFamilyAnalyticPackage
    (S : CompletedPrimeContourTransportScheduleGeometry)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    ExplicitFormulaFamilyAnalyticPackage
      (convolutionAutocorrelation f)
      completedPrimeContourTransportFamily :=
  { phi_control := hPhi
    logderiv_control := hLog
    height_schedule := S.height_schedule }

/-- The prime contour-transport package has the supplied cofinal height schedule as its
schedule field. -/
theorem completedPrimeContourTransportFamilyAnalyticPackage_height_schedule
    (S : CompletedPrimeContourTransportScheduleGeometry)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    (completedPrimeContourTransportFamilyAnalyticPackage S f hPhi hLog).height_schedule =
      S.height_schedule :=
  Eq.refl S.height_schedule

/-- The prime contour-transport package is the scheduled-contour-family analytic package
for the scheduled prime transport object when the same analytic controls are supplied. -/
theorem completedPrimeContourTransportFamilyAnalyticPackage_eq_scheduledContourFamilyPackage_of_controls
    (S : CompletedPrimeContourTransportScheduleGeometry)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    completedPrimeContourTransportFamilyAnalyticPackage S f hPhi hLog =
      explicitFormulaFamilyAnalyticPackage_of_scheduledContourFamily hPhi hLog
        S.toScheduledContourFamily :=
  Eq.refl (completedPrimeContourTransportFamilyAnalyticPackage S f hPhi hLog)

/-- Narrow scheduled analytic package for the convolution autocorrelation and the completed
prime contour-transport family. -/
noncomputable def completedPrimeContourTransportScheduledFamilyAnalyticPackage
    (S : CompletedPrimeContourTransportScheduleGeometry)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hHorizontal :
      ExplicitFormulaScheduledHorizontalLogDerivControl
        (convolutionAutocorrelation f)
        completedPrimeContourTransportFamily
        S.height_schedule) :
    ExplicitFormulaScheduledFamilyAnalyticPackage
      (convolutionAutocorrelation f)
      completedPrimeContourTransportFamily :=
  { phi_control := hPhi
    height_schedule := S.height_schedule
    horizontal_logderiv_control := hHorizontal }

/-- The finite residue shadow is pointwise the real part of the scheduled
horizontal window-error term. -/
theorem finitePrimeHorizontalResidueShadowAt_fun_eq_horizontalResidueWindowError_re
    (S : CompletedPrimeContourTransportScheduleGeometry)
    (f : ZetaAdmissibleFunction) :
    (fun N : ℕ => finitePrimeHorizontalResidueShadowAt S.height_schedule N f) =
      (fun N : ℕ =>
        Complex.re
          (explicitFormulaFamilyHorizontalResidueWindowError
            (convolutionAutocorrelation f)
            completedPrimeContourTransportFamily
            (S.height_schedule.height (N : ℝ)))) :=
  funext
    (fun N =>
      finitePrimeHorizontalResidueShadowAt_eq_horizontalResidueWindowError_re
        S.height_schedule
        N
        f)

/-- Complex horizontal window-error convergence implies real-part convergence
to the real zero. -/
theorem horizontalResidueWindowError_re_tendsto_zero_of_complex_tendsto_zero
    (S : CompletedPrimeContourTransportScheduleGeometry)
    (f : ZetaAdmissibleFunction)
    (hcomplex :
      Tendsto
        (fun N : ℕ =>
          explicitFormulaFamilyHorizontalResidueWindowError
            (convolutionAutocorrelation f)
            completedPrimeContourTransportFamily
            (S.height_schedule.height (N : ℝ)))
        atTop
        (𝓝 0)) :
    Tendsto
      (fun N : ℕ =>
        Complex.re
          (explicitFormulaFamilyHorizontalResidueWindowError
            (convolutionAutocorrelation f)
            completedPrimeContourTransportFamily
            (S.height_schedule.height (N : ℝ))))
      atTop
      (𝓝 0) :=
  Eq.subst
    (motive := fun x : ℝ =>
      Tendsto
        (fun N : ℕ =>
          Complex.re
            (explicitFormulaFamilyHorizontalResidueWindowError
              (convolutionAutocorrelation f)
              completedPrimeContourTransportFamily
              (S.height_schedule.height (N : ℝ))))
        atTop
        (𝓝 x))
    Complex.zero_re
    ((RCLike.continuous_re.tendsto (0 : ℂ)).comp hcomplex)

/-- Real-part horizontal window-error convergence transports to the residue
shadow convergence. -/
theorem finitePrimeHorizontalResidueShadowAt_tendsto_zero_of_horizontalResidueWindowError_re
    (S : CompletedPrimeContourTransportScheduleGeometry)
    (f : ZetaAdmissibleFunction)
    (hre :
      Tendsto
        (fun N : ℕ =>
          Complex.re
            (explicitFormulaFamilyHorizontalResidueWindowError
              (convolutionAutocorrelation f)
              completedPrimeContourTransportFamily
              (S.height_schedule.height (N : ℝ))))
        atTop
        (𝓝 0)) :
    Tendsto
      (fun N : ℕ => finitePrimeHorizontalResidueShadowAt S.height_schedule N f)
      atTop
      (𝓝 0) :=
  Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    (finitePrimeHorizontalResidueShadowAt_fun_eq_horizontalResidueWindowError_re
      S
      f).symm
    hre

/-- The narrow scheduled package gives complex horizontal window-error
convergence along natural heights. -/
theorem horizontalResidueWindowError_tendsto_zero_of_scheduledPackage_nat
    (S : CompletedPrimeContourTransportScheduleGeometry)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hHorizontal :
      ExplicitFormulaScheduledHorizontalLogDerivControl
        (convolutionAutocorrelation f)
        completedPrimeContourTransportFamily
        S.height_schedule) :
    Tendsto
      (fun N : ℕ =>
        explicitFormulaFamilyHorizontalResidueWindowError
          (convolutionAutocorrelation f)
          completedPrimeContourTransportFamily
          (S.height_schedule.height (N : ℝ)))
      atTop
      (𝓝 0) :=
  (explicitFormulaFamilyHorizontalResidueWindowError_tendsto_zero_of_scheduledPackage
    (convolutionAutocorrelation f)
    completedPrimeContourTransportFamily
    (completedPrimeContourTransportScheduledFamilyAnalyticPackage
      S
      f
      hPhi
      hHorizontal)
    S.horizontal_decay_order).comp tendsto_natCast_atTop_atTop

/-- The family package height schedule transports the horizontal window-error
stream to the schedule stored in the geometric data. -/
theorem completedPrimeContourTransportPackage_horizontalResidueWindowError_fun_eq_ownerSchedule
    (S : CompletedPrimeContourTransportScheduleGeometry)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    (fun u : ℝ =>
      explicitFormulaFamilyHorizontalResidueWindowError
        (convolutionAutocorrelation f)
        completedPrimeContourTransportFamily
        ((completedPrimeContourTransportFamilyAnalyticPackage
          S f hPhi hLog).height_schedule.height u)) =
      (fun u : ℝ =>
        explicitFormulaFamilyHorizontalResidueWindowError
          (convolutionAutocorrelation f)
          completedPrimeContourTransportFamily
          (S.height_schedule.height u)) :=
  congrArg
    (fun schedule :
      ExplicitFormulaCofinalHeightSchedule completedPrimeContourTransportFamily =>
      fun u : ℝ =>
        explicitFormulaFamilyHorizontalResidueWindowError
          (convolutionAutocorrelation f)
          completedPrimeContourTransportFamily
          (schedule.height u))
    (completedPrimeContourTransportFamilyAnalyticPackage_height_schedule
      S
      f
      hPhi
      hLog)

/-- The full family package gives complex horizontal window-error convergence
along natural heights after height-schedule transport. -/
theorem horizontalResidueWindowError_tendsto_zero_of_package_nat
    (S : CompletedPrimeContourTransportScheduleGeometry)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    Tendsto
      (fun N : ℕ =>
        explicitFormulaFamilyHorizontalResidueWindowError
          (convolutionAutocorrelation f)
          completedPrimeContourTransportFamily
          (S.height_schedule.height (N : ℝ)))
      atTop
      (𝓝 0) :=
  (Eq.subst
    (motive := fun v : ℝ → ℂ => Tendsto v atTop (𝓝 0))
    (completedPrimeContourTransportPackage_horizontalResidueWindowError_fun_eq_ownerSchedule
      S
      f
      hPhi
      hLog)
    (explicitFormulaFamilyHorizontalResidueWindowError_tendsto_zero_of_scheduledCarrier
      (convolutionAutocorrelation f)
      completedPrimeContourTransportFamily
      (completedPrimeContourTransportFamilyAnalyticPackage S f hPhi hLog)
      S.horizontal_decay_order)).comp tendsto_natCast_atTop_atTop

/-- The finite horizontal residue shadow along the supplied schedule tends to zero
by scheduled horizontal decay from a narrow scheduled analytic package. -/
theorem finitePrimeHorizontalResidueShadowAt_tendsto_zero_of_scheduledPackage
    (S : CompletedPrimeContourTransportScheduleGeometry)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hHorizontal :
      ExplicitFormulaScheduledHorizontalLogDerivControl
        (convolutionAutocorrelation f)
        completedPrimeContourTransportFamily
        S.height_schedule) :
    Tendsto
      (fun N : ℕ => finitePrimeHorizontalResidueShadowAt S.height_schedule N f)
      atTop
      (𝓝 0) :=
  finitePrimeHorizontalResidueShadowAt_tendsto_zero_of_horizontalResidueWindowError_re
    S
    f
    (horizontalResidueWindowError_re_tendsto_zero_of_complex_tendsto_zero
      S
      f
      (horizontalResidueWindowError_tendsto_zero_of_scheduledPackage_nat
        S
        f
        hPhi
        hHorizontal))

/-- The finite horizontal residue shadow along the supplied schedule tends to zero
by scheduled horizontal decay from an explicit family analytic package. -/
theorem finitePrimeHorizontalResidueShadowAt_tendsto_zero_of_package
    (S : CompletedPrimeContourTransportScheduleGeometry)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    Tendsto
      (fun N : ℕ => finitePrimeHorizontalResidueShadowAt S.height_schedule N f)
      atTop
      (𝓝 0) :=
  finitePrimeHorizontalResidueShadowAt_tendsto_zero_of_horizontalResidueWindowError_re
    S
    f
    (horizontalResidueWindowError_re_tendsto_zero_of_complex_tendsto_zero
      S
      f
      (horizontalResidueWindowError_tendsto_zero_of_package_nat
        S
        f
        hPhi
        hLog))

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

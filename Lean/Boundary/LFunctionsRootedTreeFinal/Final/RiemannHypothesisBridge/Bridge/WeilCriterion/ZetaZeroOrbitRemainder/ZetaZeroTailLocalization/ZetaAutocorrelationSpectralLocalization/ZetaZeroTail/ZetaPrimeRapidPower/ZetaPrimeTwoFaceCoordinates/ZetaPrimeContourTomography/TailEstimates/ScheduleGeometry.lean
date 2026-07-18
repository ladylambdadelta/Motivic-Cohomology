import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.CoordinateTail

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
  horizontal_excisedStrip :
    CompletedZetaZeroExcisedStrip
      (min completedPrimeContourTransportFamily.c
        (1 - completedPrimeContourTransportFamily.c))
      (max completedPrimeContourTransportFamily.c
        (1 - completedPrimeContourTransportFamily.c))
  horizontal_top_mem :
    ∀ (T x : ℝ),
      x ∈ Set.uIcc completedPrimeContourTransportFamily.c
          (1 - completedPrimeContourTransportFamily.c) →
        zetaCompletedExplicitFormulaTopPath
            (completedPrimeContourTransportFamily.rectangle T) x ∈
          horizontal_excisedStrip.carrier
  horizontal_bottom_mem :
    ∀ (T x : ℝ),
      x ∈ Set.uIcc completedPrimeContourTransportFamily.c
          (1 - completedPrimeContourTransportFamily.c) →
        zetaCompletedExplicitFormulaBottomPath
            (completedPrimeContourTransportFamily.rectangle T) x ∈
          horizontal_excisedStrip.carrier
  horizontal_decay_order : ℕ

/-- Combined geometric schedule and finite reconstruction data. -/
structure CompletedPrimeContourTransportScheduledFamily extends
    CompletedPrimeContourTransportScheduleGeometry where
  primeDistributionReconstruction :
    ∀ f : ZetaAdmissibleFunction,
      CompletedFiniteWindowPrimeDistributionReconstruction f

/-- Forget reconstruction data and retain only the contour geometry. -/
def CompletedPrimeContourTransportScheduledFamily.toScheduleGeometry
    (S : CompletedPrimeContourTransportScheduledFamily) :
    CompletedPrimeContourTransportScheduleGeometry :=
  S.toCompletedPrimeContourTransportScheduleGeometry

/-- Scheduled contour data construct the completed finite-window prime distribution
reconstruction datum consumed by the distribution-transport owner theorem. -/
def completedFiniteWindowPrimeDistributionReconstruction_of_scheduledContourFamily
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction) :
    CompletedFiniteWindowPrimeDistributionReconstruction f :=
  S.primeDistributionReconstruction f

/-- The scheduled-family reconstruction stream is the common finite-window stream stored
in the scheduled contour data. -/
theorem completedFiniteWindowPrimeDistributionReconstruction_of_scheduledContourFamily_finiteWindow
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction) :
    (completedFiniteWindowPrimeDistributionReconstruction_of_scheduledContourFamily S f).finiteWindow =
      (S.primeDistributionReconstruction f).finiteWindow := by
  rfl

/-- The scheduled-family reconstruction stream has the time-window presentation. -/
theorem completedFiniteWindowPrimeDistributionReconstruction_of_scheduledContourFamily_timeWindow
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction)
    (N : ℕ) :
    (completedFiniteWindowPrimeDistributionReconstruction_of_scheduledContourFamily S f).finiteWindow N =
      finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) :=
  (completedFiniteWindowPrimeDistributionReconstruction_of_scheduledContourFamily
    S f).finiteWindow_eq_timeWindow N

/-- The scheduled-family reconstruction stream has the contour-window presentation. -/
theorem completedFiniteWindowPrimeDistributionReconstruction_of_scheduledContourFamily_contourWindow
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction)
    (N : ℕ) :
    (completedFiniteWindowPrimeDistributionReconstruction_of_scheduledContourFamily S f).finiteWindow N =
      finitePrimeContourRealizedTimeDistributionWindow N (convolutionAutocorrelation f) :=
  (completedFiniteWindowPrimeDistributionReconstruction_of_scheduledContourFamily
    S f).finiteWindow_eq_contourWindow N

/-- The scheduled-family time finite windows converge to the completed time pairing. -/
theorem completedFiniteWindowPrimeDistributionReconstruction_of_scheduledContourFamily_timeWindow_tendsto
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f))
      atTop
      (𝓝 (completedPrimeTimeDistributionPairing (convolutionAutocorrelation f))) :=
  (completedFiniteWindowPrimeDistributionReconstruction_of_scheduledContourFamily
    S f).timeWindow_tendsto

/-- The scheduled-family contour finite windows converge to the completed contour
pairing. -/
theorem completedFiniteWindowPrimeDistributionReconstruction_of_scheduledContourFamily_contourWindow_tendsto
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeContourRealizedTimeDistributionWindow N (convolutionAutocorrelation f))
      atTop
      (𝓝
        (completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f))) :=
  (completedFiniteWindowPrimeDistributionReconstruction_of_scheduledContourFamily
    S f).contourWindow_tendsto

/-- Scheduled contour data route the completed prime distribution transport theorem through
the explicit finite-window reconstruction datum. -/
theorem completedPrimeDistributionTransport_timePairing_eq_contourRealizedPairing_of_scheduledContourFamily
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction) :
    completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
      completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f) :=
  completedPrimeDistributionTransport_timePairing_eq_contourRealizedPairing_ownerFiniteWindowTransport
    f
    (completedFiniteWindowPrimeDistributionReconstruction_of_scheduledContourFamily S f)

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
      completedPrimeContourTransportFamily := by
  rfl

/-- The scheduled contour-family object associated to prime transport data carries the
stored prime transport height schedule. -/
theorem CompletedPrimeContourTransportScheduleGeometry.toScheduledContourFamily_height_schedule
    (S : CompletedPrimeContourTransportScheduleGeometry) :
    S.toScheduledContourFamily.height_schedule =
      S.height_schedule := by
  rfl

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
      S.height_schedule := by
  rfl

/-- The prime contour-transport package is the scheduled-contour-family analytic package
for the scheduled prime transport object when the same analytic controls are supplied. -/
theorem completedPrimeContourTransportFamilyAnalyticPackage_eq_scheduledContourFamilyPackage_of_controls
    (S : CompletedPrimeContourTransportScheduleGeometry)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    completedPrimeContourTransportFamilyAnalyticPackage S f hPhi hLog =
      explicitFormulaFamilyAnalyticPackage_of_scheduledContourFamily hPhi hLog
        S.toScheduledContourFamily := by
  rfl

/-- The finite horizontal residue shadow tends to zero by horizontal decay from an explicit
family analytic package. -/
theorem finitePrimeHorizontalResidueShadow_tendsto_zero_of_package
    (f : ZetaAdmissibleFunction)
    (h : ExplicitFormulaFamilyAnalyticPackage
      (convolutionAutocorrelation f)
      completedPrimeContourTransportFamily)
    (E : CompletedZetaZeroExcisedStrip
      (min completedPrimeContourTransportFamily.c
        (1 - completedPrimeContourTransportFamily.c))
      (max completedPrimeContourTransportFamily.c
        (1 - completedPrimeContourTransportFamily.c)))
    (hTopMem :
      ∀ (T x : ℝ),
        x ∈ Set.uIcc completedPrimeContourTransportFamily.c
            (1 - completedPrimeContourTransportFamily.c) →
          zetaCompletedExplicitFormulaTopPath
              (completedPrimeContourTransportFamily.rectangle T) x ∈
            E.carrier)
    (hBottomMem :
      ∀ (T x : ℝ),
        x ∈ Set.uIcc completedPrimeContourTransportFamily.c
            (1 - completedPrimeContourTransportFamily.c) →
          zetaCompletedExplicitFormulaBottomPath
              (completedPrimeContourTransportFamily.rectangle T) x ∈
            E.carrier)
    (M : ℕ) :
    Tendsto
      (fun N : ℕ => finitePrimeHorizontalResidueShadow N f)
      atTop
      (𝓝 0) := by
  have hcomplex :
      Tendsto
        (fun N : ℕ =>
          explicitFormulaFamilyHorizontalResidueWindowError
            (convolutionAutocorrelation f)
            completedPrimeContourTransportFamily
            (N : ℝ))
        atTop
        (𝓝 0) := by
    exact
        (explicitFormulaFamilyHorizontalResidueWindowError_tendsto_zero
          (convolutionAutocorrelation f)
          completedPrimeContourTransportFamily
          h
          E
          hTopMem
          hBottomMem
          M).comp tendsto_natCast_atTop_atTop
  have hre :
      Tendsto
        (fun N : ℕ =>
          Complex.re
            (explicitFormulaFamilyHorizontalResidueWindowError
                (convolutionAutocorrelation f)
                completedPrimeContourTransportFamily
                (N : ℝ)))
        atTop
        (𝓝 (Complex.re 0)) :=
    (RCLike.continuous_re.tendsto (0 : ℂ)).comp hcomplex
  have hzero : Complex.re (0 : ℂ) = (0 : ℝ) :=
    Complex.zero_re
  have hshadow :
      (fun N : ℕ => finitePrimeHorizontalResidueShadow N f) =
        (fun N : ℕ =>
          Complex.re
            (explicitFormulaFamilyHorizontalResidueWindowError
              (convolutionAutocorrelation f)
              completedPrimeContourTransportFamily
              (N : ℝ))) := by
    funext N
    exact finitePrimeHorizontalResidueShadow_eq_horizontalResidueWindowError_re
      N f
  exact Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hshadow.symm
    (Eq.subst
      (motive := fun x : ℝ =>
        Tendsto
          (fun N : ℕ =>
            Complex.re
              (explicitFormulaFamilyHorizontalResidueWindowError
                (convolutionAutocorrelation f)
                completedPrimeContourTransportFamily
                (N : ℝ)))
          atTop
          (𝓝 x))
      hzero
      hre)

/-- The finite horizontal residue shadow tends to zero by supplied scheduled prime
contour-transport data. -/
theorem finitePrimeHorizontalResidueShadow_tendsto_zero_ownerTailEstimate
    (S : CompletedPrimeContourTransportScheduleGeometry)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    Tendsto
      (fun N : ℕ => finitePrimeHorizontalResidueShadow N f)
      atTop
      (𝓝 0) := by
  exact
    finitePrimeHorizontalResidueShadow_tendsto_zero_of_package
      f
      (completedPrimeContourTransportFamilyAnalyticPackage S f hPhi hLog)
      S.horizontal_excisedStrip
      S.horizontal_top_mem
      S.horizontal_bottom_mem
      S.horizontal_decay_order

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

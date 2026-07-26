import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.ConcreteOwner

/-!
# Tomographic majorant convergence

This file owns the first GNS-normalization tail peel: the finite-window
tomographic majorant is proved schedule-parametrically, and the concrete theorem
is only a specialization wrapper.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The explicit finite-window tail majorant tends to zero before specializing the height
schedule. -/
theorem finitePrimeContourTransportTomographicErrorRemainderMajorantAt_tendsto_zero_core
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hHorizontal :
      ExplicitFormulaScheduledHorizontalLogDerivControl
        (convolutionAutocorrelation f)
        completedPrimeContourTransportFamily
        S.height_schedule) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeContourTransportTomographicErrorRemainderMajorantAt
          S.height_schedule N f)
      atTop
      (𝓝 0) := by
  exact
    finitePrimeContourTransportTomographicErrorRemainderMajorantAt_tendsto_zero
      S
      f
      hPhi
      hHorizontal

/-- The explicit finite-window tail majorant tends to zero after specializing to the
canonical concrete height schedule. -/
theorem finitePrimeContourTransportTomographicErrorRemainderMajorant_tendsto_zero_core
    (S : CompletedPrimeContourTransportScheduledFamily)
    (hheight :
      S.height_schedule = completedPrimeContourTransportHeightSchedule_owner)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hHorizontal :
      ExplicitFormulaScheduledHorizontalLogDerivControl
        (convolutionAutocorrelation f)
        completedPrimeContourTransportFamily
        S.height_schedule) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeContourTransportTomographicErrorRemainderMajorant N f)
      atTop
      (𝓝 0) := by
  have hparametric :
      Tendsto
        (fun N : ℕ =>
          finitePrimeContourTransportTomographicErrorRemainderMajorantAt
            S.height_schedule N f)
        atTop
        (𝓝 0) :=
    finitePrimeContourTransportTomographicErrorRemainderMajorantAt_tendsto_zero_core
      S
      f
      hPhi
      hHorizontal
  have hfun :
      (fun N : ℕ =>
        finitePrimeContourTransportTomographicErrorRemainderMajorantAt
          S.height_schedule N f) =
        (fun N : ℕ =>
          finitePrimeContourTransportTomographicErrorRemainderMajorant N f) := by
    funext N
    have hschedule :
        finitePrimeContourTransportTomographicErrorRemainderMajorantAt
            S.height_schedule N f =
          finitePrimeContourTransportTomographicErrorRemainderMajorantAt
            completedPrimeContourTransportHeightSchedule_owner N f :=
      congrArg
        (fun heightSchedule :
          ExplicitFormulaCofinalHeightSchedule completedPrimeContourTransportFamily =>
          finitePrimeContourTransportTomographicErrorRemainderMajorantAt
            heightSchedule N f)
        hheight
    have hconcrete :
        finitePrimeContourTransportTomographicErrorRemainderMajorantAt
            completedPrimeContourTransportHeightSchedule_owner N f =
          finitePrimeContourTransportTomographicErrorRemainderMajorant N f := by
      rfl
    exact hschedule.trans hconcrete
  exact Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hfun
    hparametric

/-- The explicit finite-window tail majorant tends to zero. -/
theorem finitePrimeContourTransportTomographicErrorRemainderMajorant_tendsto_zero
    (S : CompletedPrimeContourTransportScheduledFamily)
    (hheight :
      S.height_schedule = completedPrimeContourTransportHeightSchedule_owner)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hHorizontal :
      ExplicitFormulaScheduledHorizontalLogDerivControl
        (convolutionAutocorrelation f)
        completedPrimeContourTransportFamily
        S.height_schedule) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeContourTransportTomographicErrorRemainderMajorant N f)
      atTop
      (𝓝 0) := by
  exact
    finitePrimeContourTransportTomographicErrorRemainderMajorant_tendsto_zero_core
      S hheight f hPhi hHorizontal

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

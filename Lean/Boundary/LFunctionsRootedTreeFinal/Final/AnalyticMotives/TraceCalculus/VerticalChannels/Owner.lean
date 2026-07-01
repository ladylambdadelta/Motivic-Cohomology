import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.BasicChannels

/-!
# Analytic-motive vertical channels

This file exposes the finite-height contour channels already owned by the
explicit-formula complex-analysis lane as analytic-motive trace channels.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open LSeries ArithmeticFunction
open scoped ArithmeticFunction

namespace AnalyticMotives

/-- The contour family used by the analytic-motive trace-channel facade. -/
abbrev TraceContourFamily :=
  ExplicitFormulaContourFamily

/-- Analytic package for a trace contour family. -/
abbrev TraceContourAnalyticPackage
    (f : ZetaAdmissibleFunction) (F : TraceContourFamily) :=
  ExplicitFormulaFamilyAnalyticPackage f F

/-- The finite-height prime trace channel. -/
def primeVerticalTraceChannel
    (f : ZetaAdmissibleFunction) (F : TraceContourFamily) (T : ℝ) : ℂ :=
  ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeVerticalChannel f F T

/-- The finite-height archimedean trace channel. -/
def archimedeanVerticalTraceChannel
    (f : ZetaAdmissibleFunction) (F : TraceContourFamily) (T : ℝ) : ℂ :=
  ZetaAdmissibleFunction.zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F T

/-- The finite-height pole-correction trace channel. -/
def correctionVerticalTraceChannel
    (f : ZetaAdmissibleFunction) (F : TraceContourFamily) (T : ℝ) : ℂ :=
  ZetaAdmissibleFunction.zetaCompletedExplicitFormulaCorrectionVerticalChannel f F T

/-- The finite-height inverse-Gamma completion trace channel. -/
def inverseGammaCompletionVerticalTraceChannel
    (f : ZetaAdmissibleFunction) (F : TraceContourFamily) (T : ℝ) : ℂ :=
  ZetaAdmissibleFunction.zetaCompletedExplicitFormulaInverseGammaCompletionVerticalChannel f F T

/-- Prime-channel transport defect against its limiting trace contribution. -/
def primeVerticalTraceTransportRemainder
    (f : ZetaAdmissibleFunction) (F : TraceContourFamily) (T : ℝ) : ℂ :=
  ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
    f F T

/-- Archimedean-channel transport defect against its limiting trace contribution. -/
def archimedeanVerticalTraceTransportRemainder
    (f : ZetaAdmissibleFunction) (F : TraceContourFamily) (T : ℝ) : ℂ :=
  ZetaAdmissibleFunction.zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
    f F T

/-- The sum of the prime, archimedean, and correction trace channels. -/
def verticalTraceChannelSum
    (f : ZetaAdmissibleFunction) (F : TraceContourFamily) (T : ℝ) : ℂ :=
  ZetaAdmissibleFunction.zetaCompletedExplicitFormulaVerticalChannelSum f F T

/-- Prime-channel normalization by the right von Mangoldt integral. -/
theorem primeVerticalTraceChannel_eq_rightVonMangoldtIntegral_sub_left
    (f : ZetaAdmissibleFunction) (F : TraceContourFamily) (T : ℝ) :
    primeVerticalTraceChannel f F T =
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        L ↗Λ
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) -
        ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
          explicitFormulaPrimeLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) :=
  ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeVerticalChannel_eq_rightVonMangoldtIntegral_sub_left
    f F T

/-- Scheduled inverse-Gamma completion is the explicit right-minus-left vertical integral. -/
theorem inverseGammaCompletionVerticalTraceChannel_scheduled_eq
    (f : ZetaAdmissibleFunction) (F : TraceContourFamily)
    (h : TraceContourAnalyticPackage f F) (u : ℝ) :
    inverseGammaCompletionVerticalTraceChannel f F (h.height_schedule.height u) =
      (∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaRightPath
              (F.rectangle (h.height_schedule.height u)) t) *
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath
              (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) -
        ∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
          inverseGammaCompletionLogDeriv
              (zetaCompletedExplicitFormulaLeftPath
                (F.rectangle (h.height_schedule.height u)) t) *
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath
                (F.rectangle (h.height_schedule.height u)) t - 1 / 2) :=
  ZetaAdmissibleFunction.zetaCompletedExplicitFormulaInverseGammaCompletionVerticalChannel_scheduled_eq
    f F h u

/-- Fixed-height inverse-Gamma completion decomposes into archimedean plus correction traces. -/
theorem inverseGammaCompletionVerticalTraceChannel_eq_archimedean_add_correction
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : TraceContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    inverseGammaCompletionVerticalTraceChannel f F T =
      archimedeanVerticalTraceChannel f F T +
        correctionVerticalTraceChannel f F T :=
  ZetaAdmissibleFunction.zetaCompletedExplicitFormulaInverseGammaCompletionVerticalChannel_eq_archimedean_add_correction_ownerCompact
    f hPhi F T havoid

end AnalyticMotives

end
end LFunctions
end Boundary

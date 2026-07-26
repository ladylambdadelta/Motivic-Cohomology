import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.PositivityBridge
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalAnalyticInputs

/-!
# Canonical schedule compatibility for the positivity bridge

The active positivity bridge is schedule-parametric.  This file preserves the
canonical schedule theorem names as compatibility wrappers around that
schedule-parametric owner surface.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- The right-one correction integral converges to its Cauchy projection along
the canonical avoiding height schedule. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_tendsto_projection_owner
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaAdmissibleFunction.ZetaPhiAnalyticControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    Tendsto
      (fun u : ℝ =>
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
          ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
            f
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
            hPhi
            hLog).height_schedule.height u))
      atTop
      (𝓝
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :=
  zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_tendsto_projection_of_schedule_owner
    f
    (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
    hPhi
    hLog

/-- Scheduled contour convergence along the canonical autocorrelation height
schedule. -/
def ZetaCompletedAutocorrelationScheduledContourLimit : Prop :=
  ZetaCompletedAutocorrelationScheduledContourLimitOf
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)

/-- Scheduled contour convergence along the canonical autocorrelation height
schedule with fixed-degree scheduled horizontal log-derivative growth. -/
def ZetaCompletedAutocorrelationPolynomialScheduledContourLimit : Prop :=
  ZetaCompletedAutocorrelationPolynomialScheduledContourLimitOf
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)

/-- Pointwise finite-rectangle residue equality along the canonical
autocorrelation height schedule for the completed-boundary bridge. -/
def ZetaCompletedAutocorrelationScheduledFiniteResidueEquality : Prop :=
  ZetaCompletedAutocorrelationScheduledFiniteResidueEqualityOf
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)

/-- Pointwise finite-residue equality at every canonical scheduled height. -/
def ZetaCompletedAutocorrelationCanonicalHeightWindowResidueEquality : Prop :=
  ∀ f : ZetaAdmissibleFunction,
    ∀ hPhi : ZetaAdmissibleFunction.ZetaPhiAnalyticControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f),
    ∀ hLog : ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f),
    ∀ u : ℝ,
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaContourIntegral
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
              f
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
              hPhi
              hLog).height_schedule.height u)) =
        ZetaAdmissibleFunction.explicitFormulaCompletedZeroContourHeightWindowResidueSum
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
            f
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
            hPhi
            hLog).height_schedule.height u)

/-- Vanishing of the scheduled finite-residue error at every canonical
autocorrelation height. -/
def ZetaCompletedAutocorrelationCanonicalResidueEqualityErrorVanishing : Prop :=
  ∀ f : ZetaAdmissibleFunction,
    ∀ hPhi : ZetaAdmissibleFunction.ZetaPhiAnalyticControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f),
    ∀ hLog : ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f),
    ∀ u : ℝ,
      ZetaAdmissibleFunction.explicitFormulaScheduledRectangleResidueEqualityError
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
            f
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
            hPhi
            hLog)
          u =
        0

/-- Canonical scheduled residue-error vanishing gives pointwise canonical
height-window residue equality. -/
theorem zetaCompletedAutocorrelationCanonicalHeightWindowResidueEquality_of_residueEqualityErrorVanishing
    (hzero :
      ZetaCompletedAutocorrelationCanonicalResidueEqualityErrorVanishing) :
    ZetaCompletedAutocorrelationCanonicalHeightWindowResidueEquality :=
  fun f hPhi hLog =>
    ZetaAdmissibleFunction.zetaCompletedScheduledHeightWindowResidueEquality_of_residueEqualityError_eq_zero_all
      (ZetaAdmissibleFunction.convolutionAutocorrelation f)
      (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
      (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
        f
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
        hPhi
        hLog)
      (hzero f hPhi hLog)

/-- Canonical height-window residue equality gives vanishing of the scheduled
finite-residue error. -/
theorem zetaCompletedAutocorrelationCanonicalResidueEqualityErrorVanishing_of_heightWindowResidueEquality
    (hfinite :
      ZetaCompletedAutocorrelationCanonicalHeightWindowResidueEquality) :
    ZetaCompletedAutocorrelationCanonicalResidueEqualityErrorVanishing :=
  fun f hPhi hLog u =>
    ZetaAdmissibleFunction.explicitFormulaScheduledRectangleResidueEqualityError_eq_zero_of_heightWindowResidueEquality
      (ZetaAdmissibleFunction.convolutionAutocorrelation f)
      (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
      (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
        f
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
        hPhi
        hLog)
      u
      (hfinite f hPhi hLog u)

/-- The canonical scheduled finite-rectangle equality is the exact residue
content needed for residue-error vanishing.  The analytic package already
stores the scheduled boundary-avoidance certificate, so this wrapper leaves
only the pointwise finite-residue equality as the remaining finite-rectangle
theorem input. -/
theorem zetaCompletedAutocorrelationCanonicalResidueEqualityErrorVanishing_of_pointwiseFiniteRectangleResidueEquality
    (hfinite :
      ∀ f : ZetaAdmissibleFunction,
        ∀ hPhi : ZetaAdmissibleFunction.ZetaPhiAnalyticControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f),
        ∀ hLog : ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f),
        ∀ u : ℝ,
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaContourIntegral
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
                  f
                  (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
                  hPhi
                  hLog).height_schedule.height u)) =
            ZetaAdmissibleFunction.explicitFormulaCompletedZeroContourHeightWindowResidueSum
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
                f
                (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
                hPhi
                hLog).height_schedule.height u)) :
    ZetaCompletedAutocorrelationCanonicalResidueEqualityErrorVanishing :=
  zetaCompletedAutocorrelationCanonicalResidueEqualityErrorVanishing_of_heightWindowResidueEquality
    hfinite

/-- The canonical finite-residue error surface is equivalent to pointwise
height-window residue equality. -/
theorem zetaCompletedAutocorrelationCanonicalResidueEqualityErrorVanishing_iff_heightWindowResidueEquality :
    ZetaCompletedAutocorrelationCanonicalResidueEqualityErrorVanishing ↔
      ZetaCompletedAutocorrelationCanonicalHeightWindowResidueEquality :=
  Iff.intro
    zetaCompletedAutocorrelationCanonicalHeightWindowResidueEquality_of_residueEqualityErrorVanishing
    zetaCompletedAutocorrelationCanonicalResidueEqualityErrorVanishing_of_heightWindowResidueEquality

/-- Pointwise finite-residue equality at every canonical scheduled height
supplies the canonical scheduled finite-residue package. -/
theorem zetaCompletedAutocorrelationScheduledFiniteResidueEquality_of_heightWindowResidueEquality
    (hfinite :
      ZetaCompletedAutocorrelationCanonicalHeightWindowResidueEquality) :
    ZetaCompletedAutocorrelationScheduledFiniteResidueEquality :=
  fun f hPhi hLog =>
    ZetaAdmissibleFunction.zetaCompletedScheduledFiniteResidueEquality_of_heightWindowResidueEquality
      (ZetaAdmissibleFunction.convolutionAutocorrelation f)
      (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
      (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
        f
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
        hPhi
      hLog)
      (hfinite f hPhi hLog)

/-- The canonical scheduled finite-residue package unfolds back to pointwise
height-window residue equality. -/
theorem zetaCompletedAutocorrelationCanonicalHeightWindowResidueEquality_of_scheduledFiniteResidueEquality
    (hfinite :
      ZetaCompletedAutocorrelationScheduledFiniteResidueEquality) :
    ZetaCompletedAutocorrelationCanonicalHeightWindowResidueEquality :=
  fun f hPhi hLog =>
    Exists.elim (hfinite f hPhi hLog)
      (fun residueWindowDegree hresidue =>
        Eq.subst
          (motive := fun residueWindowDegreeTransport : ℕ =>
            ∀ u : ℝ,
              ZetaAdmissibleFunction.zetaCompletedExplicitFormulaContourIntegral
                  (ZetaAdmissibleFunction.convolutionAutocorrelation f)
                  ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                    ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
                      f
                      (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
                      hPhi
                      hLog).height_schedule.height u)) =
                ZetaAdmissibleFunction.explicitFormulaCompletedZeroContourHeightWindowResidueSum
                  (ZetaAdmissibleFunction.convolutionAutocorrelation f)
                  ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
                    f
                    (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
                    hPhi
                    hLog).height_schedule.height u))
          (Eq.refl residueWindowDegree)
          hresidue)

/-- The canonical scheduled finite-residue package is exactly the pointwise
height-window residue equality. -/
theorem zetaCompletedAutocorrelationScheduledFiniteResidueEquality_iff_heightWindowResidueEquality :
    ZetaCompletedAutocorrelationScheduledFiniteResidueEquality ↔
      ZetaCompletedAutocorrelationCanonicalHeightWindowResidueEquality :=
  Iff.intro
    zetaCompletedAutocorrelationCanonicalHeightWindowResidueEquality_of_scheduledFiniteResidueEquality
    zetaCompletedAutocorrelationScheduledFiniteResidueEquality_of_heightWindowResidueEquality

/-- Canonical scheduled residue-error vanishing gives the canonical scheduled
finite-residue package. -/
theorem zetaCompletedAutocorrelationScheduledFiniteResidueEquality_of_residueEqualityErrorVanishing
    (hzero :
      ZetaCompletedAutocorrelationCanonicalResidueEqualityErrorVanishing) :
    ZetaCompletedAutocorrelationScheduledFiniteResidueEquality :=
  zetaCompletedAutocorrelationScheduledFiniteResidueEquality_of_heightWindowResidueEquality
    (zetaCompletedAutocorrelationCanonicalHeightWindowResidueEquality_of_residueEqualityErrorVanishing
      hzero)

/-- The canonical scheduled finite-residue package gives vanishing of the
scheduled finite-residue error. -/
theorem zetaCompletedAutocorrelationCanonicalResidueEqualityErrorVanishing_of_scheduledFiniteResidueEquality
    (hfinite :
      ZetaCompletedAutocorrelationScheduledFiniteResidueEquality) :
    ZetaCompletedAutocorrelationCanonicalResidueEqualityErrorVanishing :=
  zetaCompletedAutocorrelationCanonicalResidueEqualityErrorVanishing_of_heightWindowResidueEquality
    (zetaCompletedAutocorrelationCanonicalHeightWindowResidueEquality_of_scheduledFiniteResidueEquality
      hfinite)

/-- The canonical scheduled finite-residue package is equivalent to vanishing
of the scheduled finite-residue error. -/
theorem zetaCompletedAutocorrelationScheduledFiniteResidueEquality_iff_residueEqualityErrorVanishing :
    ZetaCompletedAutocorrelationScheduledFiniteResidueEquality ↔
      ZetaCompletedAutocorrelationCanonicalResidueEqualityErrorVanishing :=
  Iff.intro
    zetaCompletedAutocorrelationCanonicalResidueEqualityErrorVanishing_of_scheduledFiniteResidueEquality
    zetaCompletedAutocorrelationScheduledFiniteResidueEquality_of_residueEqualityErrorVanishing

/-- The canonical finite-rectangle pointwise residue theorem implies the
canonical fixed-degree scheduled autocorrelation contour limit. -/
theorem zetaCompletedAutocorrelationPolynomialScheduledContourLimit_of_finiteResidueEquality
    (hfinite :
      ZetaCompletedAutocorrelationScheduledFiniteResidueEquality) :
    ZetaCompletedAutocorrelationPolynomialScheduledContourLimit :=
  zetaCompletedAutocorrelationPolynomialScheduledContourLimitOf_of_finiteResidueEquality
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
    hfinite

/-- The canonical fixed-degree scheduled contour limit supplies the legacy
canonical scheduled contour-limit surface. -/
theorem zetaCompletedAutocorrelationScheduledContourLimit_of_polynomialScheduledContourLimit
    (hpoly :
      ZetaCompletedAutocorrelationPolynomialScheduledContourLimit) :
    ZetaCompletedAutocorrelationScheduledContourLimit :=
  zetaCompletedAutocorrelationScheduledContourLimitOf_of_polynomialScheduledContourLimit
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
    hpoly

/-- The canonical finite-rectangle pointwise residue theorem plus independent
polynomial-growth control implies the canonical scheduled autocorrelation
contour limit. -/
theorem zetaCompletedAutocorrelationScheduledContourLimit_of_finiteResidueEquality_and_polynomialGrowthControl
    (hfinite :
      ZetaCompletedAutocorrelationScheduledFiniteResidueEquality)
    (hGrowth : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivPolynomialGrowthControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    ZetaCompletedAutocorrelationScheduledContourLimit :=
  zetaCompletedAutocorrelationScheduledContourLimitOf_of_finiteResidueEquality_and_polynomialGrowthControl
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
    hfinite
    hGrowth

theorem zetaCompletedAutocorrelationScheduledContourLimit_of_heightWindowResidueEquality_and_polynomialGrowthControl
    (hheight :
      ZetaCompletedAutocorrelationCanonicalHeightWindowResidueEquality)
    (hGrowth : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivPolynomialGrowthControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    ZetaCompletedAutocorrelationScheduledContourLimit :=
  zetaCompletedAutocorrelationScheduledContourLimit_of_finiteResidueEquality_and_polynomialGrowthControl
    (zetaCompletedAutocorrelationScheduledFiniteResidueEquality_of_heightWindowResidueEquality
      hheight)
    hGrowth

/-- The canonical autocorrelation schedule family. -/
noncomputable def zetaCompletedAutocorrelationCanonicalScheduleFamily :
    ZetaCompletedAutocorrelationHorizontalAvoidingScheduleFamily :=
  { schedule :=
      fun f =>
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f }

/-- Completed log-derivative control, Binet coherence, and the canonical
scheduled contour limit give the completed-boundary identification. -/
theorem zetaWeilAutocorrelationCompletedBoundaryIdentification_of_contourAssembly
    (hPhi : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hcontour :
      ZetaCompletedAutocorrelationScheduledContourLimit) :
    ZetaWeilAutocorrelationCompletedBoundaryIdentification :=
  zetaWeilAutocorrelationCompletedBoundaryIdentification_of_contourAssemblyOf
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
    hPhi
    hLog
    hcoh
    hcontour

/-- The scheduled normalized pole-corrected contour integrals converge to the
completed-zero side of the autocorrelation probe. -/
theorem zetaCompletedExplicitFormulaAutocorrelationNormalizedPoleCorrectedContour_tendsto_zeroSide_owner
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaAdmissibleFunction.ZetaPhiAnalyticControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (zeroSideSummable :
      Summable
        (fun rho : {rho : ℂ // ZetaCompletedZero rho} =>
          zetaZeroSideContribution (rho : ℂ)
            (ZetaAdmissibleFunction.convolutionAutocorrelation f))) :
    Tendsto
      (fun u : ℝ =>
        ZetaAdmissibleFunction.explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
          ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
            f
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
            hPhi
            hLog).height_schedule.height u))
      atTop
      (𝓝 (ZetaAdmissibleFunction.zetaCompletedZeroSideComplex
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))) :=
  let probe : ZetaAdmissibleFunction :=
    ZetaAdmissibleFunction.convolutionAutocorrelation f
  let family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily :=
    ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f
  let analyticPackage :
      ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage probe family :=
    ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
      f
      (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
      hPhi
      hLog
  Exists.elim analyticPackage.scheduled_horizontalFamilyZeroExcisedStrip
    (fun carrier stripSpec =>
      ZetaAdmissibleFunction.explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral_tendsto_zeroSideComplex
        probe family analyticPackage carrier stripSpec.1 stripSpec.2 zeroSideSummable)

end

end LFunctions
end Boundary

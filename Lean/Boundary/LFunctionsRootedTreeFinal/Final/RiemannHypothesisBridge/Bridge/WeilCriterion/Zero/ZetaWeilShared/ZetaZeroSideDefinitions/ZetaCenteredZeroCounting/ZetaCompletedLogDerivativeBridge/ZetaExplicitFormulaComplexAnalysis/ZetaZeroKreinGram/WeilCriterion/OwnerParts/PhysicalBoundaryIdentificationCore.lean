import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PhysicalContourBoundaryCore

/-!
# Selector-free physical boundary identification

This file owns the limit-uniqueness and real-part transport from completed
zero-side boundary data to the Weil boundary identification.  It deliberately
does not select a contour-height schedule.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

/-- A common contour limit identifies the zero-side series with the
pole-corrected boundary. -/
theorem zetaCompletedAutocorrelationZeroSideBoundaryIdentification_of_commonLimit_core
    (commonLimit : ZetaCompletedAutocorrelationPoleCorrectedCommonLimit) :
    ZetaCompletedAutocorrelationZeroSideBoundaryIdentification :=
  fun f =>
    Exists.elim (commonLimit f)
      (fun φ hφ =>
        tendsto_nhds_unique hφ.1 hφ.2)

/-- A pointwise family with the two physical endpoint limits constructs the
common-limit surface consumed by zero-side boundary identification. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_limitFamily_core
    (φ : ∀ f : ZetaAdmissibleFunction, ℝ → ℂ)
    (zeroLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto (φ f) atTop
          (𝓝
            (Boundary.LFunctions.zetaCompletedZeroSideComplex
              (ZetaAdmissibleFunction.convolutionAutocorrelation f))))
    (boundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto (φ f) atTop
          (𝓝
            (zetaCompletedAffinePoleCorrectedBoundaryChannel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)))) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  fun f =>
    Exists.intro
      (φ f)
      (And.intro
        (zeroLimit f)
        (boundaryLimit f))

/-- The zero-side boundary identification implies the real Weil-form boundary
identification. -/
theorem zetaWeilAutocorrelationBoundaryIdentification_of_zeroSideBoundaryIdentification_core
    (zeroBoundary :
      ZetaCompletedAutocorrelationZeroSideBoundaryIdentification) :
    ZetaWeilAutocorrelationBoundaryIdentification :=
  fun f =>
    Eq.trans
      (zetaWeilFormCompleted_convolutionAutocorrelation_eq_zeroSide f)
      (congrArg Complex.re (zeroBoundary f))

/-- The common-limit statement supplies the exact boundary identification
consumed by the positivity bridge. -/
theorem zetaWeilAutocorrelationBoundaryIdentification_of_commonLimit_core
    (commonLimit : ZetaCompletedAutocorrelationPoleCorrectedCommonLimit) :
    ZetaWeilAutocorrelationBoundaryIdentification :=
  zetaWeilAutocorrelationBoundaryIdentification_of_zeroSideBoundaryIdentification_core
    (zetaCompletedAutocorrelationZeroSideBoundaryIdentification_of_commonLimit_core
      commonLimit)

end
end LFunctions
end Boundary

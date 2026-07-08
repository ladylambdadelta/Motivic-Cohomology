import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Defects.Filtration.FiniteChain.Payload.Sums.AssociatedAppend.Owner

/-!
# Right-bracketed associated-graded payloads as recursive sums

This file gives recursive payload normal forms for the right-bracketed
finite-chain associated-graded defect ledger `first ++ (second ++ third)`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The imported-rectangle count of a right-bracketed associated-graded
finite-chain defect is the right-associated sum of recursive counts. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_rebracketTarget_importedRectangleCount_eq_sum
    (first second third : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (first ++ (second ++ third))).importedRectangleCount =
      TraceTransport.finiteChainDefectImportedRectangleCount first +
        (TraceTransport.finiteChainDefectImportedRectangleCount second +
          TraceTransport.finiteChainDefectImportedRectangleCount third) :=
  Eq.trans
    (TraceTransport.finiteChainAssociatedGradedDefect_append_importedRectangleCount_eq_sum
      first
      (second ++ third))
    (congrArg
      (fun count =>
        TraceTransport.finiteChainDefectImportedRectangleCount first + count)
      (TraceTransport.finiteChainDefectImportedRectangleCount_append
        second
        third))

/-- The imported-rectangle list of a right-bracketed associated-graded
finite-chain defect is the right-associated append of recursive lists. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_rebracketTarget_importedRectangles_eq_sum
    (first second third : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (first ++ (second ++ third))).importedRectangles =
      TraceTransport.finiteChainDefectImportedRectangles first ++
        (TraceTransport.finiteChainDefectImportedRectangles second ++
          TraceTransport.finiteChainDefectImportedRectangles third) :=
  Eq.trans
    (TraceTransport.finiteChainAssociatedGradedDefect_append_importedRectangles_eq_sum
      first
      (second ++ third))
    (congrArg
      (fun rectangles =>
        TraceTransport.finiteChainDefectImportedRectangles first ++ rectangles)
      (TraceTransport.finiteChainDefectImportedRectangles_append
        second
        third))

/-- The bookkeeping count of a right-bracketed associated-graded finite-chain
defect is the right-associated sum of recursive bookkeeping counts. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_rebracketTarget_traceBookkeepingCount_eq_sum
    (first second third : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (first ++ (second ++ third))).traceBookkeepingCount =
      TraceTransport.finiteChainDefectTraceBookkeepingCount first +
        (TraceTransport.finiteChainDefectTraceBookkeepingCount second +
          TraceTransport.finiteChainDefectTraceBookkeepingCount third) :=
  Eq.trans
    (TraceTransport.finiteChainAssociatedGradedDefect_append_traceBookkeepingCount_eq_sum
      first
      (second ++ third))
    (congrArg
      (fun count =>
        TraceTransport.finiteChainDefectTraceBookkeepingCount first + count)
      (TraceTransport.finiteChainDefectTraceBookkeepingCount_append
        second
        third))

/-- The rewrite-step count of a right-bracketed associated-graded finite-chain
defect is the right-associated sum of recursive rewrite-step counts. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_rebracketTarget_rewriteStepCount_eq_sum
    (first second third : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (first ++ (second ++ third))).rewriteStepCount =
      TraceTransport.finiteChainDefectRewriteStepCount first +
        (TraceTransport.finiteChainDefectRewriteStepCount second +
          TraceTransport.finiteChainDefectRewriteStepCount third) :=
  Eq.trans
    (TraceTransport.finiteChainAssociatedGradedDefect_append_rewriteStepCount_eq_sum
      first
      (second ++ third))
    (congrArg
      (fun count =>
        TraceTransport.finiteChainDefectRewriteStepCount first + count)
      (TraceTransport.finiteChainDefectRewriteStepCount_append
        second
        third))

end AnalyticMotives
end LFunctions
end Boundary

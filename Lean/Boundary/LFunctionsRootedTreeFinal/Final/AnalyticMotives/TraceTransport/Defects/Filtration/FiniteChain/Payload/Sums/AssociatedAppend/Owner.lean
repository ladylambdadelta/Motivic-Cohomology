import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Defects.Filtration.FiniteChain.Append.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Defects.Filtration.FiniteChain.Payload.Sums.Owner

/-!
# Associated-graded append payloads as recursive sums

This file combines finite-chain associated-graded append payload splitting with
the recursive payload-sum normal forms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The imported-rectangle count of a concatenated associated-graded finite-chain
defect is the sum of the two recursive imported-rectangle counts. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_append_importedRectangleCount_eq_sum
    (first second : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (first ++ second)).importedRectangleCount =
      TraceTransport.finiteChainDefectImportedRectangleCount first +
        TraceTransport.finiteChainDefectImportedRectangleCount second :=
  Eq.trans
    (TraceTransport.finiteChainAssociatedGradedDefect_append_importedRectangleCount
      first
      second)
    (Eq.trans
      (congrArg
        (fun count =>
          count +
            (TraceTransport.finiteChainAssociatedGradedDefect second).importedRectangleCount)
        (TraceTransport.finiteChainAssociatedGradedDefect_importedRectangleCount_eq_sum
          first))
      (congrArg
        (fun count =>
          TraceTransport.finiteChainDefectImportedRectangleCount first + count)
        (TraceTransport.finiteChainAssociatedGradedDefect_importedRectangleCount_eq_sum
          second)))

/-- The imported-rectangle list of a concatenated associated-graded finite-chain
defect is the append of the two recursive imported-rectangle lists. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_append_importedRectangles_eq_sum
    (first second : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (first ++ second)).importedRectangles =
      TraceTransport.finiteChainDefectImportedRectangles first ++
        TraceTransport.finiteChainDefectImportedRectangles second :=
  Eq.trans
    (TraceTransport.finiteChainAssociatedGradedDefect_append_importedRectangles
      first
      second)
    (Eq.trans
      (congrArg
        (fun rectangles =>
          rectangles ++
            (TraceTransport.finiteChainAssociatedGradedDefect second).importedRectangles)
        (TraceTransport.finiteChainAssociatedGradedDefect_importedRectangles_eq_sum
          first))
      (congrArg
        (fun rectangles =>
          TraceTransport.finiteChainDefectImportedRectangles first ++ rectangles)
        (TraceTransport.finiteChainAssociatedGradedDefect_importedRectangles_eq_sum
          second)))

/-- The bookkeeping count of a concatenated associated-graded finite-chain
defect is the sum of the two recursive bookkeeping counts. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_append_traceBookkeepingCount_eq_sum
    (first second : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (first ++ second)).traceBookkeepingCount =
      TraceTransport.finiteChainDefectTraceBookkeepingCount first +
        TraceTransport.finiteChainDefectTraceBookkeepingCount second :=
  Eq.trans
    (TraceTransport.finiteChainAssociatedGradedDefect_append_traceBookkeepingCount
      first
      second)
    (Eq.trans
      (congrArg
        (fun count =>
          count +
            (TraceTransport.finiteChainAssociatedGradedDefect second).traceBookkeepingCount)
        (TraceTransport.finiteChainAssociatedGradedDefect_traceBookkeepingCount_eq_sum
          first))
      (congrArg
        (fun count =>
          TraceTransport.finiteChainDefectTraceBookkeepingCount first + count)
        (TraceTransport.finiteChainAssociatedGradedDefect_traceBookkeepingCount_eq_sum
          second)))

/-- The rewrite-step count of a concatenated associated-graded finite-chain
defect is the sum of the two recursive rewrite-step counts. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_append_rewriteStepCount_eq_sum
    (first second : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (first ++ second)).rewriteStepCount =
      TraceTransport.finiteChainDefectRewriteStepCount first +
        TraceTransport.finiteChainDefectRewriteStepCount second :=
  Eq.trans
    (TraceTransport.finiteChainAssociatedGradedDefect_append_rewriteStepCount
      first
      second)
    (Eq.trans
      (congrArg
        (fun count =>
          count +
            (TraceTransport.finiteChainAssociatedGradedDefect second).rewriteStepCount)
        (TraceTransport.finiteChainAssociatedGradedDefect_rewriteStepCount_eq_sum
          first))
      (congrArg
        (fun count =>
          TraceTransport.finiteChainDefectRewriteStepCount first + count)
        (TraceTransport.finiteChainAssociatedGradedDefect_rewriteStepCount_eq_sum
          second)))

end AnalyticMotives
end LFunctions
end Boundary

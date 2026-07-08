import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Defects.Filtration.FiniteChain.Associativity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Defects.Filtration.FiniteChain.Payload.Sums.Owner

/-!
# Associated-graded associativity payloads as recursive sums

This file combines finite-chain associated-graded three-block payload
associativity with the recursive payload-sum normal forms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The imported-rectangle count of a three-block associated-graded finite-chain
defect is the right-associated sum of the three recursive counts. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_assoc_importedRectangleCount_eq_sum
    (first second third : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ((first ++ second) ++ third)).importedRectangleCount =
      TraceTransport.finiteChainDefectImportedRectangleCount first +
        (TraceTransport.finiteChainDefectImportedRectangleCount second +
          TraceTransport.finiteChainDefectImportedRectangleCount third) :=
  Eq.trans
    (TraceTransport.finiteChainAssociatedGradedDefect_append_append_assoc_importedRectangleCount
      first
      second
      third)
    (Eq.trans
      (congrArg
        (fun count =>
          count +
            ((TraceTransport.finiteChainAssociatedGradedDefect second).importedRectangleCount +
              (TraceTransport.finiteChainAssociatedGradedDefect third).importedRectangleCount))
        (TraceTransport.finiteChainAssociatedGradedDefect_importedRectangleCount_eq_sum
          first))
      (Eq.trans
        (congrArg
          (fun count =>
            TraceTransport.finiteChainDefectImportedRectangleCount first +
              (count +
                (TraceTransport.finiteChainAssociatedGradedDefect third).importedRectangleCount))
          (TraceTransport.finiteChainAssociatedGradedDefect_importedRectangleCount_eq_sum
            second))
        (congrArg
          (fun count =>
            TraceTransport.finiteChainDefectImportedRectangleCount first +
              (TraceTransport.finiteChainDefectImportedRectangleCount second + count))
          (TraceTransport.finiteChainAssociatedGradedDefect_importedRectangleCount_eq_sum
            third))))

/-- The imported-rectangle list of a three-block associated-graded finite-chain
defect is the right-associated append of the three recursive lists. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_assoc_importedRectangles_eq_sum
    (first second third : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ((first ++ second) ++ third)).importedRectangles =
      TraceTransport.finiteChainDefectImportedRectangles first ++
        (TraceTransport.finiteChainDefectImportedRectangles second ++
          TraceTransport.finiteChainDefectImportedRectangles third) :=
  Eq.trans
    (TraceTransport.finiteChainAssociatedGradedDefect_append_append_assoc_importedRectangles
      first
      second
      third)
    (Eq.trans
      (congrArg
        (fun rectangles =>
          rectangles ++
            ((TraceTransport.finiteChainAssociatedGradedDefect second).importedRectangles ++
              (TraceTransport.finiteChainAssociatedGradedDefect third).importedRectangles))
        (TraceTransport.finiteChainAssociatedGradedDefect_importedRectangles_eq_sum
          first))
      (Eq.trans
        (congrArg
          (fun rectangles =>
            TraceTransport.finiteChainDefectImportedRectangles first ++
              (rectangles ++
                (TraceTransport.finiteChainAssociatedGradedDefect third).importedRectangles))
          (TraceTransport.finiteChainAssociatedGradedDefect_importedRectangles_eq_sum
            second))
        (congrArg
          (fun rectangles =>
            TraceTransport.finiteChainDefectImportedRectangles first ++
              (TraceTransport.finiteChainDefectImportedRectangles second ++ rectangles))
          (TraceTransport.finiteChainAssociatedGradedDefect_importedRectangles_eq_sum
            third))))

/-- The bookkeeping count of a three-block associated-graded finite-chain defect
is the right-associated sum of the three recursive bookkeeping counts. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_assoc_traceBookkeepingCount_eq_sum
    (first second third : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ((first ++ second) ++ third)).traceBookkeepingCount =
      TraceTransport.finiteChainDefectTraceBookkeepingCount first +
        (TraceTransport.finiteChainDefectTraceBookkeepingCount second +
          TraceTransport.finiteChainDefectTraceBookkeepingCount third) :=
  Eq.trans
    (TraceTransport.finiteChainAssociatedGradedDefect_append_append_assoc_traceBookkeepingCount
      first
      second
      third)
    (Eq.trans
      (congrArg
        (fun count =>
          count +
            ((TraceTransport.finiteChainAssociatedGradedDefect second).traceBookkeepingCount +
              (TraceTransport.finiteChainAssociatedGradedDefect third).traceBookkeepingCount))
        (TraceTransport.finiteChainAssociatedGradedDefect_traceBookkeepingCount_eq_sum
          first))
      (Eq.trans
        (congrArg
          (fun count =>
            TraceTransport.finiteChainDefectTraceBookkeepingCount first +
              (count +
                (TraceTransport.finiteChainAssociatedGradedDefect third).traceBookkeepingCount))
          (TraceTransport.finiteChainAssociatedGradedDefect_traceBookkeepingCount_eq_sum
            second))
        (congrArg
          (fun count =>
            TraceTransport.finiteChainDefectTraceBookkeepingCount first +
              (TraceTransport.finiteChainDefectTraceBookkeepingCount second + count))
          (TraceTransport.finiteChainAssociatedGradedDefect_traceBookkeepingCount_eq_sum
            third))))

/-- The rewrite-step count of a three-block associated-graded finite-chain defect
is the right-associated sum of the three recursive rewrite-step counts. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_assoc_rewriteStepCount_eq_sum
    (first second third : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ((first ++ second) ++ third)).rewriteStepCount =
      TraceTransport.finiteChainDefectRewriteStepCount first +
        (TraceTransport.finiteChainDefectRewriteStepCount second +
          TraceTransport.finiteChainDefectRewriteStepCount third) :=
  Eq.trans
    (TraceTransport.finiteChainAssociatedGradedDefect_append_append_assoc_rewriteStepCount
      first
      second
      third)
    (Eq.trans
      (congrArg
        (fun count =>
          count +
            ((TraceTransport.finiteChainAssociatedGradedDefect second).rewriteStepCount +
              (TraceTransport.finiteChainAssociatedGradedDefect third).rewriteStepCount))
        (TraceTransport.finiteChainAssociatedGradedDefect_rewriteStepCount_eq_sum
          first))
      (Eq.trans
        (congrArg
          (fun count =>
            TraceTransport.finiteChainDefectRewriteStepCount first +
              (count +
                (TraceTransport.finiteChainAssociatedGradedDefect third).rewriteStepCount))
          (TraceTransport.finiteChainAssociatedGradedDefect_rewriteStepCount_eq_sum
            second))
        (congrArg
          (fun count =>
            TraceTransport.finiteChainDefectRewriteStepCount first +
              (TraceTransport.finiteChainDefectRewriteStepCount second + count))
          (TraceTransport.finiteChainAssociatedGradedDefect_rewriteStepCount_eq_sum
            third))))

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Defects.Filtration.Composite.Triple.Owner

/-!
# Payload formulas for triple composite defect filtrations

This file specializes the finite-chain three-block payload formulas to
three singleton transport factors.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The left-associated triple defect rewrite-step count is the right-associated
sum of the three singleton defect rewrite-step counts. -/
theorem TraceTransport.leftTripleAssociatedGradedDefect_rewriteStepCount
    (first second third : TraceTransport) :
    (TraceTransport.leftTripleAssociatedGradedDefect
      first
      second
      third).rewriteStepCount =
      (TraceTransport.finiteChainAssociatedGradedDefect [first]).rewriteStepCount +
        ((TraceTransport.finiteChainAssociatedGradedDefect [second]).rewriteStepCount +
          (TraceTransport.finiteChainAssociatedGradedDefect [third]).rewriteStepCount) :=
  TraceTransport.finiteChainAssociatedGradedDefect_append_append_assoc_rewriteStepCount
    [first]
    [second]
    [third]

/-- The left-associated triple defect imported-rectangle count is the
right-associated sum of the three singleton defect imported-rectangle counts. -/
theorem TraceTransport.leftTripleAssociatedGradedDefect_importedRectangleCount
    (first second third : TraceTransport) :
    (TraceTransport.leftTripleAssociatedGradedDefect
      first
      second
      third).importedRectangleCount =
      (TraceTransport.finiteChainAssociatedGradedDefect [first]).importedRectangleCount +
        ((TraceTransport.finiteChainAssociatedGradedDefect [second]).importedRectangleCount +
          (TraceTransport.finiteChainAssociatedGradedDefect [third]).importedRectangleCount) :=
  TraceTransport.finiteChainAssociatedGradedDefect_append_append_assoc_importedRectangleCount
    [first]
    [second]
    [third]

/-- The left-associated triple defect rectangle list is the right-associated
append of the three singleton defect rectangle lists. -/
theorem TraceTransport.leftTripleAssociatedGradedDefect_importedRectangles
    (first second third : TraceTransport) :
    (TraceTransport.leftTripleAssociatedGradedDefect
      first
      second
      third).importedRectangles =
      (TraceTransport.finiteChainAssociatedGradedDefect [first]).importedRectangles ++
        ((TraceTransport.finiteChainAssociatedGradedDefect [second]).importedRectangles ++
          (TraceTransport.finiteChainAssociatedGradedDefect [third]).importedRectangles) :=
  TraceTransport.finiteChainAssociatedGradedDefect_append_append_assoc_importedRectangles
    [first]
    [second]
    [third]

/-- The left-associated triple defect bookkeeping count is the right-associated
sum of the three singleton defect bookkeeping counts. -/
theorem TraceTransport.leftTripleAssociatedGradedDefect_traceBookkeepingCount
    (first second third : TraceTransport) :
    (TraceTransport.leftTripleAssociatedGradedDefect
      first
      second
      third).traceBookkeepingCount =
      (TraceTransport.finiteChainAssociatedGradedDefect [first]).traceBookkeepingCount +
        ((TraceTransport.finiteChainAssociatedGradedDefect [second]).traceBookkeepingCount +
          (TraceTransport.finiteChainAssociatedGradedDefect [third]).traceBookkeepingCount) :=
  TraceTransport.finiteChainAssociatedGradedDefect_append_append_assoc_traceBookkeepingCount
    [first]
    [second]
    [third]

end AnalyticMotives
end LFunctions
end Boundary

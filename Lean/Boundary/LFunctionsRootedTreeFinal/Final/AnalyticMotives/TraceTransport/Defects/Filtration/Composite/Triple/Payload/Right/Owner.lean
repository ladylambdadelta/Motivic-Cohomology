import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Defects.Filtration.Composite.Triple.Payload.Owner

/-!
# Right-associated triple composite payload formulas

This file transports the left-associated triple payload formulas across the
triple rebracketing equality.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The right-associated triple defect rewrite-step count is the
right-associated sum of the three singleton defect rewrite-step counts. -/
theorem TraceTransport.rightTripleAssociatedGradedDefect_rewriteStepCount
    (first second third : TraceTransport) :
    (TraceTransport.rightTripleAssociatedGradedDefect
      first
      second
      third).rewriteStepCount =
      (TraceTransport.finiteChainAssociatedGradedDefect [first]).rewriteStepCount +
        ((TraceTransport.finiteChainAssociatedGradedDefect [second]).rewriteStepCount +
          (TraceTransport.finiteChainAssociatedGradedDefect [third]).rewriteStepCount) :=
  Eq.trans
    (Eq.symm
      (TraceTransport.tripleAssociatedGradedDefect_rebracket_rewriteStepCount
        first
        second
        third))
    (TraceTransport.leftTripleAssociatedGradedDefect_rewriteStepCount
      first
      second
      third)

/-- The right-associated triple defect imported-rectangle count is the
right-associated sum of the three singleton defect imported-rectangle counts. -/
theorem TraceTransport.rightTripleAssociatedGradedDefect_importedRectangleCount
    (first second third : TraceTransport) :
    (TraceTransport.rightTripleAssociatedGradedDefect
      first
      second
      third).importedRectangleCount =
      (TraceTransport.finiteChainAssociatedGradedDefect [first]).importedRectangleCount +
        ((TraceTransport.finiteChainAssociatedGradedDefect [second]).importedRectangleCount +
          (TraceTransport.finiteChainAssociatedGradedDefect [third]).importedRectangleCount) :=
  Eq.trans
    (Eq.symm
      (TraceTransport.tripleAssociatedGradedDefect_rebracket_importedRectangleCount
        first
        second
        third))
    (TraceTransport.leftTripleAssociatedGradedDefect_importedRectangleCount
      first
      second
      third)

/-- The right-associated triple defect rectangle list is the right-associated
append of the three singleton defect rectangle lists. -/
theorem TraceTransport.rightTripleAssociatedGradedDefect_importedRectangles
    (first second third : TraceTransport) :
    (TraceTransport.rightTripleAssociatedGradedDefect
      first
      second
      third).importedRectangles =
      (TraceTransport.finiteChainAssociatedGradedDefect [first]).importedRectangles ++
        ((TraceTransport.finiteChainAssociatedGradedDefect [second]).importedRectangles ++
          (TraceTransport.finiteChainAssociatedGradedDefect [third]).importedRectangles) :=
  Eq.trans
    (Eq.symm
      (TraceTransport.tripleAssociatedGradedDefect_rebracket_importedRectangles
        first
        second
        third))
    (TraceTransport.leftTripleAssociatedGradedDefect_importedRectangles
      first
      second
      third)

/-- The right-associated triple defect bookkeeping count is the right-associated
sum of the three singleton defect bookkeeping counts. -/
theorem TraceTransport.rightTripleAssociatedGradedDefect_traceBookkeepingCount
    (first second third : TraceTransport) :
    (TraceTransport.rightTripleAssociatedGradedDefect
      first
      second
      third).traceBookkeepingCount =
      (TraceTransport.finiteChainAssociatedGradedDefect [first]).traceBookkeepingCount +
        ((TraceTransport.finiteChainAssociatedGradedDefect [second]).traceBookkeepingCount +
          (TraceTransport.finiteChainAssociatedGradedDefect [third]).traceBookkeepingCount) :=
  Eq.trans
    (Eq.symm
      (TraceTransport.tripleAssociatedGradedDefect_rebracket_traceBookkeepingCount
        first
        second
        third))
    (TraceTransport.leftTripleAssociatedGradedDefect_traceBookkeepingCount
      first
      second
      third)

end AnalyticMotives
end LFunctions
end Boundary

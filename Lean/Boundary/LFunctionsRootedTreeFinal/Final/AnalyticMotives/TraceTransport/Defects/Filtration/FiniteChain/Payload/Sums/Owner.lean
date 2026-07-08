import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Defects.Filtration.FiniteChain.Owner

/-!
# Recursive payload sums for finite-chain defect filtrations

This file gives recursive normal forms for the payloads of a finite-chain
associated-graded defect ledger.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The recursive imported-rectangle count of a transport chain. -/
def TraceTransport.finiteChainDefectImportedRectangleCount :
    List TraceTransport → Nat
  | [] => 0
  | transport :: tail =>
      transport.defectLedger.importedRectangleCount +
        TraceTransport.finiteChainDefectImportedRectangleCount tail

/-- The recursive imported-rectangle list of a transport chain. -/
def TraceTransport.finiteChainDefectImportedRectangles :
    List TraceTransport → List ZetaAdmissibleFunction.ExplicitFormulaRectangle
  | [] => []
  | transport :: tail =>
      transport.defectLedger.importedRectangles ++
        TraceTransport.finiteChainDefectImportedRectangles tail

/-- The recursive bookkeeping count of a transport chain. -/
def TraceTransport.finiteChainDefectTraceBookkeepingCount :
    List TraceTransport → Nat
  | [] => 0
  | transport :: tail =>
      transport.defectLedger.traceBookkeepingCount +
        TraceTransport.finiteChainDefectTraceBookkeepingCount tail

/-- The recursive rewrite-step count of a transport chain. -/
def TraceTransport.finiteChainDefectRewriteStepCount :
    List TraceTransport → Nat
  | [] => 0
  | transport :: tail =>
      transport.defectLedger.rewriteStepCount +
        TraceTransport.finiteChainDefectRewriteStepCount tail

/-- The associated-graded finite-chain imported-rectangle count is the recursive
sum of transport-defect imported-rectangle counts. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_importedRectangleCount_eq_sum
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect chain).importedRectangleCount =
      TraceTransport.finiteChainDefectImportedRectangleCount chain :=
  match chain with
  | [] => rfl
  | transport :: tail =>
      Eq.trans
        (TraceTransport.finiteChainAssociatedGradedDefect_cons_importedRectangleCount
          transport
          tail)
        (congrArg
          (fun count =>
            transport.defectLedger.importedRectangleCount + count)
          (TraceTransport.finiteChainAssociatedGradedDefect_importedRectangleCount_eq_sum
            tail))

/-- The associated-graded finite-chain rectangle list is the recursive append of
transport-defect rectangle lists. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_importedRectangles_eq_sum
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect chain).importedRectangles =
      TraceTransport.finiteChainDefectImportedRectangles chain :=
  match chain with
  | [] => rfl
  | transport :: tail =>
      Eq.trans
        (TraceTransport.finiteChainAssociatedGradedDefect_cons_importedRectangles
          transport
          tail)
        (congrArg
          (fun rectangles =>
            transport.defectLedger.importedRectangles ++ rectangles)
          (TraceTransport.finiteChainAssociatedGradedDefect_importedRectangles_eq_sum
            tail))

/-- The associated-graded finite-chain bookkeeping count is the recursive sum of
transport-defect bookkeeping counts. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_traceBookkeepingCount_eq_sum
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect chain).traceBookkeepingCount =
      TraceTransport.finiteChainDefectTraceBookkeepingCount chain :=
  match chain with
  | [] => rfl
  | transport :: tail =>
      Eq.trans
        (TraceTransport.finiteChainAssociatedGradedDefect_cons_traceBookkeepingCount
          transport
          tail)
        (congrArg
          (fun count =>
            transport.defectLedger.traceBookkeepingCount + count)
          (TraceTransport.finiteChainAssociatedGradedDefect_traceBookkeepingCount_eq_sum
            tail))

/-- The associated-graded finite-chain rewrite-step count is the recursive sum
of transport-defect rewrite-step counts. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_rewriteStepCount_eq_sum
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect chain).rewriteStepCount =
      TraceTransport.finiteChainDefectRewriteStepCount chain :=
  match chain with
  | [] => rfl
  | transport :: tail =>
      Eq.trans
        (TraceTransport.finiteChainAssociatedGradedDefect_cons_rewriteStepCount
          transport
          tail)
        (congrArg
          (fun count =>
            transport.defectLedger.rewriteStepCount + count)
          (TraceTransport.finiteChainAssociatedGradedDefect_rewriteStepCount_eq_sum
            tail))

end AnalyticMotives
end LFunctions
end Boundary

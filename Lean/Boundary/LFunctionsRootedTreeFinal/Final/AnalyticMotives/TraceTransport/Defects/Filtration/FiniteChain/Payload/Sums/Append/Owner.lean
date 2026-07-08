import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Defects.Filtration.FiniteChain.Payload.Sums.Owner

/-!
# Append laws for recursive finite-chain payload sums

This file proves that the recursive payload sums attached to finite transport
chains preserve concatenation of chains.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Recursive imported-rectangle counts preserve chain concatenation. -/
theorem TraceTransport.finiteChainDefectImportedRectangleCount_append
    (first second : List TraceTransport) :
    TraceTransport.finiteChainDefectImportedRectangleCount (first ++ second) =
      TraceTransport.finiteChainDefectImportedRectangleCount first +
        TraceTransport.finiteChainDefectImportedRectangleCount second :=
  match first with
  | [] => rfl
  | transport :: tail =>
      Eq.trans
        (congrArg
          (fun count =>
            transport.defectLedger.importedRectangleCount + count)
          (TraceTransport.finiteChainDefectImportedRectangleCount_append
            tail
            second))
        (Eq.symm
          (Nat.add_assoc
            transport.defectLedger.importedRectangleCount
            (TraceTransport.finiteChainDefectImportedRectangleCount tail)
            (TraceTransport.finiteChainDefectImportedRectangleCount second)))

/-- Recursive imported-rectangle lists preserve chain concatenation. -/
theorem TraceTransport.finiteChainDefectImportedRectangles_append
    (first second : List TraceTransport) :
    TraceTransport.finiteChainDefectImportedRectangles (first ++ second) =
      TraceTransport.finiteChainDefectImportedRectangles first ++
        TraceTransport.finiteChainDefectImportedRectangles second :=
  match first with
  | [] => rfl
  | transport :: tail =>
      Eq.trans
        (congrArg
          (fun rectangles =>
            transport.defectLedger.importedRectangles ++ rectangles)
          (TraceTransport.finiteChainDefectImportedRectangles_append
            tail
            second))
        (Eq.symm
          (List.append_assoc
            transport.defectLedger.importedRectangles
            (TraceTransport.finiteChainDefectImportedRectangles tail)
            (TraceTransport.finiteChainDefectImportedRectangles second)))

/-- Recursive trace-bookkeeping counts preserve chain concatenation. -/
theorem TraceTransport.finiteChainDefectTraceBookkeepingCount_append
    (first second : List TraceTransport) :
    TraceTransport.finiteChainDefectTraceBookkeepingCount (first ++ second) =
      TraceTransport.finiteChainDefectTraceBookkeepingCount first +
        TraceTransport.finiteChainDefectTraceBookkeepingCount second :=
  match first with
  | [] => rfl
  | transport :: tail =>
      Eq.trans
        (congrArg
          (fun count =>
            transport.defectLedger.traceBookkeepingCount + count)
          (TraceTransport.finiteChainDefectTraceBookkeepingCount_append
            tail
            second))
        (Eq.symm
          (Nat.add_assoc
            transport.defectLedger.traceBookkeepingCount
            (TraceTransport.finiteChainDefectTraceBookkeepingCount tail)
            (TraceTransport.finiteChainDefectTraceBookkeepingCount second)))

/-- Recursive rewrite-step counts preserve chain concatenation. -/
theorem TraceTransport.finiteChainDefectRewriteStepCount_append
    (first second : List TraceTransport) :
    TraceTransport.finiteChainDefectRewriteStepCount (first ++ second) =
      TraceTransport.finiteChainDefectRewriteStepCount first +
        TraceTransport.finiteChainDefectRewriteStepCount second :=
  match first with
  | [] => rfl
  | transport :: tail =>
      Eq.trans
        (congrArg
          (fun count =>
            transport.defectLedger.rewriteStepCount + count)
          (TraceTransport.finiteChainDefectRewriteStepCount_append
            tail
            second))
        (Eq.symm
          (Nat.add_assoc
            transport.defectLedger.rewriteStepCount
            (TraceTransport.finiteChainDefectRewriteStepCount tail)
            (TraceTransport.finiteChainDefectRewriteStepCount second)))

end AnalyticMotives
end LFunctions
end Boundary

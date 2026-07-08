import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Defects.Filtration.FiniteChain.Payload.Sums.Append.Owner

/-!
# Unit laws for recursive finite-chain payload sums

This file records the empty-chain unit laws for recursive payload sums attached
to finite transport chains.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Empty left append preserves recursive imported-rectangle counts. -/
theorem TraceTransport.finiteChainDefectImportedRectangleCount_empty_append
    (chain : List TraceTransport) :
    TraceTransport.finiteChainDefectImportedRectangleCount ([] ++ chain) =
      TraceTransport.finiteChainDefectImportedRectangleCount chain :=
  rfl

/-- Empty right append preserves recursive imported-rectangle counts. -/
theorem TraceTransport.finiteChainDefectImportedRectangleCount_append_empty
    (chain : List TraceTransport) :
    TraceTransport.finiteChainDefectImportedRectangleCount (chain ++ []) =
      TraceTransport.finiteChainDefectImportedRectangleCount chain :=
  Eq.trans
    (TraceTransport.finiteChainDefectImportedRectangleCount_append
      chain
      [])
    (Nat.add_zero
      (TraceTransport.finiteChainDefectImportedRectangleCount chain))

/-- Empty left append preserves recursive imported-rectangle lists. -/
theorem TraceTransport.finiteChainDefectImportedRectangles_empty_append
    (chain : List TraceTransport) :
    TraceTransport.finiteChainDefectImportedRectangles ([] ++ chain) =
      TraceTransport.finiteChainDefectImportedRectangles chain :=
  rfl

/-- Empty right append preserves recursive imported-rectangle lists. -/
theorem TraceTransport.finiteChainDefectImportedRectangles_append_empty
    (chain : List TraceTransport) :
    TraceTransport.finiteChainDefectImportedRectangles (chain ++ []) =
      TraceTransport.finiteChainDefectImportedRectangles chain :=
  Eq.trans
    (TraceTransport.finiteChainDefectImportedRectangles_append
      chain
      [])
    (List.append_nil
      (TraceTransport.finiteChainDefectImportedRectangles chain))

/-- Empty left append preserves recursive bookkeeping counts. -/
theorem TraceTransport.finiteChainDefectTraceBookkeepingCount_empty_append
    (chain : List TraceTransport) :
    TraceTransport.finiteChainDefectTraceBookkeepingCount ([] ++ chain) =
      TraceTransport.finiteChainDefectTraceBookkeepingCount chain :=
  rfl

/-- Empty right append preserves recursive bookkeeping counts. -/
theorem TraceTransport.finiteChainDefectTraceBookkeepingCount_append_empty
    (chain : List TraceTransport) :
    TraceTransport.finiteChainDefectTraceBookkeepingCount (chain ++ []) =
      TraceTransport.finiteChainDefectTraceBookkeepingCount chain :=
  Eq.trans
    (TraceTransport.finiteChainDefectTraceBookkeepingCount_append
      chain
      [])
    (Nat.add_zero
      (TraceTransport.finiteChainDefectTraceBookkeepingCount chain))

/-- Empty left append preserves recursive rewrite-step counts. -/
theorem TraceTransport.finiteChainDefectRewriteStepCount_empty_append
    (chain : List TraceTransport) :
    TraceTransport.finiteChainDefectRewriteStepCount ([] ++ chain) =
      TraceTransport.finiteChainDefectRewriteStepCount chain :=
  rfl

/-- Empty right append preserves recursive rewrite-step counts. -/
theorem TraceTransport.finiteChainDefectRewriteStepCount_append_empty
    (chain : List TraceTransport) :
    TraceTransport.finiteChainDefectRewriteStepCount (chain ++ []) =
      TraceTransport.finiteChainDefectRewriteStepCount chain :=
  Eq.trans
    (TraceTransport.finiteChainDefectRewriteStepCount_append
      chain
      [])
    (Nat.add_zero
      (TraceTransport.finiteChainDefectRewriteStepCount chain))

end AnalyticMotives
end LFunctions
end Boundary

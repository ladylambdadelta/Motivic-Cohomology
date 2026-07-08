import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Defects.Filtration.FiniteChain.Payload.Sums.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Defects.Filtration.FiniteChain.Units.Owner

/-!
# Associated-graded unit payloads as recursive sums

This file combines finite-chain associated-graded unit laws with the recursive
payload-sum normal forms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The imported-rectangle count of a left-unit associated-graded finite-chain
defect is the recursive imported-rectangle count. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_empty_append_importedRectangleCount_eq_sum
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ([] ++ chain)).importedRectangleCount =
      TraceTransport.finiteChainDefectImportedRectangleCount chain :=
  Eq.trans
    (TraceTransport.finiteChainAssociatedGradedDefect_empty_append_importedRectangleCount
      chain)
    (TraceTransport.finiteChainAssociatedGradedDefect_importedRectangleCount_eq_sum
      chain)

/-- The imported-rectangle count of a right-unit associated-graded finite-chain
defect is the recursive imported-rectangle count. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_append_empty_importedRectangleCount_eq_sum
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (chain ++ [])).importedRectangleCount =
      TraceTransport.finiteChainDefectImportedRectangleCount chain :=
  Eq.trans
    (TraceTransport.finiteChainAssociatedGradedDefect_append_empty_importedRectangleCount
      chain)
    (TraceTransport.finiteChainAssociatedGradedDefect_importedRectangleCount_eq_sum
      chain)

/-- The imported-rectangle list of a left-unit associated-graded finite-chain
defect is the recursive imported-rectangle list. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_empty_append_importedRectangles_eq_sum
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ([] ++ chain)).importedRectangles =
      TraceTransport.finiteChainDefectImportedRectangles chain :=
  Eq.trans
    (TraceTransport.finiteChainAssociatedGradedDefect_empty_append_importedRectangles
      chain)
    (TraceTransport.finiteChainAssociatedGradedDefect_importedRectangles_eq_sum
      chain)

/-- The imported-rectangle list of a right-unit associated-graded finite-chain
defect is the recursive imported-rectangle list. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_append_empty_importedRectangles_eq_sum
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (chain ++ [])).importedRectangles =
      TraceTransport.finiteChainDefectImportedRectangles chain :=
  Eq.trans
    (TraceTransport.finiteChainAssociatedGradedDefect_append_empty_importedRectangles
      chain)
    (TraceTransport.finiteChainAssociatedGradedDefect_importedRectangles_eq_sum
      chain)

/-- The bookkeeping count of a left-unit associated-graded finite-chain defect is
the recursive bookkeeping count. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_empty_append_traceBookkeepingCount_eq_sum
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ([] ++ chain)).traceBookkeepingCount =
      TraceTransport.finiteChainDefectTraceBookkeepingCount chain :=
  Eq.trans
    (TraceTransport.finiteChainAssociatedGradedDefect_empty_append_traceBookkeepingCount
      chain)
    (TraceTransport.finiteChainAssociatedGradedDefect_traceBookkeepingCount_eq_sum
      chain)

/-- The bookkeeping count of a right-unit associated-graded finite-chain defect is
the recursive bookkeeping count. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_append_empty_traceBookkeepingCount_eq_sum
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (chain ++ [])).traceBookkeepingCount =
      TraceTransport.finiteChainDefectTraceBookkeepingCount chain :=
  Eq.trans
    (TraceTransport.finiteChainAssociatedGradedDefect_append_empty_traceBookkeepingCount
      chain)
    (TraceTransport.finiteChainAssociatedGradedDefect_traceBookkeepingCount_eq_sum
      chain)

/-- The rewrite-step count of a left-unit associated-graded finite-chain defect is
the recursive rewrite-step count. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_empty_append_rewriteStepCount_eq_sum
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ([] ++ chain)).rewriteStepCount =
      TraceTransport.finiteChainDefectRewriteStepCount chain :=
  Eq.trans
    (TraceTransport.finiteChainAssociatedGradedDefect_empty_append_rewriteStepCount
      chain)
    (TraceTransport.finiteChainAssociatedGradedDefect_rewriteStepCount_eq_sum
      chain)

/-- The rewrite-step count of a right-unit associated-graded finite-chain defect is
the recursive rewrite-step count. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_append_empty_rewriteStepCount_eq_sum
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (chain ++ [])).rewriteStepCount =
      TraceTransport.finiteChainDefectRewriteStepCount chain :=
  Eq.trans
    (TraceTransport.finiteChainAssociatedGradedDefect_append_empty_rewriteStepCount
      chain)
    (TraceTransport.finiteChainAssociatedGradedDefect_rewriteStepCount_eq_sum
      chain)

end AnalyticMotives
end LFunctions
end Boundary

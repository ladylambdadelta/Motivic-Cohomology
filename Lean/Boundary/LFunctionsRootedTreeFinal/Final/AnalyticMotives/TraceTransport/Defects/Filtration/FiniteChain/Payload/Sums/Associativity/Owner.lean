import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Defects.Filtration.FiniteChain.Payload.Sums.Append.Owner

/-!
# Associativity laws for recursive finite-chain payload sums

This file proves three-block associativity and list-rebracketing laws for the
recursive payload sums attached to finite transport chains.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Three-block append associativity for recursive imported-rectangle counts. -/
theorem TraceTransport.finiteChainDefectImportedRectangleCount_append_append_assoc
    (first second third : List TraceTransport) :
    TraceTransport.finiteChainDefectImportedRectangleCount ((first ++ second) ++ third) =
      TraceTransport.finiteChainDefectImportedRectangleCount first +
        (TraceTransport.finiteChainDefectImportedRectangleCount second +
          TraceTransport.finiteChainDefectImportedRectangleCount third) :=
  Eq.trans
    (TraceTransport.finiteChainDefectImportedRectangleCount_append
      (first ++ second)
      third)
    (Eq.trans
      (congrArg
        (fun count =>
          count + TraceTransport.finiteChainDefectImportedRectangleCount third)
        (TraceTransport.finiteChainDefectImportedRectangleCount_append
          first
          second))
      (Nat.add_assoc
        (TraceTransport.finiteChainDefectImportedRectangleCount first)
        (TraceTransport.finiteChainDefectImportedRectangleCount second)
        (TraceTransport.finiteChainDefectImportedRectangleCount third)))

/-- Rebracketing preserves recursive imported-rectangle counts. -/
theorem TraceTransport.finiteChainDefectImportedRectangleCount_rebracket
    (first second third : List TraceTransport) :
    TraceTransport.finiteChainDefectImportedRectangleCount ((first ++ second) ++ third) =
      TraceTransport.finiteChainDefectImportedRectangleCount (first ++ (second ++ third)) :=
  congrArg
    TraceTransport.finiteChainDefectImportedRectangleCount
    (List.append_assoc
      first
      second
      third)

/-- Three-block append associativity for recursive imported-rectangle lists. -/
theorem TraceTransport.finiteChainDefectImportedRectangles_append_append_assoc
    (first second third : List TraceTransport) :
    TraceTransport.finiteChainDefectImportedRectangles ((first ++ second) ++ third) =
      TraceTransport.finiteChainDefectImportedRectangles first ++
        (TraceTransport.finiteChainDefectImportedRectangles second ++
          TraceTransport.finiteChainDefectImportedRectangles third) :=
  Eq.trans
    (TraceTransport.finiteChainDefectImportedRectangles_append
      (first ++ second)
      third)
    (Eq.trans
      (congrArg
        (fun rectangles =>
          rectangles ++ TraceTransport.finiteChainDefectImportedRectangles third)
        (TraceTransport.finiteChainDefectImportedRectangles_append
          first
          second))
      (List.append_assoc
        (TraceTransport.finiteChainDefectImportedRectangles first)
        (TraceTransport.finiteChainDefectImportedRectangles second)
        (TraceTransport.finiteChainDefectImportedRectangles third)))

/-- Rebracketing preserves recursive imported-rectangle lists. -/
theorem TraceTransport.finiteChainDefectImportedRectangles_rebracket
    (first second third : List TraceTransport) :
    TraceTransport.finiteChainDefectImportedRectangles ((first ++ second) ++ third) =
      TraceTransport.finiteChainDefectImportedRectangles (first ++ (second ++ third)) :=
  congrArg
    TraceTransport.finiteChainDefectImportedRectangles
    (List.append_assoc
      first
      second
      third)

/-- Three-block append associativity for recursive trace-bookkeeping counts. -/
theorem TraceTransport.finiteChainDefectTraceBookkeepingCount_append_append_assoc
    (first second third : List TraceTransport) :
    TraceTransport.finiteChainDefectTraceBookkeepingCount ((first ++ second) ++ third) =
      TraceTransport.finiteChainDefectTraceBookkeepingCount first +
        (TraceTransport.finiteChainDefectTraceBookkeepingCount second +
          TraceTransport.finiteChainDefectTraceBookkeepingCount third) :=
  Eq.trans
    (TraceTransport.finiteChainDefectTraceBookkeepingCount_append
      (first ++ second)
      third)
    (Eq.trans
      (congrArg
        (fun count =>
          count + TraceTransport.finiteChainDefectTraceBookkeepingCount third)
        (TraceTransport.finiteChainDefectTraceBookkeepingCount_append
          first
          second))
      (Nat.add_assoc
        (TraceTransport.finiteChainDefectTraceBookkeepingCount first)
        (TraceTransport.finiteChainDefectTraceBookkeepingCount second)
        (TraceTransport.finiteChainDefectTraceBookkeepingCount third)))

/-- Rebracketing preserves recursive trace-bookkeeping counts. -/
theorem TraceTransport.finiteChainDefectTraceBookkeepingCount_rebracket
    (first second third : List TraceTransport) :
    TraceTransport.finiteChainDefectTraceBookkeepingCount ((first ++ second) ++ third) =
      TraceTransport.finiteChainDefectTraceBookkeepingCount (first ++ (second ++ third)) :=
  congrArg
    TraceTransport.finiteChainDefectTraceBookkeepingCount
    (List.append_assoc
      first
      second
      third)

/-- Three-block append associativity for recursive rewrite-step counts. -/
theorem TraceTransport.finiteChainDefectRewriteStepCount_append_append_assoc
    (first second third : List TraceTransport) :
    TraceTransport.finiteChainDefectRewriteStepCount ((first ++ second) ++ third) =
      TraceTransport.finiteChainDefectRewriteStepCount first +
        (TraceTransport.finiteChainDefectRewriteStepCount second +
          TraceTransport.finiteChainDefectRewriteStepCount third) :=
  Eq.trans
    (TraceTransport.finiteChainDefectRewriteStepCount_append
      (first ++ second)
      third)
    (Eq.trans
      (congrArg
        (fun count =>
          count + TraceTransport.finiteChainDefectRewriteStepCount third)
        (TraceTransport.finiteChainDefectRewriteStepCount_append
          first
          second))
      (Nat.add_assoc
        (TraceTransport.finiteChainDefectRewriteStepCount first)
        (TraceTransport.finiteChainDefectRewriteStepCount second)
        (TraceTransport.finiteChainDefectRewriteStepCount third)))

/-- Rebracketing preserves recursive rewrite-step counts. -/
theorem TraceTransport.finiteChainDefectRewriteStepCount_rebracket
    (first second third : List TraceTransport) :
    TraceTransport.finiteChainDefectRewriteStepCount ((first ++ second) ++ third) =
      TraceTransport.finiteChainDefectRewriteStepCount (first ++ (second ++ third)) :=
  congrArg
    TraceTransport.finiteChainDefectRewriteStepCount
    (List.append_assoc
      first
      second
      third)

end AnalyticMotives
end LFunctions
end Boundary

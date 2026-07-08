import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.FormalSums.Constructors.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.FormalSums.Terms.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.FormalSums.Additive.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.FormalSums.Scalars.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.FormalSums.Composition.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.FormalSums.TermRight.Owner

/-!
# Top-root formal-sum trace-correspondence facades

This file collects public formal-sum facades that are split out of the main
`Root/TraceCorQ` owner to keep the public import boundary below the line cap.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Formal-sum aggregate: zero has no imported rectangle payload. -/
theorem AnalyticMotivesRoot.traceCorQFormalSumSummary_zero_importedRectangleCount :
    TraceCorQFormalSum.zero.importedRectangleCount =
      0 :=
  AnalyticMotivesRoot.traceCorQFormalSum_zero_importedRectangleCount

/-- Formal-sum aggregate: singleton payload count is the generator payload count plus empty ledger. -/
theorem AnalyticMotivesRoot.traceCorQFormalSumSummary_singleton_importedRectangleCount
    (coefficient : Rat) (generator : TraceCorQGenerator) :
    (TraceCorQFormalSum.singleton coefficient generator).importedRectangleCount =
      generator.importedRectangleCount +
        ResidueChannelCertificateLedger.empty.importedRectangleCount :=
  AnalyticMotivesRoot.traceCorQFormalSum_singleton_importedRectangleCount
    coefficient
    generator

/-- Formal-sum aggregate: cons payload counts add term and tail counts. -/
theorem AnalyticMotivesRoot.traceCorQFormalSumSummary_cons_importedRectangleCount
    (term : TraceCorQTerm) (tail : TraceCorQFormalSum) :
    TraceCorQFormalSum.importedRectangleCount (term :: tail) =
      term.importedRectangleCount +
        tail.importedRectangleCount :=
  AnalyticMotivesRoot.traceCorQFormalSum_cons_importedRectangleCount
    term
    tail

/-- Formal-sum aggregate: zero is a left additive identity. -/
theorem AnalyticMotivesRoot.traceCorQFormalSumSummary_zero_add
    (formalSum : TraceCorQFormalSum) :
    TraceCorQFormalSum.add TraceCorQFormalSum.zero formalSum =
      formalSum :=
  AnalyticMotivesRoot.traceCorQFormalSum_zero_add
    formalSum

/-- Formal-sum aggregate: scalar multiplication distributes over formal-sum addition. -/
theorem AnalyticMotivesRoot.traceCorQFormalSumSummary_smul_add
    (coefficient : Rat)
    (left right : TraceCorQFormalSum) :
    TraceCorQFormalSum.smul coefficient
        (TraceCorQFormalSum.add left right) =
      TraceCorQFormalSum.add
        (TraceCorQFormalSum.smul coefficient left)
        (TraceCorQFormalSum.smul coefficient right) :=
  AnalyticMotivesRoot.traceCorQFormalSum_smul_add
    coefficient
    left
    right

/-- Formal-sum aggregate: composition distributes over addition on the left. -/
theorem AnalyticMotivesRoot.traceCorQFormalSumSummary_add_comp
    (left right tail : TraceCorQFormalSum) :
    TraceCorQFormalSum.comp
      (TraceCorQFormalSum.add left right)
      tail =
      TraceCorQFormalSum.add
        (TraceCorQFormalSum.comp left tail)
        (TraceCorQFormalSum.comp right tail) :=
  AnalyticMotivesRoot.traceCorQFormalSum_compSummary_add_comp
    left
    right
    tail

/-- Formal-sum aggregate: scalar multiplication commutes with composition on the left. -/
theorem AnalyticMotivesRoot.traceCorQFormalSumSummary_smul_comp
    (coefficient : Rat)
    (left right : TraceCorQFormalSum) :
    TraceCorQFormalSum.comp
      (TraceCorQFormalSum.smul coefficient left)
      right =
      TraceCorQFormalSum.smul
        coefficient
        (TraceCorQFormalSum.comp left right) :=
  AnalyticMotivesRoot.traceCorQFormalSum_compSummary_smul_comp
    coefficient
    left
    right

end AnalyticMotives
end LFunctions
end Boundary

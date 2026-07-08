import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Payload.Owner

/-!
# Public typed hom payload length facts

This file exposes imported-rectangle count equals list-length facts for typed
trace-correspondence hom terms, formal sums, and representatives.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes generator-term rectangle count as list length. -/
theorem AnalyticMotivesRoot.traceCorQHomPayload_term_ofGenerator_importedRectangleCount_eq_length
    (source target : TraceCorQObject)
    (coefficient : Rat)
    (generator : TraceCorQGenerator)
    (source_eq : generator.source = source)
    (target_eq : generator.target = target) :
    (TraceCorQHomTerm.ofGenerator
      source
      target
      coefficient
      generator
      source_eq
      target_eq).importedRectangleCount =
      (TraceCorQHomTerm.ofGenerator
        source
        target
        coefficient
        generator
        source_eq
        target_eq).importedRectangles.length :=
  TraceCorQHomPayload.term_ofGenerator_importedRectangleCount_eq_length
    source
    target
    coefficient
    generator
    source_eq
    target_eq

/-- The top root exposes zero formal-sum rectangle count as list length. -/
theorem AnalyticMotivesRoot.traceCorQHomPayload_formalSum_zero_importedRectangleCount_eq_length
    (source target : TraceCorQObject) :
    (TraceCorQHomFormalSum.zero source target).importedRectangleCount =
      (TraceCorQHomFormalSum.zero source target).importedRectangles.length :=
  TraceCorQHomPayload.formalSum_zero_importedRectangleCount_eq_length
    source
    target

/-- The top root exposes singleton formal-sum rectangle count as list length. -/
theorem AnalyticMotivesRoot.traceCorQHomPayload_formalSum_singleton_importedRectangleCount_eq_length
    (source target : TraceCorQObject)
    (coefficient : Rat)
    (generator : TraceCorQGenerator)
    (source_eq : generator.source = source)
    (target_eq : generator.target = target) :
    (TraceCorQHomFormalSum.singleton
      source
      target
      coefficient
      generator
      source_eq
      target_eq).importedRectangleCount =
      (TraceCorQHomFormalSum.singleton
        source
        target
        coefficient
        generator
        source_eq
        target_eq).importedRectangles.length :=
  TraceCorQHomPayload.formalSum_singleton_importedRectangleCount_eq_length
    source
    target
    coefficient
    generator
    source_eq
    target_eq

/-- The top root exposes added formal-sum rectangle count as list length. -/
theorem AnalyticMotivesRoot.traceCorQHomPayload_formalSum_add_importedRectangleCount_eq_length
    {source target : TraceCorQObject}
    (left right : TraceCorQHomFormalSum source target) :
    (TraceCorQHomFormalSum.add left right).importedRectangleCount =
      (TraceCorQHomFormalSum.add left right).importedRectangles.length :=
  TraceCorQHomPayload.formalSum_add_importedRectangleCount_eq_length
    left
    right

/-- The top root exposes zero representative rectangle count as list length. -/
theorem AnalyticMotivesRoot.traceCorQHomPayload_representative_zero_importedRectangleCount_eq_length
    (source target : TraceCorQObject) :
    (TraceCorQHomRepresentative.ofFormalSumLedger
      (TraceCorQHomFormalSum.zero source target)
      TraceCorQRelationLedger.empty).importedRectangleCount =
      (TraceCorQHomRepresentative.ofFormalSumLedger
        (TraceCorQHomFormalSum.zero source target)
        TraceCorQRelationLedger.empty).importedRectangles.length :=
  TraceCorQHomPayload.representative_zero_importedRectangleCount_eq_length
    source
    target

/-- The top root exposes singleton representative rectangle count as list length. -/
theorem AnalyticMotivesRoot.traceCorQHomPayload_representative_singleton_importedRectangleCount_eq_length
    (source target : TraceCorQObject)
    (coefficient : Rat)
    (generator : TraceCorQGenerator)
    (source_eq : generator.source = source)
    (target_eq : generator.target = target) :
    (TraceCorQHomRepresentative.ofFormalSumLedger
      (TraceCorQHomFormalSum.singleton
        source
        target
        coefficient
        generator
        source_eq
        target_eq)
      TraceCorQRelationLedger.empty).importedRectangleCount =
      (TraceCorQHomRepresentative.ofFormalSumLedger
        (TraceCorQHomFormalSum.singleton
          source
          target
          coefficient
          generator
          source_eq
          target_eq)
        TraceCorQRelationLedger.empty).importedRectangles.length :=
  TraceCorQHomPayload.representative_singleton_importedRectangleCount_eq_length
    source
    target
    coefficient
    generator
    source_eq
    target_eq

end AnalyticMotives
end LFunctions
end Boundary

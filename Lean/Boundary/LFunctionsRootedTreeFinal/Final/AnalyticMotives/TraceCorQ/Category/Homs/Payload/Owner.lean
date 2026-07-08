import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Payload.Lengths.Owner

/-!
# Typed hom payload facts

This file owns the typed-hom payload surface.  Nested files prove the concrete
length invariants; this owner re-exposes the facts at the payload boundary so
downstream files do not import the nested length owner directly.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The typed-hom payload surface exposes generator-term rectangle counts. -/
theorem TraceCorQHomPayload.term_ofGenerator_importedRectangleCount_eq_length
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
  TraceCorQHomTerm.ofGenerator_importedRectangleCount_eq_length
    source
    target
    coefficient
    generator
    source_eq
    target_eq

/-- The typed-hom payload surface exposes zero formal-sum rectangle counts. -/
theorem TraceCorQHomPayload.formalSum_zero_importedRectangleCount_eq_length
    (source target : TraceCorQObject) :
    (TraceCorQHomFormalSum.zero source target).importedRectangleCount =
      (TraceCorQHomFormalSum.zero source target).importedRectangles.length :=
  TraceCorQHomFormalSum.zero_importedRectangleCount_eq_length
    source
    target

/-- The typed-hom payload surface exposes singleton formal-sum rectangle counts. -/
theorem TraceCorQHomPayload.formalSum_singleton_importedRectangleCount_eq_length
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
  TraceCorQHomFormalSum.singleton_importedRectangleCount_eq_length
    source
    target
    coefficient
    generator
    source_eq
    target_eq

/-- The typed-hom payload surface exposes additive formal-sum rectangle counts. -/
theorem TraceCorQHomPayload.formalSum_add_importedRectangleCount_eq_length
    {source target : TraceCorQObject}
    (left right : TraceCorQHomFormalSum source target) :
    (TraceCorQHomFormalSum.add left right).importedRectangleCount =
      (TraceCorQHomFormalSum.add left right).importedRectangles.length :=
  TraceCorQHomFormalSum.add_importedRectangleCount_eq_length
    left
    right

/-- The typed-hom payload surface exposes zero representative rectangle counts. -/
theorem TraceCorQHomPayload.representative_zero_importedRectangleCount_eq_length
    (source target : TraceCorQObject) :
    (TraceCorQHomRepresentative.ofFormalSumLedger
      (TraceCorQHomFormalSum.zero source target)
      TraceCorQRelationLedger.empty).importedRectangleCount =
      (TraceCorQHomRepresentative.ofFormalSumLedger
        (TraceCorQHomFormalSum.zero source target)
        TraceCorQRelationLedger.empty).importedRectangles.length :=
  TraceCorQHomRepresentative.zero_importedRectangleCount_eq_length
    source
    target

/-- The typed-hom payload surface exposes singleton representative rectangle counts. -/
theorem TraceCorQHomPayload.representative_singleton_importedRectangleCount_eq_length
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
  TraceCorQHomRepresentative.singleton_emptyLedger_importedRectangleCount_eq_length
    source
    target
    coefficient
    generator
    source_eq
    target_eq

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Certificates.Owner

/-!
# Typed hom payload length facts

This file owns imported-rectangle length invariants for typed hom terms,
typed formal-sum constructors, and typed representative constructors.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A typed generator term built from a generator has count equal to rectangle-list length. -/
theorem TraceCorQHomTerm.ofGenerator_importedRectangleCount_eq_length
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
  TraceCorQHomTerm.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQHomTerm.ofGenerator
      source
      target
      coefficient
      generator
      source_eq
      target_eq)

/-- The zero typed formal sum has count equal to rectangle-list length. -/
theorem TraceCorQHomFormalSum.zero_importedRectangleCount_eq_length
    (source target : TraceCorQObject) :
    (TraceCorQHomFormalSum.zero source target).importedRectangleCount =
      (TraceCorQHomFormalSum.zero source target).importedRectangles.length :=
  TraceCorQHomFormalSum.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQHomFormalSum.zero source target)

/-- A singleton typed formal sum has count equal to rectangle-list length. -/
theorem TraceCorQHomFormalSum.singleton_importedRectangleCount_eq_length
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
  TraceCorQHomFormalSum.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQHomFormalSum.singleton
      source
      target
      coefficient
      generator
      source_eq
      target_eq)

/-- An added typed formal sum has count equal to rectangle-list length. -/
theorem TraceCorQHomFormalSum.add_importedRectangleCount_eq_length
    {source target : TraceCorQObject}
    (left right : TraceCorQHomFormalSum source target) :
    (TraceCorQHomFormalSum.add left right).importedRectangleCount =
      (TraceCorQHomFormalSum.add left right).importedRectangles.length :=
  TraceCorQHomFormalSum.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQHomFormalSum.add left right)

/-- The zero typed representative has count equal to rectangle-list length. -/
theorem TraceCorQHomRepresentative.zero_importedRectangleCount_eq_length
    (source target : TraceCorQObject) :
    (TraceCorQHomRepresentative.ofFormalSumLedger
      (TraceCorQHomFormalSum.zero source target)
      TraceCorQRelationLedger.empty).importedRectangleCount =
      (TraceCorQHomRepresentative.ofFormalSumLedger
        (TraceCorQHomFormalSum.zero source target)
        TraceCorQRelationLedger.empty).importedRectangles.length :=
  TraceCorQHomRepresentative.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQHomRepresentative.ofFormalSumLedger
      (TraceCorQHomFormalSum.zero source target)
      TraceCorQRelationLedger.empty)

/-- A singleton typed representative has count equal to rectangle-list length. -/
theorem TraceCorQHomRepresentative.singleton_emptyLedger_importedRectangleCount_eq_length
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
  TraceCorQHomRepresentative.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQHomRepresentative.ofFormalSumLedger
      (TraceCorQHomFormalSum.singleton
        source
        target
        coefficient
        generator
        source_eq
        target_eq)
      TraceCorQRelationLedger.empty)

end AnalyticMotives
end LFunctions
end Boundary

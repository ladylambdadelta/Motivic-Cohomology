import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Terms.Owner

/-!
# Public typed trace-correspondence terms

This file exposes endpoint and payload formulas for typed weighted
trace-correspondence generator terms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes the raw weighted generator of a built typed hom term. -/
theorem AnalyticMotivesRoot.traceCorQHomTerm_ofGenerator_raw
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
      target_eq).raw =
      (coefficient, generator) :=
  TraceCorQHomTerm.ofGenerator_raw
    source
    target
    coefficient
    generator
    source_eq
    target_eq

/-- The top root exposes generator-term certificate ledgers. -/
theorem AnalyticMotivesRoot.traceCorQHomTerm_ofGenerator_certificateLedger
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
      target_eq).certificateLedger =
      generator.certificateLedger :=
  TraceCorQHomTerm.ofGenerator_certificateLedger
    source
    target
    coefficient
    generator
    source_eq
    target_eq

/-- The top root exposes generator-term imported counts. -/
theorem AnalyticMotivesRoot.traceCorQHomTerm_ofGenerator_importedRectangleCount
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
      generator.importedRectangleCount :=
  TraceCorQHomTerm.ofGenerator_importedRectangleCount
    source
    target
    coefficient
    generator
    source_eq
    target_eq

/-- The top root exposes generator-term imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQHomTerm_ofGenerator_importedRectangles
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
      target_eq).importedRectangles =
      generator.importedRectangles :=
  TraceCorQHomTerm.ofGenerator_importedRectangles
    source
    target
    coefficient
    generator
    source_eq
    target_eq

/-- The top root exposes generator-term bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQHomTerm_ofGenerator_traceBookkeepingCount
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
      target_eq).traceBookkeepingCount =
      generator.traceBookkeepingCount :=
  TraceCorQHomTerm.ofGenerator_traceBookkeepingCount
    source
    target
    coefficient
    generator
    source_eq
    target_eq

/-- The top root exposes generator-term rewrite-step counts. -/
theorem AnalyticMotivesRoot.traceCorQHomTerm_ofGenerator_rewriteStepCount
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
      target_eq).rewriteStepCount =
      generator.rewriteStepCount :=
  TraceCorQHomTerm.ofGenerator_rewriteStepCount
    source
    target
    coefficient
    generator
    source_eq
    target_eq

/-- The top root exposes typed hom term rewrite-step counts as raw counts. -/
theorem AnalyticMotivesRoot.traceCorQHomTerm_rewriteStepCount_eq_raw
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target) :
    term.rewriteStepCount =
      term.raw.rewriteStepCount :=
  TraceCorQHomTerm.rewriteStepCount_eq_raw
    term

/-- The top root exposes typed hom term imported rectangles as raw rectangles. -/
theorem AnalyticMotivesRoot.traceCorQHomTerm_importedRectangles_eq_raw
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target) :
    term.importedRectangles =
      term.raw.importedRectangles :=
  TraceCorQHomTerm.importedRectangles_eq_raw
    term

/-- The top root exposes typed hom term imported counts as list lengths. -/
theorem AnalyticMotivesRoot.traceCorQHomTerm_importedRectangleCount_eq_length_importedRectangles
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target) :
    term.importedRectangleCount =
      term.importedRectangles.length :=
  TraceCorQHomTerm.importedRectangleCount_eq_length_importedRectangles
    term

end AnalyticMotives
end LFunctions
end Boundary

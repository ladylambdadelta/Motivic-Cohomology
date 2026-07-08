import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Terms.Owner

/-!
# Composition of typed hom terms

This file owns composition of one typed weighted generator with another.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Compose typed hom terms by multiplying coefficients and composing generators. -/
def TraceCorQHomTerm.comp
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomTerm source middle)
    (right : TraceCorQHomTerm middle target) :
    TraceCorQHomTerm source target :=
  TraceCorQHomTerm.ofGenerator
    source
    target
    (left.coefficient * right.coefficient)
    (TraceCorQGenerator.comp left.generator right.generator)
    (Eq.trans
      (TraceCorQGenerator.comp_source left.generator right.generator)
      (TraceCorQHomTerm.generator_source left))
    (Eq.trans
      (TraceCorQGenerator.comp_target left.generator right.generator)
      (TraceCorQHomTerm.generator_target right))

/-- The raw term of typed term composition is raw term composition. -/
theorem TraceCorQHomTerm.comp_raw
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomTerm source middle)
    (right : TraceCorQHomTerm middle target) :
    (TraceCorQHomTerm.comp left right).raw =
      (left.raw.1 * right.raw.1,
        TraceCorQGenerator.comp left.raw.2 right.raw.2) :=
  rfl

/-- Typed term composition carries the raw term-composition rewrite-step payload. -/
theorem TraceCorQHomTerm.comp_rewriteStepCount
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomTerm source middle)
    (right : TraceCorQHomTerm middle target) :
    (TraceCorQHomTerm.comp left right).rewriteStepCount =
      (TraceCorQTerm.comp left.raw right.raw).rewriteStepCount :=
  rfl

/-- Typed term composition carries the raw term-composition imported payload. -/
theorem TraceCorQHomTerm.comp_importedRectangleCount
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomTerm source middle)
    (right : TraceCorQHomTerm middle target) :
    (TraceCorQHomTerm.comp left right).importedRectangleCount =
      (TraceCorQTerm.comp left.raw right.raw).importedRectangleCount :=
  rfl

/-- Typed term composition exposes the raw term-composition imported rectangles. -/
theorem TraceCorQHomTerm.comp_importedRectangles
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomTerm source middle)
    (right : TraceCorQHomTerm middle target) :
    (TraceCorQHomTerm.comp left right).importedRectangles =
      (TraceCorQTerm.comp left.raw right.raw).importedRectangles :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

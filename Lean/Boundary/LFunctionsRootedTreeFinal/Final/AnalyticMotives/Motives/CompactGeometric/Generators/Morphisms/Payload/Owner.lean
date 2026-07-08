import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Morphisms.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Payload.Owner

/-!
# Endpoint payload for compact geometric generator morphisms

Compact-generator morphisms are quotient trace-correspondence homs, so this
file does not assign them a canonical representative ledger.  It records the
canonical analytic payload that is available without choosing a representative:
the imported finite-rectangle payload of their source and target generators.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Source endpoint imported rectangles of a compact-generator morphism. -/
def TraceAnalyticGeometricGenerator.Hom.sourceImportedRectangles
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  source.importedRectangles

/-- Target endpoint imported rectangles of a compact-generator morphism. -/
def TraceAnalyticGeometricGenerator.Hom.targetImportedRectangles
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  target.importedRectangles

/-- Source endpoint imported-rectangle count of a compact-generator morphism. -/
def TraceAnalyticGeometricGenerator.Hom.sourceImportedRectangleCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    Nat :=
  source.importedRectangleCount

/-- Target endpoint imported-rectangle count of a compact-generator morphism. -/
def TraceAnalyticGeometricGenerator.Hom.targetImportedRectangleCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    Nat :=
  target.importedRectangleCount

/-- Source endpoint trace-bookkeeping count of a compact-generator morphism. -/
def TraceAnalyticGeometricGenerator.Hom.sourceTraceBookkeepingCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    Nat :=
  source.traceBookkeepingCount

/-- Target endpoint trace-bookkeeping count of a compact-generator morphism. -/
def TraceAnalyticGeometricGenerator.Hom.targetTraceBookkeepingCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    Nat :=
  target.traceBookkeepingCount

/-- Source endpoint rewrite-step count of a compact-generator morphism. -/
def TraceAnalyticGeometricGenerator.Hom.sourceRewriteStepCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    Nat :=
  source.rewriteStepCount

/-- Target endpoint rewrite-step count of a compact-generator morphism. -/
def TraceAnalyticGeometricGenerator.Hom.targetRewriteStepCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    Nat :=
  target.rewriteStepCount

/-- Source endpoint count is counted by the source endpoint rectangle list. -/
theorem TraceAnalyticGeometricGenerator.Hom.sourceImportedRectangleCount_eq_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.sourceImportedRectangleCount =
      morphism.sourceImportedRectangles.length :=
  TraceAnalyticGeometricGenerator.importedRectangleCount_eq_length_importedRectangles
    source

/-- Target endpoint count is counted by the target endpoint rectangle list. -/
theorem TraceAnalyticGeometricGenerator.Hom.targetImportedRectangleCount_eq_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.targetImportedRectangleCount =
      morphism.targetImportedRectangles.length :=
  TraceAnalyticGeometricGenerator.importedRectangleCount_eq_length_importedRectangles
    target

/-- Identity morphism source endpoint rectangles are the generator imported rectangles. -/
theorem TraceAnalyticGeometricGenerator.Hom.id_sourceImportedRectangles
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceAnalyticGeometricGenerator.id generator).sourceImportedRectangles =
      generator.importedRectangles :=
  rfl

/-- Identity morphism target endpoint rectangles are the generator imported rectangles. -/
theorem TraceAnalyticGeometricGenerator.Hom.id_targetImportedRectangles
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceAnalyticGeometricGenerator.id generator).targetImportedRectangles =
      generator.importedRectangles :=
  rfl

/-- Identity morphism source endpoint count is the generator imported count. -/
theorem TraceAnalyticGeometricGenerator.Hom.id_sourceImportedRectangleCount
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceAnalyticGeometricGenerator.id generator).sourceImportedRectangleCount =
      generator.importedRectangleCount :=
  rfl

/-- Identity morphism target endpoint count is the generator imported count. -/
theorem TraceAnalyticGeometricGenerator.Hom.id_targetImportedRectangleCount
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceAnalyticGeometricGenerator.id generator).targetImportedRectangleCount =
      generator.importedRectangleCount :=
  rfl

/-- Identity morphism source endpoint bookkeeping count is the generator bookkeeping count. -/
theorem TraceAnalyticGeometricGenerator.Hom.id_sourceTraceBookkeepingCount
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceAnalyticGeometricGenerator.id generator).sourceTraceBookkeepingCount =
      generator.traceBookkeepingCount :=
  rfl

/-- Identity morphism target endpoint bookkeeping count is the generator bookkeeping count. -/
theorem TraceAnalyticGeometricGenerator.Hom.id_targetTraceBookkeepingCount
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceAnalyticGeometricGenerator.id generator).targetTraceBookkeepingCount =
      generator.traceBookkeepingCount :=
  rfl

/-- Identity morphism source endpoint rewrite count is the generator rewrite count. -/
theorem TraceAnalyticGeometricGenerator.Hom.id_sourceRewriteStepCount
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceAnalyticGeometricGenerator.id generator).sourceRewriteStepCount =
      generator.rewriteStepCount :=
  rfl

/-- Identity morphism target endpoint rewrite count is the generator rewrite count. -/
theorem TraceAnalyticGeometricGenerator.Hom.id_targetRewriteStepCount
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceAnalyticGeometricGenerator.id generator).targetRewriteStepCount =
      generator.rewriteStepCount :=
  rfl

/-- Composition keeps the left morphism source endpoint rectangles. -/
theorem TraceAnalyticGeometricGenerator.Hom.comp_sourceImportedRectangles
    {first second third : TraceAnalyticGeometricGenerator}
    (left : TraceAnalyticGeometricGenerator.Hom first second)
    (right : TraceAnalyticGeometricGenerator.Hom second third) :
    (TraceAnalyticGeometricGenerator.comp left right).sourceImportedRectangles =
      left.sourceImportedRectangles :=
  rfl

/-- Composition keeps the right morphism target endpoint rectangles. -/
theorem TraceAnalyticGeometricGenerator.Hom.comp_targetImportedRectangles
    {first second third : TraceAnalyticGeometricGenerator}
    (left : TraceAnalyticGeometricGenerator.Hom first second)
    (right : TraceAnalyticGeometricGenerator.Hom second third) :
    (TraceAnalyticGeometricGenerator.comp left right).targetImportedRectangles =
      right.targetImportedRectangles :=
  rfl

/-- Composition keeps the left morphism source endpoint count. -/
theorem TraceAnalyticGeometricGenerator.Hom.comp_sourceImportedRectangleCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : TraceAnalyticGeometricGenerator.Hom first second)
    (right : TraceAnalyticGeometricGenerator.Hom second third) :
    (TraceAnalyticGeometricGenerator.comp left right).sourceImportedRectangleCount =
      left.sourceImportedRectangleCount :=
  rfl

/-- Composition keeps the right morphism target endpoint count. -/
theorem TraceAnalyticGeometricGenerator.Hom.comp_targetImportedRectangleCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : TraceAnalyticGeometricGenerator.Hom first second)
    (right : TraceAnalyticGeometricGenerator.Hom second third) :
    (TraceAnalyticGeometricGenerator.comp left right).targetImportedRectangleCount =
      right.targetImportedRectangleCount :=
  rfl

/-- Composition keeps the left morphism source endpoint bookkeeping count. -/
theorem TraceAnalyticGeometricGenerator.Hom.comp_sourceTraceBookkeepingCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : TraceAnalyticGeometricGenerator.Hom first second)
    (right : TraceAnalyticGeometricGenerator.Hom second third) :
    (TraceAnalyticGeometricGenerator.comp left right).sourceTraceBookkeepingCount =
      left.sourceTraceBookkeepingCount :=
  rfl

/-- Composition keeps the right morphism target endpoint bookkeeping count. -/
theorem TraceAnalyticGeometricGenerator.Hom.comp_targetTraceBookkeepingCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : TraceAnalyticGeometricGenerator.Hom first second)
    (right : TraceAnalyticGeometricGenerator.Hom second third) :
    (TraceAnalyticGeometricGenerator.comp left right).targetTraceBookkeepingCount =
      right.targetTraceBookkeepingCount :=
  rfl

/-- Composition keeps the left morphism source endpoint rewrite count. -/
theorem TraceAnalyticGeometricGenerator.Hom.comp_sourceRewriteStepCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : TraceAnalyticGeometricGenerator.Hom first second)
    (right : TraceAnalyticGeometricGenerator.Hom second third) :
    (TraceAnalyticGeometricGenerator.comp left right).sourceRewriteStepCount =
      left.sourceRewriteStepCount :=
  rfl

/-- Composition keeps the right morphism target endpoint rewrite count. -/
theorem TraceAnalyticGeometricGenerator.Hom.comp_targetRewriteStepCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : TraceAnalyticGeometricGenerator.Hom first second)
    (right : TraceAnalyticGeometricGenerator.Hom second third) :
    (TraceAnalyticGeometricGenerator.comp left right).targetRewriteStepCount =
      right.targetRewriteStepCount :=
  rfl

/-- Source endpoint rectangles agree with the source localized object payload. -/
theorem TraceAnalyticGeometricGenerator.Hom.sourceImportedRectangles_eq_localizedObject
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.sourceImportedRectangles =
      source.localizedObject.importedRectangles :=
  Eq.symm
    (TraceAnalyticGeometricGenerator.localizedObject_importedRectangles
      source)

/-- Target endpoint rectangles agree with the target localized object payload. -/
theorem TraceAnalyticGeometricGenerator.Hom.targetImportedRectangles_eq_localizedObject
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.targetImportedRectangles =
      target.localizedObject.importedRectangles :=
  Eq.symm
    (TraceAnalyticGeometricGenerator.localizedObject_importedRectangles
      target)

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Morphisms.Payload.Owner

/-!
# Motive-root compact morphism payload operations

This file exposes identity and composition laws for endpoint payloads of compact
geometric generator morphisms at the motive root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Identity compact morphism source rectangles are the generator rectangles. -/
theorem TraceAnalyticMotive.compactGeneratorMorphism_id_sourceImportedRectangles
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceAnalyticGeometricGenerator.id generator).sourceImportedRectangles =
      generator.importedRectangles :=
  TraceAnalyticGeometricGenerator.Hom.id_sourceImportedRectangles
    generator

/-- Identity compact morphism target rectangles are the generator rectangles. -/
theorem TraceAnalyticMotive.compactGeneratorMorphism_id_targetImportedRectangles
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceAnalyticGeometricGenerator.id generator).targetImportedRectangles =
      generator.importedRectangles :=
  TraceAnalyticGeometricGenerator.Hom.id_targetImportedRectangles
    generator

/-- Identity compact morphism source imported-rectangle count is the generator count. -/
theorem TraceAnalyticMotive.compactGeneratorMorphism_id_sourceImportedRectangleCount
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceAnalyticGeometricGenerator.id generator).sourceImportedRectangleCount =
      generator.importedRectangleCount :=
  TraceAnalyticGeometricGenerator.Hom.id_sourceImportedRectangleCount
    generator

/-- Identity compact morphism target imported-rectangle count is the generator count. -/
theorem TraceAnalyticMotive.compactGeneratorMorphism_id_targetImportedRectangleCount
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceAnalyticGeometricGenerator.id generator).targetImportedRectangleCount =
      generator.importedRectangleCount :=
  TraceAnalyticGeometricGenerator.Hom.id_targetImportedRectangleCount
    generator

/-- Identity compact morphism source bookkeeping count is the generator count. -/
theorem TraceAnalyticMotive.compactGeneratorMorphism_id_sourceTraceBookkeepingCount
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceAnalyticGeometricGenerator.id generator).sourceTraceBookkeepingCount =
      generator.traceBookkeepingCount :=
  TraceAnalyticGeometricGenerator.Hom.id_sourceTraceBookkeepingCount
    generator

/-- Identity compact morphism target bookkeeping count is the generator count. -/
theorem TraceAnalyticMotive.compactGeneratorMorphism_id_targetTraceBookkeepingCount
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceAnalyticGeometricGenerator.id generator).targetTraceBookkeepingCount =
      generator.traceBookkeepingCount :=
  TraceAnalyticGeometricGenerator.Hom.id_targetTraceBookkeepingCount
    generator

/-- Identity compact morphism source rewrite-step count is the generator count. -/
theorem TraceAnalyticMotive.compactGeneratorMorphism_id_sourceRewriteStepCount
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceAnalyticGeometricGenerator.id generator).sourceRewriteStepCount =
      generator.rewriteStepCount :=
  TraceAnalyticGeometricGenerator.Hom.id_sourceRewriteStepCount
    generator

/-- Identity compact morphism target rewrite-step count is the generator count. -/
theorem TraceAnalyticMotive.compactGeneratorMorphism_id_targetRewriteStepCount
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceAnalyticGeometricGenerator.id generator).targetRewriteStepCount =
      generator.rewriteStepCount :=
  TraceAnalyticGeometricGenerator.Hom.id_targetRewriteStepCount
    generator

/-- Composition keeps the left compact morphism source rectangles. -/
theorem TraceAnalyticMotive.compactGeneratorMorphism_comp_sourceImportedRectangles
    {first second third : TraceAnalyticGeometricGenerator}
    (left : TraceAnalyticGeometricGenerator.Hom first second)
    (right : TraceAnalyticGeometricGenerator.Hom second third) :
    (TraceAnalyticGeometricGenerator.comp left right).sourceImportedRectangles =
      left.sourceImportedRectangles :=
  TraceAnalyticGeometricGenerator.Hom.comp_sourceImportedRectangles
    left
    right

/-- Composition keeps the right compact morphism target rectangles. -/
theorem TraceAnalyticMotive.compactGeneratorMorphism_comp_targetImportedRectangles
    {first second third : TraceAnalyticGeometricGenerator}
    (left : TraceAnalyticGeometricGenerator.Hom first second)
    (right : TraceAnalyticGeometricGenerator.Hom second third) :
    (TraceAnalyticGeometricGenerator.comp left right).targetImportedRectangles =
      right.targetImportedRectangles :=
  TraceAnalyticGeometricGenerator.Hom.comp_targetImportedRectangles
    left
    right

/-- Composition keeps the left compact morphism source imported-rectangle count. -/
theorem TraceAnalyticMotive.compactGeneratorMorphism_comp_sourceImportedRectangleCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : TraceAnalyticGeometricGenerator.Hom first second)
    (right : TraceAnalyticGeometricGenerator.Hom second third) :
    (TraceAnalyticGeometricGenerator.comp left right).sourceImportedRectangleCount =
      left.sourceImportedRectangleCount :=
  TraceAnalyticGeometricGenerator.Hom.comp_sourceImportedRectangleCount
    left
    right

/-- Composition keeps the right compact morphism target imported-rectangle count. -/
theorem TraceAnalyticMotive.compactGeneratorMorphism_comp_targetImportedRectangleCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : TraceAnalyticGeometricGenerator.Hom first second)
    (right : TraceAnalyticGeometricGenerator.Hom second third) :
    (TraceAnalyticGeometricGenerator.comp left right).targetImportedRectangleCount =
      right.targetImportedRectangleCount :=
  TraceAnalyticGeometricGenerator.Hom.comp_targetImportedRectangleCount
    left
    right

/-- Composition keeps the left compact morphism source bookkeeping count. -/
theorem TraceAnalyticMotive.compactGeneratorMorphism_comp_sourceTraceBookkeepingCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : TraceAnalyticGeometricGenerator.Hom first second)
    (right : TraceAnalyticGeometricGenerator.Hom second third) :
    (TraceAnalyticGeometricGenerator.comp left right).sourceTraceBookkeepingCount =
      left.sourceTraceBookkeepingCount :=
  TraceAnalyticGeometricGenerator.Hom.comp_sourceTraceBookkeepingCount
    left
    right

/-- Composition keeps the right compact morphism target bookkeeping count. -/
theorem TraceAnalyticMotive.compactGeneratorMorphism_comp_targetTraceBookkeepingCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : TraceAnalyticGeometricGenerator.Hom first second)
    (right : TraceAnalyticGeometricGenerator.Hom second third) :
    (TraceAnalyticGeometricGenerator.comp left right).targetTraceBookkeepingCount =
      right.targetTraceBookkeepingCount :=
  TraceAnalyticGeometricGenerator.Hom.comp_targetTraceBookkeepingCount
    left
    right

/-- Composition keeps the left compact morphism source rewrite-step count. -/
theorem TraceAnalyticMotive.compactGeneratorMorphism_comp_sourceRewriteStepCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : TraceAnalyticGeometricGenerator.Hom first second)
    (right : TraceAnalyticGeometricGenerator.Hom second third) :
    (TraceAnalyticGeometricGenerator.comp left right).sourceRewriteStepCount =
      left.sourceRewriteStepCount :=
  TraceAnalyticGeometricGenerator.Hom.comp_sourceRewriteStepCount
    left
    right

/-- Composition keeps the right compact morphism target rewrite-step count. -/
theorem TraceAnalyticMotive.compactGeneratorMorphism_comp_targetRewriteStepCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : TraceAnalyticGeometricGenerator.Hom first second)
    (right : TraceAnalyticGeometricGenerator.Hom second third) :
    (TraceAnalyticGeometricGenerator.comp left right).targetRewriteStepCount =
      right.targetRewriteStepCount :=
  TraceAnalyticGeometricGenerator.Hom.comp_targetRewriteStepCount
    left
    right

end AnalyticMotives
end LFunctions
end Boundary

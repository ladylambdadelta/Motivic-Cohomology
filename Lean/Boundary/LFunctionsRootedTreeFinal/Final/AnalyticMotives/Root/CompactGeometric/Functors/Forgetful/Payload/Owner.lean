import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Functors.Forgetful.Payload.Owner

/-!
# Top-root compact forgetful payloads

This file exposes payload preservation for the compact-generator forgetful
functor at the public analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The forgotten object has the generator imported rectangles. -/
theorem AnalyticMotivesRoot.compactGenerator_forgetfulFunctor_obj_importedRectangles
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
      generator).importedRectangles =
      generator.importedRectangles :=
  TraceAnalyticMotive.compactGenerator_forgetfulFunctor_obj_importedRectangles
    generator

/-- The forgotten object has the generator imported-rectangle count. -/
theorem AnalyticMotivesRoot.compactGenerator_forgetfulFunctor_obj_importedRectangleCount
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
      generator).importedRectangleCount =
      generator.importedRectangleCount :=
  TraceAnalyticMotive.compactGenerator_forgetfulFunctor_obj_importedRectangleCount
    generator

/-- The forgotten object has the generator bookkeeping count. -/
theorem AnalyticMotivesRoot.compactGenerator_forgetfulFunctor_obj_traceBookkeepingCount
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
      generator).traceBookkeepingCount =
      generator.traceBookkeepingCount :=
  TraceAnalyticMotive.compactGenerator_forgetfulFunctor_obj_traceBookkeepingCount
    generator

/-- The forgotten object has the generator rewrite-step count. -/
theorem AnalyticMotivesRoot.compactGenerator_forgetfulFunctor_obj_rewriteStepCount
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
      generator).rewriteStepCount =
      generator.rewriteStepCount :=
  TraceAnalyticMotive.compactGenerator_forgetfulFunctor_obj_rewriteStepCount
    generator

/-- The forgotten object imported count is counted by its rectangle list. -/
theorem AnalyticMotivesRoot.compactGenerator_forgetfulFunctor_obj_importedRectangleCount_eq_length
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
      generator).importedRectangleCount =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        generator).importedRectangles.length :=
  TraceAnalyticMotive.compactGenerator_forgetfulFunctor_obj_importedRectangleCount_eq_length
    generator

/-- A compact morphism source rectangle payload agrees with the forgotten source. -/
theorem AnalyticMotivesRoot.compactGeneratorMorphism_sourceImportedRectangles_eq_forgetful_source
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.sourceImportedRectangles =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        source).importedRectangles :=
  TraceAnalyticMotive.compactGeneratorMorphism_sourceImportedRectangles_eq_forgetful_source
    morphism

/-- A compact morphism target rectangle payload agrees with the forgotten target. -/
theorem AnalyticMotivesRoot.compactGeneratorMorphism_targetImportedRectangles_eq_forgetful_target
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.targetImportedRectangles =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        target).importedRectangles :=
  TraceAnalyticMotive.compactGeneratorMorphism_targetImportedRectangles_eq_forgetful_target
    morphism

/-- A compact morphism source imported count agrees with the forgotten source. -/
theorem AnalyticMotivesRoot.compactGeneratorMorphism_sourceImportedRectangleCount_eq_forgetful_source
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.sourceImportedRectangleCount =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        source).importedRectangleCount :=
  TraceAnalyticMotive.compactGeneratorMorphism_sourceImportedRectangleCount_eq_forgetful_source
    morphism

/-- A compact morphism target imported count agrees with the forgotten target. -/
theorem AnalyticMotivesRoot.compactGeneratorMorphism_targetImportedRectangleCount_eq_forgetful_target
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.targetImportedRectangleCount =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        target).importedRectangleCount :=
  TraceAnalyticMotive.compactGeneratorMorphism_targetImportedRectangleCount_eq_forgetful_target
    morphism

/-- A compact morphism source bookkeeping count agrees with the forgotten source. -/
theorem AnalyticMotivesRoot.compactGeneratorMorphism_sourceTraceBookkeepingCount_eq_forgetful_source
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.sourceTraceBookkeepingCount =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        source).traceBookkeepingCount :=
  TraceAnalyticMotive.compactGeneratorMorphism_sourceTraceBookkeepingCount_eq_forgetful_source
    morphism

/-- A compact morphism target bookkeeping count agrees with the forgotten target. -/
theorem AnalyticMotivesRoot.compactGeneratorMorphism_targetTraceBookkeepingCount_eq_forgetful_target
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.targetTraceBookkeepingCount =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        target).traceBookkeepingCount :=
  TraceAnalyticMotive.compactGeneratorMorphism_targetTraceBookkeepingCount_eq_forgetful_target
    morphism

/-- A compact morphism source rewrite count agrees with the forgotten source. -/
theorem AnalyticMotivesRoot.compactGeneratorMorphism_sourceRewriteStepCount_eq_forgetful_source
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.sourceRewriteStepCount =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        source).rewriteStepCount :=
  TraceAnalyticMotive.compactGeneratorMorphism_sourceRewriteStepCount_eq_forgetful_source
    morphism

/-- A compact morphism target rewrite count agrees with the forgotten target. -/
theorem AnalyticMotivesRoot.compactGeneratorMorphism_targetRewriteStepCount_eq_forgetful_target
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.targetRewriteStepCount =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        target).rewriteStepCount :=
  TraceAnalyticMotive.compactGeneratorMorphism_targetRewriteStepCount_eq_forgetful_target
    morphism

end AnalyticMotives
end LFunctions
end Boundary

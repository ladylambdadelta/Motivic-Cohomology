import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Forgetful.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Morphisms.Payload.Owner

/-!
# Payload preservation for the compact-generator forgetful functor

This file records that the forgetful functor from compact geometric generators
to trace correspondences preserves the imported finite-rectangle endpoint
payload by definition.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The forgetful functor object has the generator imported rectangles. -/
theorem TraceAnalyticGeometricGenerator.forgetfulFunctor_obj_importedRectangles
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
      generator).importedRectangles =
      generator.importedRectangles :=
  rfl

/-- The forgetful functor object has the generator imported count. -/
theorem TraceAnalyticGeometricGenerator.forgetfulFunctor_obj_importedRectangleCount
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
      generator).importedRectangleCount =
      generator.importedRectangleCount :=
  rfl

/-- The forgetful functor object has the generator bookkeeping count. -/
theorem TraceAnalyticGeometricGenerator.forgetfulFunctor_obj_traceBookkeepingCount
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
      generator).traceBookkeepingCount =
      generator.traceBookkeepingCount :=
  rfl

/-- The forgetful functor object has the generator rewrite-step count. -/
theorem TraceAnalyticGeometricGenerator.forgetfulFunctor_obj_rewriteStepCount
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
      generator).rewriteStepCount =
      generator.rewriteStepCount :=
  rfl

/-- The forgetful functor object imported count is counted by its rectangle list. -/
theorem TraceAnalyticGeometricGenerator.forgetfulFunctor_obj_importedRectangleCount_eq_length
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
      generator).importedRectangleCount =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        generator).importedRectangles.length :=
  TraceCorQObject.importedRectangleCount_eq_length_importedRectangles
    (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj generator)

/-- A compact morphism source payload agrees with the forgotten source trace object. -/
theorem TraceAnalyticGeometricGenerator.Hom.sourceImportedRectangles_eq_forgetful_source
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.sourceImportedRectangles =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        source).importedRectangles :=
  rfl

/-- A compact morphism target payload agrees with the forgotten target trace object. -/
theorem TraceAnalyticGeometricGenerator.Hom.targetImportedRectangles_eq_forgetful_target
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.targetImportedRectangles =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        target).importedRectangles :=
  rfl

/-- A compact morphism source payload count agrees with the forgotten source trace object. -/
theorem TraceAnalyticGeometricGenerator.Hom.sourceImportedRectangleCount_eq_forgetful_source
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.sourceImportedRectangleCount =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        source).importedRectangleCount :=
  rfl

/-- A compact morphism target payload count agrees with the forgotten target trace object. -/
theorem TraceAnalyticGeometricGenerator.Hom.targetImportedRectangleCount_eq_forgetful_target
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.targetImportedRectangleCount =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        target).importedRectangleCount :=
  rfl

/-- A compact morphism source bookkeeping count agrees with the forgotten source trace object. -/
theorem TraceAnalyticGeometricGenerator.Hom.sourceTraceBookkeepingCount_eq_forgetful_source
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.sourceTraceBookkeepingCount =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        source).traceBookkeepingCount :=
  rfl

/-- A compact morphism target bookkeeping count agrees with the forgotten target trace object. -/
theorem TraceAnalyticGeometricGenerator.Hom.targetTraceBookkeepingCount_eq_forgetful_target
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.targetTraceBookkeepingCount =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        target).traceBookkeepingCount :=
  rfl

/-- A compact morphism source rewrite count agrees with the forgotten source trace object. -/
theorem TraceAnalyticGeometricGenerator.Hom.sourceRewriteStepCount_eq_forgetful_source
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.sourceRewriteStepCount =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        source).rewriteStepCount :=
  rfl

/-- A compact morphism target rewrite count agrees with the forgotten target trace object. -/
theorem TraceAnalyticGeometricGenerator.Hom.targetRewriteStepCount_eq_forgetful_target
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.targetRewriteStepCount =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        target).rewriteStepCount :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

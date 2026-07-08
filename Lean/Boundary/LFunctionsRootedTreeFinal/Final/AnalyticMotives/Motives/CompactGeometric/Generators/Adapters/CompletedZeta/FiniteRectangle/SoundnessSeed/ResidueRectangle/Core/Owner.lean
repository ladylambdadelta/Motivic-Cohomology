import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Morphisms.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Forgetful.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleRectanglePipeline.Owner

/-!
# Core compact generator data for the zero-pole residue rectangle seed

This file owns the source and target compact generators, their representing
trace morphism, and the basic object-level projection facts.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The compact source generator of the rectangle-certified zero-pole residue seed. -/
def completedZetaZeroPoleResidueRectangleSourceGenerator
    (R : ℝ) :
    TraceAnalyticGeometricGenerator :=
  TraceAnalyticGeometricGenerator.ofTraceObject
    (completedZetaZeroPoleResidueRectanglePipeline_source R)

/-- The compact target generator of the rectangle-certified zero-pole residue seed. -/
def completedZetaZeroPoleResidueRectangleTargetGenerator :
    TraceAnalyticGeometricGenerator :=
  TraceAnalyticGeometricGenerator.ofTraceObject
    completedZetaZeroPoleResidueRectanglePipeline_target

/-- The compact-generator morphism represented by the rectangle-certified residue hom. -/
def completedZetaZeroPoleResidueRectangleGeneratorHom
    (R : ℝ) :
    TraceAnalyticGeometricGenerator.Hom
      (completedZetaZeroPoleResidueRectangleSourceGenerator R)
      completedZetaZeroPoleResidueRectangleTargetGenerator :=
  completedZetaZeroPoleResidueRectanglePipeline_hom R

/-- The residue rectangle source generator has the pipeline source trace object. -/
theorem completedZetaZeroPoleResidueRectangleSourceGenerator_traceObject
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleSourceGenerator R).traceObject =
      completedZetaZeroPoleResidueRectanglePipeline_source R :=
  rfl

/-- The residue rectangle target generator has the pipeline target trace object. -/
theorem completedZetaZeroPoleResidueRectangleTargetGenerator_traceObject :
    completedZetaZeroPoleResidueRectangleTargetGenerator.traceObject =
      completedZetaZeroPoleResidueRectanglePipeline_target :=
  rfl

/-- Forgetting the residue rectangle source generator gives the pipeline source trace object. -/
theorem completedZetaZeroPoleResidueRectangleSourceGenerator_forgetfulFunctor_obj
    (R : ℝ) :
    TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        (completedZetaZeroPoleResidueRectangleSourceGenerator R) =
      completedZetaZeroPoleResidueRectanglePipeline_source R :=
  rfl

/-- Forgetting the residue rectangle target generator gives the pipeline target trace object. -/
theorem completedZetaZeroPoleResidueRectangleTargetGenerator_forgetfulFunctor_obj :
    TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        completedZetaZeroPoleResidueRectangleTargetGenerator =
      completedZetaZeroPoleResidueRectanglePipeline_target :=
  rfl

/-- The residue rectangle source generator presheaf is the pipeline source representable. -/
theorem completedZetaZeroPoleResidueRectangleSourceGenerator_presheaf
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleSourceGenerator R).presheaf =
      TraceCorQPresheaf.representable
        (completedZetaZeroPoleResidueRectanglePipeline_source R) :=
  rfl

/-- The residue rectangle target generator presheaf is the pipeline target representable. -/
theorem completedZetaZeroPoleResidueRectangleTargetGenerator_presheaf :
    completedZetaZeroPoleResidueRectangleTargetGenerator.presheaf =
      TraceCorQPresheaf.representable
        completedZetaZeroPoleResidueRectanglePipeline_target :=
  rfl

/-- The residue rectangle source generator has the lifted pipeline source representable object. -/
theorem completedZetaZeroPoleResidueRectangleSourceGenerator_representableObject
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleSourceGenerator R).representableObject =
      (TraceCorQRepresentablePresheaf.yoneda).obj
        (completedZetaZeroPoleResidueRectanglePipeline_source R) :=
  rfl

/-- The residue rectangle target generator has the lifted pipeline target representable object. -/
theorem completedZetaZeroPoleResidueRectangleTargetGenerator_representableObject :
    completedZetaZeroPoleResidueRectangleTargetGenerator.representableObject =
      (TraceCorQRepresentablePresheaf.yoneda).obj
        completedZetaZeroPoleResidueRectanglePipeline_target :=
  rfl

/-- The residue rectangle source generator has the pipeline source localized word object. -/
theorem completedZetaZeroPoleResidueRectangleSourceGenerator_localizedWordObject
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleSourceGenerator R).localizedWordObject =
      TraceLocalizedWordObject.ofTraceObject
        (completedZetaZeroPoleResidueRectanglePipeline_source R) :=
  rfl

/-- The residue rectangle target generator has the pipeline target localized word object. -/
theorem completedZetaZeroPoleResidueRectangleTargetGenerator_localizedWordObject :
    completedZetaZeroPoleResidueRectangleTargetGenerator.localizedWordObject =
      TraceLocalizedWordObject.ofTraceObject
        completedZetaZeroPoleResidueRectanglePipeline_target :=
  rfl

/-- The residue rectangle source localized object has the source generator rectangles. -/
theorem completedZetaZeroPoleResidueRectangleSourceGenerator_localizedObject_importedRectangles
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleSourceGenerator R).localizedObject.importedRectangles =
      (completedZetaZeroPoleResidueRectangleSourceGenerator R).importedRectangles :=
  TraceAnalyticGeometricGenerator.localizedObject_importedRectangles
    (completedZetaZeroPoleResidueRectangleSourceGenerator R)

/-- The residue rectangle source localized object has the source generator rectangle count. -/
theorem completedZetaZeroPoleResidueRectangleSourceGenerator_localizedObject_importedRectangleCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleSourceGenerator R).localizedObject.importedRectangleCount =
      (completedZetaZeroPoleResidueRectangleSourceGenerator R).importedRectangleCount :=
  TraceAnalyticGeometricGenerator.localizedObject_importedRectangleCount
    (completedZetaZeroPoleResidueRectangleSourceGenerator R)

/-- The residue rectangle source localized object rectangle count is counted by its rectangles. -/
theorem completedZetaZeroPoleResidueRectangleSourceGenerator_localizedObject_importedRectangleCount_eq_length
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleSourceGenerator R).localizedObject.importedRectangleCount =
      (completedZetaZeroPoleResidueRectangleSourceGenerator R).localizedObject.importedRectangles.length :=
  TraceAnalyticGeometricGenerator.localizedObject_importedRectangleCount_eq_length
    (completedZetaZeroPoleResidueRectangleSourceGenerator R)

/-- The residue rectangle target localized object has the target generator rectangles. -/
theorem completedZetaZeroPoleResidueRectangleTargetGenerator_localizedObject_importedRectangles :
    completedZetaZeroPoleResidueRectangleTargetGenerator.localizedObject.importedRectangles =
      completedZetaZeroPoleResidueRectangleTargetGenerator.importedRectangles :=
  TraceAnalyticGeometricGenerator.localizedObject_importedRectangles
    completedZetaZeroPoleResidueRectangleTargetGenerator

/-- The residue rectangle target localized object has the target generator rectangle count. -/
theorem completedZetaZeroPoleResidueRectangleTargetGenerator_localizedObject_importedRectangleCount :
    completedZetaZeroPoleResidueRectangleTargetGenerator.localizedObject.importedRectangleCount =
      completedZetaZeroPoleResidueRectangleTargetGenerator.importedRectangleCount :=
  TraceAnalyticGeometricGenerator.localizedObject_importedRectangleCount
    completedZetaZeroPoleResidueRectangleTargetGenerator

/-- The residue rectangle target localized object rectangle count is counted by its rectangles. -/
theorem completedZetaZeroPoleResidueRectangleTargetGenerator_localizedObject_importedRectangleCount_eq_length :
    completedZetaZeroPoleResidueRectangleTargetGenerator.localizedObject.importedRectangleCount =
      completedZetaZeroPoleResidueRectangleTargetGenerator.localizedObject.importedRectangles.length :=
  TraceAnalyticGeometricGenerator.localizedObject_importedRectangleCount_eq_length
    completedZetaZeroPoleResidueRectangleTargetGenerator

/-- Evaluation at the residue rectangle source generator is evaluation at the pipeline source. -/
theorem completedZetaZeroPoleResidueRectangleSourceGenerator_evaluation
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleSourceGenerator R).evaluation =
      TraceCorQPresheaf.evaluation
        (completedZetaZeroPoleResidueRectanglePipeline_source R) :=
  rfl

/-- Evaluation at the residue rectangle target generator is evaluation at the pipeline target. -/
theorem completedZetaZeroPoleResidueRectangleTargetGenerator_evaluation :
    completedZetaZeroPoleResidueRectangleTargetGenerator.evaluation =
      TraceCorQPresheaf.evaluation
        completedZetaZeroPoleResidueRectanglePipeline_target :=
  rfl

/-- Source sections of the target representable are trace homs from source to target. -/
theorem completedZetaZeroPoleResidueRectangleSourceSections_targetPresheaf
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleSourceGenerator R).sections
        completedZetaZeroPoleResidueRectangleTargetGenerator.presheaf =
      ModuleCat.of Rat
        ((completedZetaZeroPoleResidueRectanglePipeline_source R) ⟶
          completedZetaZeroPoleResidueRectanglePipeline_target) :=
  TraceAnalyticGeometricGenerator.representable_sections
    (completedZetaZeroPoleResidueRectangleSourceGenerator R)
    completedZetaZeroPoleResidueRectangleTargetGenerator

/-- Target sections of the source representable are trace homs from target to source. -/
theorem completedZetaZeroPoleResidueRectangleTargetSections_sourcePresheaf
    (R : ℝ) :
    completedZetaZeroPoleResidueRectangleTargetGenerator.sections
        (completedZetaZeroPoleResidueRectangleSourceGenerator R).presheaf =
      ModuleCat.of Rat
        (completedZetaZeroPoleResidueRectanglePipeline_target ⟶
          (completedZetaZeroPoleResidueRectanglePipeline_source R)) :=
  TraceAnalyticGeometricGenerator.representable_sections
    completedZetaZeroPoleResidueRectangleTargetGenerator
    (completedZetaZeroPoleResidueRectangleSourceGenerator R)

/-- The compact-generator morphism is the pipeline typed hom. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHom_traceHom
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).traceHom =
      completedZetaZeroPoleResidueRectanglePipeline_hom R :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

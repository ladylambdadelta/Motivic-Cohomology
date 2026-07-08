import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Morphisms.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Forgetful.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleChannelRectanglePipeline.Quotient.Owner

/-!
# Core compact generator data for the zero-pole scheduled-channel rectangle seed

This file owns the source and target compact generators, their representing
trace morphism, and the basic object-level projection facts.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The compact source generator of the scheduled-channel rectangle seed. -/
def completedZetaZeroPoleChannelRectangleSourceGenerator
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceAnalyticGeometricGenerator :=
  TraceAnalyticGeometricGenerator.ofTraceObject
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u)

/-- The compact target generator of the scheduled-channel rectangle seed. -/
def completedZetaZeroPoleChannelRectangleTargetGenerator :
    TraceAnalyticGeometricGenerator :=
  TraceAnalyticGeometricGenerator.ofTraceObject
    completedZetaZeroPoleChannelScheduledRectanglePipeline_target

/-- The compact-generator morphism represented by the scheduled-channel rectangle hom. -/
def completedZetaZeroPoleChannelRectangleGeneratorHom
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceAnalyticGeometricGenerator.Hom
      (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u)
      completedZetaZeroPoleChannelRectangleTargetGenerator :=
  completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u

/-- The scheduled-channel source generator has the pipeline source trace object. -/
theorem completedZetaZeroPoleChannelRectangleSourceGenerator_traceObject
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u).traceObject =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u :=
  rfl

/-- The scheduled-channel target generator has the pipeline target trace object. -/
theorem completedZetaZeroPoleChannelRectangleTargetGenerator_traceObject :
    completedZetaZeroPoleChannelRectangleTargetGenerator.traceObject =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target :=
  rfl

/-- Forgetting the scheduled-channel source generator gives the pipeline source trace object. -/
theorem completedZetaZeroPoleChannelRectangleSourceGenerator_forgetfulFunctor_obj
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u) =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u :=
  rfl

/-- Forgetting the scheduled-channel target generator gives the pipeline target trace object. -/
theorem completedZetaZeroPoleChannelRectangleTargetGenerator_forgetfulFunctor_obj :
    TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        completedZetaZeroPoleChannelRectangleTargetGenerator =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target :=
  rfl

/-- The scheduled-channel source generator presheaf is the pipeline source representable. -/
theorem completedZetaZeroPoleChannelRectangleSourceGenerator_presheaf
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u).presheaf =
      TraceCorQPresheaf.representable
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u) :=
  rfl

/-- The scheduled-channel target generator presheaf is the pipeline target representable. -/
theorem completedZetaZeroPoleChannelRectangleTargetGenerator_presheaf :
    completedZetaZeroPoleChannelRectangleTargetGenerator.presheaf =
      TraceCorQPresheaf.representable
        completedZetaZeroPoleChannelScheduledRectanglePipeline_target :=
  rfl

/-- The scheduled-channel source generator has the lifted pipeline source representable object. -/
theorem completedZetaZeroPoleChannelRectangleSourceGenerator_representableObject
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u).representableObject =
      (TraceCorQRepresentablePresheaf.yoneda).obj
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u) :=
  rfl

/-- The scheduled-channel target generator has the lifted pipeline target representable object. -/
theorem completedZetaZeroPoleChannelRectangleTargetGenerator_representableObject :
    completedZetaZeroPoleChannelRectangleTargetGenerator.representableObject =
      (TraceCorQRepresentablePresheaf.yoneda).obj
        completedZetaZeroPoleChannelScheduledRectanglePipeline_target :=
  rfl

/-- The scheduled-channel source generator has the pipeline source localized word object. -/
theorem completedZetaZeroPoleChannelRectangleSourceGenerator_localizedWordObject
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u).localizedWordObject =
      TraceLocalizedWordObject.ofTraceObject
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u) :=
  rfl

/-- The scheduled-channel target generator has the pipeline target localized word object. -/
theorem completedZetaZeroPoleChannelRectangleTargetGenerator_localizedWordObject :
    completedZetaZeroPoleChannelRectangleTargetGenerator.localizedWordObject =
      TraceLocalizedWordObject.ofTraceObject
        completedZetaZeroPoleChannelScheduledRectanglePipeline_target :=
  rfl

/-- The scheduled-channel source localized object has the source generator rectangles. -/
theorem completedZetaZeroPoleChannelRectangleSourceGenerator_localizedObject_importedRectangles
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleSourceGenerator
      f F h u).localizedObject.importedRectangles =
      (completedZetaZeroPoleChannelRectangleSourceGenerator
        f F h u).importedRectangles :=
  TraceAnalyticGeometricGenerator.localizedObject_importedRectangles
    (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u)

/-- The scheduled-channel source localized object has the source generator rectangle count. -/
theorem completedZetaZeroPoleChannelRectangleSourceGenerator_localizedObject_importedRectangleCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleSourceGenerator
      f F h u).localizedObject.importedRectangleCount =
      (completedZetaZeroPoleChannelRectangleSourceGenerator
        f F h u).importedRectangleCount :=
  TraceAnalyticGeometricGenerator.localizedObject_importedRectangleCount
    (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u)

/-- The scheduled-channel source localized object rectangle count is counted by its rectangles. -/
theorem completedZetaZeroPoleChannelRectangleSourceGenerator_localizedObject_importedRectangleCount_eq_length
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleSourceGenerator
      f F h u).localizedObject.importedRectangleCount =
      (completedZetaZeroPoleChannelRectangleSourceGenerator
        f F h u).localizedObject.importedRectangles.length :=
  TraceAnalyticGeometricGenerator.localizedObject_importedRectangleCount_eq_length
    (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u)

/-- The scheduled-channel target localized object has the target generator rectangles. -/
theorem completedZetaZeroPoleChannelRectangleTargetGenerator_localizedObject_importedRectangles :
    completedZetaZeroPoleChannelRectangleTargetGenerator.localizedObject.importedRectangles =
      completedZetaZeroPoleChannelRectangleTargetGenerator.importedRectangles :=
  TraceAnalyticGeometricGenerator.localizedObject_importedRectangles
    completedZetaZeroPoleChannelRectangleTargetGenerator

/-- The scheduled-channel target localized object has the target generator rectangle count. -/
theorem completedZetaZeroPoleChannelRectangleTargetGenerator_localizedObject_importedRectangleCount :
    completedZetaZeroPoleChannelRectangleTargetGenerator.localizedObject.importedRectangleCount =
      completedZetaZeroPoleChannelRectangleTargetGenerator.importedRectangleCount :=
  TraceAnalyticGeometricGenerator.localizedObject_importedRectangleCount
    completedZetaZeroPoleChannelRectangleTargetGenerator

/-- The scheduled-channel target localized object rectangle count is counted by its rectangles. -/
theorem completedZetaZeroPoleChannelRectangleTargetGenerator_localizedObject_importedRectangleCount_eq_length :
    completedZetaZeroPoleChannelRectangleTargetGenerator.localizedObject.importedRectangleCount =
      completedZetaZeroPoleChannelRectangleTargetGenerator.localizedObject.importedRectangles.length :=
  TraceAnalyticGeometricGenerator.localizedObject_importedRectangleCount_eq_length
    completedZetaZeroPoleChannelRectangleTargetGenerator

/-- Evaluation at the scheduled-channel source generator is evaluation at the pipeline source. -/
theorem completedZetaZeroPoleChannelRectangleSourceGenerator_evaluation
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u).evaluation =
      TraceCorQPresheaf.evaluation
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u) :=
  rfl

/-- Evaluation at the scheduled-channel target generator is evaluation at the pipeline target. -/
theorem completedZetaZeroPoleChannelRectangleTargetGenerator_evaluation :
    completedZetaZeroPoleChannelRectangleTargetGenerator.evaluation =
      TraceCorQPresheaf.evaluation
        completedZetaZeroPoleChannelScheduledRectanglePipeline_target :=
  rfl

/-- Source sections of the target representable are trace homs from source to target. -/
theorem completedZetaZeroPoleChannelRectangleSourceSections_targetPresheaf
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u).sections
        completedZetaZeroPoleChannelRectangleTargetGenerator.presheaf =
      ModuleCat.of Rat
        ((completedZetaZeroPoleChannelScheduledRectanglePipeline_source
          f F h u) ⟶
          completedZetaZeroPoleChannelScheduledRectanglePipeline_target) :=
  TraceAnalyticGeometricGenerator.representable_sections
    (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u)
    completedZetaZeroPoleChannelRectangleTargetGenerator

/-- Target sections of the source representable are trace homs from target to source. -/
theorem completedZetaZeroPoleChannelRectangleTargetSections_sourcePresheaf
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleChannelRectangleTargetGenerator.sections
        (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u).presheaf =
      ModuleCat.of Rat
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_target ⟶
          (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u)) :=
  TraceAnalyticGeometricGenerator.representable_sections
    completedZetaZeroPoleChannelRectangleTargetGenerator
    (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u)

/-- The compact-generator morphism is the scheduled-channel pipeline typed hom. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHom_traceHom
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).traceHom =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

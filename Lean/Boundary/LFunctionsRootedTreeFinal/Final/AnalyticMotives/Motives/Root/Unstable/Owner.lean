import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Presheaves.Linear.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.CategoryLaws.Owner

/-!
# Root unstable analytic-motive wrappers

This file owns the root-level wrappers exposing representable trace presheaves
and the current unstable analytic-motive envelope.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Analytic motives currently start from Q-module-valued presheaves on `TraceCorQ`. -/
theorem TraceAnalyticMotive.representable_sections
    (source target : TraceCorQObject) :
    (TraceCorQPresheaf.representable target).sections source =
      ModuleCat.of Rat (source ⟶ target) :=
  TraceCorQPresheaf.representable_sections
    source
    target

/-- The motive root exposes the lifted representable trace-presheaf object. -/
def TraceAnalyticMotive.representableObject
    (object : TraceCorQObject) :
    TraceCorQRepresentablePresheaf :=
  (TraceCorQRepresentablePresheaf.yoneda).obj object

/-- The lifted representable object has the expected ambient presheaf. -/
theorem TraceAnalyticMotive.representableObject_presheaf
    (object : TraceCorQObject) :
    (TraceAnalyticMotive.representableObject object).presheaf =
      TraceCorQPresheaf.representable object :=
  TraceCorQRepresentablePresheaf.yoneda_obj_presheaf
    object

/-- Inclusion after lifted Yoneda is the ambient Q-linear Yoneda functor. -/
theorem TraceAnalyticMotive.representableYoneda_comp_inclusion :
    TraceCorQRepresentablePresheaf.yoneda ⋙
        TraceCorQRepresentablePresheaf.inclusion =
      TraceCorQPresheaf.yoneda :=
  TraceCorQRepresentablePresheaf.yoneda_comp_inclusion

/-- The motive root exposes the lifted-Yoneda trace preimage. -/
noncomputable def TraceAnalyticMotive.representableYonedaPreimage
    {source target : TraceCorQObject}
    (morphism :
      TraceAnalyticMotive.representableObject source ⟶
        TraceAnalyticMotive.representableObject target) :
    source ⟶ target :=
  TraceCorQRepresentablePresheaf.yonedaPreimage
    morphism

/-- Lifted-Yoneda preimage recovers the trace correspondence from a lifted-Yoneda map. -/
theorem TraceAnalyticMotive.representableYonedaPreimage_yonedaMap
    {source target : TraceCorQObject}
    (morphism : source ⟶ target) :
    TraceAnalyticMotive.representableYonedaPreimage
        ((TraceCorQRepresentablePresheaf.yoneda).map morphism) =
      morphism :=
  TraceCorQRepresentablePresheaf.yonedaPreimage_yonedaMap
    morphism

/-- Every lifted-Yoneda morphism is recovered from its motive-root trace preimage. -/
theorem TraceAnalyticMotive.yonedaMap_representableYonedaPreimage
    {source target : TraceCorQObject}
    (morphism :
      TraceAnalyticMotive.representableObject source ⟶
        TraceAnalyticMotive.representableObject target) :
    (TraceCorQRepresentablePresheaf.yoneda).map
        (TraceAnalyticMotive.representableYonedaPreimage morphism) =
      morphism :=
  TraceCorQRepresentablePresheaf.yonedaMap_yonedaPreimage
    morphism

/-- Motive-root lifted-Yoneda preimage sends identity to identity. -/
theorem TraceAnalyticMotive.representableYonedaPreimage_id
    (object : TraceCorQObject) :
    TraceAnalyticMotive.representableYonedaPreimage
        (𝟙 (TraceAnalyticMotive.representableObject object)) =
      𝟙 object :=
  TraceCorQRepresentablePresheaf.yonedaPreimage_id
    object

/-- Motive-root lifted-Yoneda preimage sends composition to trace composition. -/
theorem TraceAnalyticMotive.representableYonedaPreimage_comp
    {first second third : TraceCorQObject}
    (left :
      TraceAnalyticMotive.representableObject first ⟶
        TraceAnalyticMotive.representableObject second)
    (right :
      TraceAnalyticMotive.representableObject second ⟶
        TraceAnalyticMotive.representableObject third) :
    TraceAnalyticMotive.representableYonedaPreimage (left ≫ right) =
      TraceAnalyticMotive.representableYonedaPreimage left ≫
        TraceAnalyticMotive.representableYonedaPreimage right :=
  TraceCorQRepresentablePresheaf.yonedaPreimage_comp
    left
    right

/-- Inclusion of lifted representables preserves addition of morphisms. -/
theorem TraceAnalyticMotive.representableInclusion_map_add
    {source target : TraceCorQRepresentablePresheaf}
    (left right : source ⟶ target) :
    TraceCorQRepresentablePresheaf.inclusion.map (left + right) =
      TraceCorQRepresentablePresheaf.inclusion.map left +
        TraceCorQRepresentablePresheaf.inclusion.map right :=
  TraceCorQRepresentablePresheaf.inclusion_map_add
    left
    right

/-- Inclusion of lifted representables preserves rational scalar multiplication. -/
theorem TraceAnalyticMotive.representableInclusion_map_smul
    {source target : TraceCorQRepresentablePresheaf}
    (coefficient : Rat)
    (morphism : source ⟶ target) :
    TraceCorQRepresentablePresheaf.inclusion.map (coefficient • morphism) =
      coefficient • TraceCorQRepresentablePresheaf.inclusion.map morphism :=
  TraceCorQRepresentablePresheaf.inclusion_map_smul
    coefficient
    morphism

/-- The motive root exposes evaluation of trace presheaves on one trace object. -/
def TraceAnalyticMotive.presheafEvaluation
    (object : TraceCorQObject) :
    TraceCorQPresheaf ⥤ ModuleCat Rat :=
  TraceCorQPresheaf.evaluation object

/-- Motive-root presheaf evaluation sends a presheaf to its sections. -/
theorem TraceAnalyticMotive.presheafEvaluation_obj
    (object : TraceCorQObject)
    (presheaf : TraceCorQPresheaf) :
    (TraceAnalyticMotive.presheafEvaluation object).obj presheaf =
      presheaf.sections object :=
  TraceCorQPresheaf.evaluation_obj
    object
    presheaf

/-- Motive-root presheaf evaluation sends a presheaf morphism to its section component. -/
theorem TraceAnalyticMotive.presheafEvaluation_map
    (object : TraceCorQObject)
    {source target : TraceCorQPresheaf}
    (morphism : TraceCorQPresheafHom source target) :
    (TraceAnalyticMotive.presheafEvaluation object).map morphism =
      morphism.component object :=
  TraceCorQPresheaf.evaluation_map
    object
    morphism

/-- Motive-root presheaf evaluation preserves addition of presheaf morphisms. -/
theorem TraceAnalyticMotive.presheafEvaluation_map_add
    (object : TraceCorQObject)
    {source target : TraceCorQPresheaf}
    (left right : source ⟶ target) :
    (TraceAnalyticMotive.presheafEvaluation object).map (left + right) =
      (TraceAnalyticMotive.presheafEvaluation object).map left +
        (TraceAnalyticMotive.presheafEvaluation object).map right :=
  TraceCorQPresheaf.evaluation_map_add
    object
    left
    right

/-- Motive-root presheaf evaluation preserves rational scalar multiplication. -/
theorem TraceAnalyticMotive.presheafEvaluation_map_smul
    (object : TraceCorQObject)
    {source target : TraceCorQPresheaf}
    (coefficient : Rat)
    (morphism : source ⟶ target) :
    (TraceAnalyticMotive.presheafEvaluation object).map
        (coefficient • morphism) =
      coefficient • (TraceAnalyticMotive.presheafEvaluation object).map
        morphism :=
  TraceCorQPresheaf.evaluation_map_smul
    object
    coefficient
    morphism

/-- The formal localized-word category wraps certified trace-correspondence objects. -/
theorem TraceAnalyticMotive.localizedWordObject_underlying
    (object : TraceCorQObject) :
    (TraceLocalizedWordObject.ofTraceObject object).underlying =
      object :=
  TraceLocalizedWordObject.ofTraceObject_underlying
    object

/-- The current unstable analytic-motive envelope is the localized-word category. -/
def TraceAnalyticMotive.unstableCategory :
    CategoryTheory.Category TraceUnstableAnalyticMotive :=
  traceUnstableAnalyticMotiveCategory

/-- A trace object gives an object of the unstable analytic-motive envelope. -/
theorem TraceAnalyticMotive.unstableOfTraceObject_underlying
    (object : TraceCorQObject) :
    (TraceUnstableAnalyticMotive.ofTraceObject object).underlying =
      object :=
  TraceUnstableAnalyticMotive.ofTraceObject_underlying
    object

/-- The unstable object imported rectangles are extracted from its certificate ledger. -/
theorem TraceAnalyticMotive.unstableImportedRectangles_eq_certificateLedger_rectangles
    (object : TraceUnstableAnalyticMotive) :
    object.importedRectangles =
      object.certificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.importedRectangles_eq_certificateLedger_rectangles
    object

/-- The unstable object imported-rectangle count is counted by its certificate ledger. -/
theorem TraceAnalyticMotive.unstableImportedRectangleCount_eq_certificateLedger_count
    (object : TraceUnstableAnalyticMotive) :
    object.importedRectangleCount =
      object.certificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.importedRectangleCount_eq_certificateLedger_count
    object

/-- The unstable object trace-bookkeeping count is counted by its certificate ledger. -/
theorem TraceAnalyticMotive.unstableTraceBookkeepingCount_eq_certificateLedger_count
    (object : TraceUnstableAnalyticMotive) :
    object.traceBookkeepingCount =
      object.certificateLedger.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.traceBookkeepingCount_eq_certificateLedger_count
    object

/-- The unstable object rewrite-step count is counted by its certificate ledger. -/
theorem TraceAnalyticMotive.unstableRewriteStepCount_eq_certificateLedger_count
    (object : TraceUnstableAnalyticMotive) :
    object.rewriteStepCount =
      object.certificateLedger.rewriteStepCount :=
  TraceUnstableAnalyticMotive.rewriteStepCount_eq_certificateLedger_count
    object

/-- An arbitrary unstable hom endpoint imported count is its endpoint list length. -/
theorem TraceAnalyticMotive.unstableHom_endpointImportedRectangleCount_eq_length
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    hom.endpointImportedRectangleCount =
      hom.endpointImportedRectangles.length :=
  TraceUnstableAnalyticMotiveHom.endpointImportedRectangleCount_eq_length
    hom

/-- An arbitrary unstable hom endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableHom_endpointImportedRectangles_eq_certificateLedger_rectangles
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    hom.endpointImportedRectangles =
      hom.endpointCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotiveHom.endpointImportedRectangles_eq_certificateLedger_rectangles
    hom

/-- An arbitrary unstable hom endpoint imported count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableHom_endpointImportedRectangleCount_eq_certificateLedger_count
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    hom.endpointImportedRectangleCount =
      hom.endpointCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotiveHom.endpointImportedRectangleCount_eq_certificateLedger_count
    hom

/-- An arbitrary unstable hom endpoint bookkeeping count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableHom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    hom.endpointTraceBookkeepingCount =
      hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceUnstableAnalyticMotiveHom.endpointTraceBookkeepingCount_eq_certificateLedger_count
    hom

/-- An arbitrary unstable hom endpoint rewrite-step count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableHom_endpointRewriteStepCount_eq_certificateLedger_count
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    hom.endpointRewriteStepCount =
      hom.endpointCertificateLedger.rewriteStepCount :=
  TraceUnstableAnalyticMotiveHom.endpointRewriteStepCount_eq_certificateLedger_count
    hom

end AnalyticMotives
end LFunctions
end Boundary

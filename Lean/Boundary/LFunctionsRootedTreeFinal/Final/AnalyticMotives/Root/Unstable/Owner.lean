import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Unstable.CategoryLaws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Localization.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Localization.Owner

/-!
# Top-level unstable analytic-motive wrappers

This file owns top-level root wrappers for representable sections and the
current unstable analytic-motive envelope.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic-motives root exposes representable trace-presheaf sections. -/
theorem AnalyticMotivesRoot.representable_sections
    (source target : TraceCorQObject) :
    (TraceCorQPresheaf.representable target).sections source =
      ModuleCat.of Rat (source ⟶ target) :=
  TraceAnalyticMotive.representable_sections
    source
    target

/-- The analytic-motives root exposes the lifted representable trace-presheaf object. -/
def AnalyticMotivesRoot.representableObject
    (object : TraceCorQObject) :
    TraceCorQRepresentablePresheaf :=
  TraceAnalyticMotive.representableObject object

/-- The lifted representable object has the expected ambient presheaf. -/
theorem AnalyticMotivesRoot.representableObject_presheaf
    (object : TraceCorQObject) :
    (AnalyticMotivesRoot.representableObject object).presheaf =
      TraceCorQPresheaf.representable object :=
  TraceAnalyticMotive.representableObject_presheaf
    object

/-- Inclusion after lifted Yoneda is the ambient Q-linear Yoneda functor. -/
theorem AnalyticMotivesRoot.representableYoneda_comp_inclusion :
    TraceCorQRepresentablePresheaf.yoneda ⋙
        TraceCorQRepresentablePresheaf.inclusion =
      TraceCorQPresheaf.yoneda :=
  TraceAnalyticMotive.representableYoneda_comp_inclusion

/-- The analytic-motives root exposes the lifted-Yoneda trace preimage. -/
noncomputable def AnalyticMotivesRoot.representableYonedaPreimage
    {source target : TraceCorQObject}
    (morphism :
      AnalyticMotivesRoot.representableObject source ⟶
        AnalyticMotivesRoot.representableObject target) :
    source ⟶ target :=
  TraceAnalyticMotive.representableYonedaPreimage
    morphism

/-- Lifted-Yoneda preimage recovers the trace correspondence from a lifted-Yoneda map. -/
theorem AnalyticMotivesRoot.representableYonedaPreimage_yonedaMap
    {source target : TraceCorQObject}
    (morphism : source ⟶ target) :
    AnalyticMotivesRoot.representableYonedaPreimage
        ((TraceCorQRepresentablePresheaf.yoneda).map morphism) =
      morphism :=
  TraceAnalyticMotive.representableYonedaPreimage_yonedaMap
    morphism

/-- Every lifted-Yoneda morphism is recovered from its root trace preimage. -/
theorem AnalyticMotivesRoot.yonedaMap_representableYonedaPreimage
    {source target : TraceCorQObject}
    (morphism :
      AnalyticMotivesRoot.representableObject source ⟶
        AnalyticMotivesRoot.representableObject target) :
    (TraceCorQRepresentablePresheaf.yoneda).map
        (AnalyticMotivesRoot.representableYonedaPreimage morphism) =
      morphism :=
  TraceAnalyticMotive.yonedaMap_representableYonedaPreimage
    morphism

/-- Root lifted-Yoneda preimage sends identity to identity. -/
theorem AnalyticMotivesRoot.representableYonedaPreimage_id
    (object : TraceCorQObject) :
    AnalyticMotivesRoot.representableYonedaPreimage
        (𝟙 (AnalyticMotivesRoot.representableObject object)) =
      𝟙 object :=
  TraceAnalyticMotive.representableYonedaPreimage_id
    object

/-- Root lifted-Yoneda preimage sends composition to trace composition. -/
theorem AnalyticMotivesRoot.representableYonedaPreimage_comp
    {first second third : TraceCorQObject}
    (left :
      AnalyticMotivesRoot.representableObject first ⟶
        AnalyticMotivesRoot.representableObject second)
    (right :
      AnalyticMotivesRoot.representableObject second ⟶
        AnalyticMotivesRoot.representableObject third) :
    AnalyticMotivesRoot.representableYonedaPreimage (left ≫ right) =
      AnalyticMotivesRoot.representableYonedaPreimage left ≫
        AnalyticMotivesRoot.representableYonedaPreimage right :=
  TraceAnalyticMotive.representableYonedaPreimage_comp
    left
    right

/-- Inclusion of lifted representables preserves addition of morphisms. -/
theorem AnalyticMotivesRoot.representableInclusion_map_add
    {source target : TraceCorQRepresentablePresheaf}
    (left right : source ⟶ target) :
    TraceCorQRepresentablePresheaf.inclusion.map (left + right) =
      TraceCorQRepresentablePresheaf.inclusion.map left +
        TraceCorQRepresentablePresheaf.inclusion.map right :=
  TraceAnalyticMotive.representableInclusion_map_add
    left
    right

/-- Inclusion of lifted representables preserves rational scalar multiplication. -/
theorem AnalyticMotivesRoot.representableInclusion_map_smul
    {source target : TraceCorQRepresentablePresheaf}
    (coefficient : Rat)
    (morphism : source ⟶ target) :
    TraceCorQRepresentablePresheaf.inclusion.map (coefficient • morphism) =
      coefficient • TraceCorQRepresentablePresheaf.inclusion.map morphism :=
  TraceAnalyticMotive.representableInclusion_map_smul
    coefficient
    morphism

/-- The analytic-motives root exposes evaluation of trace presheaves on one trace object. -/
def AnalyticMotivesRoot.presheafEvaluation
    (object : TraceCorQObject) :
    TraceCorQPresheaf ⥤ ModuleCat Rat :=
  TraceAnalyticMotive.presheafEvaluation object

/-- Top-root presheaf evaluation sends a presheaf to its sections. -/
theorem AnalyticMotivesRoot.presheafEvaluation_obj
    (object : TraceCorQObject)
    (presheaf : TraceCorQPresheaf) :
    (AnalyticMotivesRoot.presheafEvaluation object).obj presheaf =
      presheaf.sections object :=
  TraceAnalyticMotive.presheafEvaluation_obj
    object
    presheaf

/-- Top-root presheaf evaluation sends a presheaf morphism to its section component. -/
theorem AnalyticMotivesRoot.presheafEvaluation_map
    (object : TraceCorQObject)
    {source target : TraceCorQPresheaf}
    (morphism : TraceCorQPresheafHom source target) :
    (AnalyticMotivesRoot.presheafEvaluation object).map morphism =
      morphism.component object :=
  TraceAnalyticMotive.presheafEvaluation_map
    object
    morphism

/-- Top-root presheaf evaluation preserves addition of presheaf morphisms. -/
theorem AnalyticMotivesRoot.presheafEvaluation_map_add
    (object : TraceCorQObject)
    {source target : TraceCorQPresheaf}
    (left right : source ⟶ target) :
    (AnalyticMotivesRoot.presheafEvaluation object).map (left + right) =
      (AnalyticMotivesRoot.presheafEvaluation object).map left +
        (AnalyticMotivesRoot.presheafEvaluation object).map right :=
  TraceAnalyticMotive.presheafEvaluation_map_add
    object
    left
    right

/-- Top-root presheaf evaluation preserves rational scalar multiplication. -/
theorem AnalyticMotivesRoot.presheafEvaluation_map_smul
    (object : TraceCorQObject)
    {source target : TraceCorQPresheaf}
    (coefficient : Rat)
    (morphism : source ⟶ target) :
    (AnalyticMotivesRoot.presheafEvaluation object).map
        (coefficient • morphism) =
      coefficient • (AnalyticMotivesRoot.presheafEvaluation object).map
        morphism :=
  TraceAnalyticMotive.presheafEvaluation_map_smul
    object
    coefficient
    morphism

/-- The analytic-motives root exposes the unstable analytic-motive category. -/
def AnalyticMotivesRoot.unstableCategory :
    CategoryTheory.Category TraceUnstableAnalyticMotive :=
  TraceAnalyticMotive.unstableCategory

/-- The analytic-motives root exposes trace objects inside the unstable envelope. -/
theorem AnalyticMotivesRoot.unstableOfTraceObject_underlying
    (object : TraceCorQObject) :
    (TraceUnstableAnalyticMotive.ofTraceObject object).underlying =
      object :=
  TraceAnalyticMotive.unstableOfTraceObject_underlying
    object

/-- The analytic-motives root exposes unstable object rectangle-ledger extraction. -/
theorem AnalyticMotivesRoot.unstableImportedRectangles_eq_certificateLedger_rectangles
    (object : TraceUnstableAnalyticMotive) :
    object.importedRectangles =
      object.certificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableImportedRectangles_eq_certificateLedger_rectangles
    object

/-- The analytic-motives root exposes unstable object rectangle-count ledger agreement. -/
theorem AnalyticMotivesRoot.unstableImportedRectangleCount_eq_certificateLedger_count
    (object : TraceUnstableAnalyticMotive) :
    object.importedRectangleCount =
      object.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableImportedRectangleCount_eq_certificateLedger_count
    object

/-- The analytic-motives root exposes unstable object bookkeeping ledger agreement. -/
theorem AnalyticMotivesRoot.unstableTraceBookkeepingCount_eq_certificateLedger_count
    (object : TraceUnstableAnalyticMotive) :
    object.traceBookkeepingCount =
      object.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableTraceBookkeepingCount_eq_certificateLedger_count
    object

/-- The analytic-motives root exposes unstable object rewrite-step ledger agreement. -/
theorem AnalyticMotivesRoot.unstableRewriteStepCount_eq_certificateLedger_count
    (object : TraceUnstableAnalyticMotive) :
    object.rewriteStepCount =
      object.certificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.unstableRewriteStepCount_eq_certificateLedger_count
    object

/-- The analytic-motives root exposes arbitrary unstable hom endpoint-count lengths. -/
theorem AnalyticMotivesRoot.unstableHom_endpointImportedRectangleCount_eq_length
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    hom.endpointImportedRectangleCount =
      hom.endpointImportedRectangles.length :=
  TraceAnalyticMotive.unstableHom_endpointImportedRectangleCount_eq_length
    hom

/-- The analytic-motives root exposes arbitrary unstable hom endpoint rectangle ledgers. -/
theorem AnalyticMotivesRoot.unstableHom_endpointImportedRectangles_eq_certificateLedger_rectangles
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    hom.endpointImportedRectangles =
      hom.endpointCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableHom_endpointImportedRectangles_eq_certificateLedger_rectangles
    hom

/-- The analytic-motives root exposes arbitrary unstable hom endpoint rectangle-count ledgers. -/
theorem AnalyticMotivesRoot.unstableHom_endpointImportedRectangleCount_eq_certificateLedger_count
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    hom.endpointImportedRectangleCount =
      hom.endpointCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableHom_endpointImportedRectangleCount_eq_certificateLedger_count
    hom

/-- The analytic-motives root exposes arbitrary unstable hom endpoint ledger counts. -/
theorem AnalyticMotivesRoot.unstableHom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    hom.endpointTraceBookkeepingCount =
      hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableHom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    hom

/-- The analytic-motives root exposes arbitrary unstable hom endpoint rewrite-step ledgers. -/
theorem AnalyticMotivesRoot.unstableHom_endpointRewriteStepCount_eq_certificateLedger_count
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    hom.endpointRewriteStepCount =
      hom.endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.unstableHom_endpointRewriteStepCount_eq_certificateLedger_count
    hom

end AnalyticMotives
end LFunctions
end Boundary

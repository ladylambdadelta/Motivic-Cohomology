import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TateStabilization.RotationExactness.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TateStabilization.ShortComplex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TateStabilization.RotationShortComplex.Owner

/-!
# Tate weight-drop root facade

This file owns the top-root facade theorems for Tate weight-drop localization,
bounded additive complexes, and their mapping-cone triangle package.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public root summary: Tate weight-drop has the named localized forward arrow as hom. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDropIso_hom
    (source target : QTraceExpression) :
    (TraceTateStabilizationLocalization.weightDropIso source target).hom =
      TraceLocalizationInput.tateWeightDropForwardArrow source target :=
  AnalyticMotivesRoot.rootSummary_tateWeightDropIso_hom
    source
    target

/-- Public root summary: Tate weight-drop has the named localized inverse arrow as
inverse. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDropIso_inv
    (source target : QTraceExpression) :
    (TraceTateStabilizationLocalization.weightDropIso source target).inv =
      TraceLocalizationInput.tateWeightDropInverseArrow source target :=
  AnalyticMotivesRoot.rootSummary_tateWeightDropIso_inv
    source
    target

/-- Public root summary: Tate weight-drop hom followed by inverse is identity in the
localization quotient. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDropIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceTateStabilizationLocalization.weightDropIso source target).hom
        (TraceTateStabilizationLocalization.weightDropIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.tateWeightDrop source target).sourceObject :=
  AnalyticMotivesRoot.rootSummary_tateWeightDropIso_hom_comp_inv
    source
    target

/-- Public root summary: Tate weight-drop inverse followed by hom is identity in the
localization quotient. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDropIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceTateStabilizationLocalization.weightDropIso source target).inv
        (TraceTateStabilizationLocalization.weightDropIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.tateWeightDrop source target).targetObject :=
  AnalyticMotivesRoot.rootSummary_tateWeightDropIso_inv_comp_hom
    source
    target

/-- Public root summary: Tate weight-drop hom followed by inverse is categorical
identity. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDropIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceTateStabilizationLocalization.weightDropIso source target).hom ≫
        (TraceTateStabilizationLocalization.weightDropIso source target).inv =
      (𝟙 (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject
          (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject) :=
  AnalyticMotivesRoot.rootSummary_tateWeightDropIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- Public root summary: Tate weight-drop inverse followed by hom is categorical
identity. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDropIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceTateStabilizationLocalization.weightDropIso source target).inv ≫
        (TraceTateStabilizationLocalization.weightDropIso source target).hom =
      (𝟙 (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject
          (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject) :=
  AnalyticMotivesRoot.rootSummary_tateWeightDropIso_inv_comp_hom_eq_categoryIdentity
    source
    target

/-- Public root summary: the Tate weight-drop source has a one-component additive object. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_additiveSourceObject_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).additiveSourceObject.length =
      1 :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_additiveSourceObject_length
    source
    target

/-- Public root summary: the Tate weight-drop target has a one-component additive object. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_additiveTargetObject_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).additiveTargetObject.length =
      1 :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_additiveTargetObject_length
    source
    target

/-- Public root summary: the zero-index additive source component of Tate weight-drop has
the source expression. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_additiveSourceObject_component_zero_source
    (source target : QTraceExpression) :
    ((TraceLocalizationInput.tateWeightDrop source target).additiveSourceObject.component 0).source =
      source :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_additiveSourceObject_component_zero_source
    source
    target

/-- Public root summary: the zero-index additive target component of Tate weight-drop has
the target expression. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_additiveTargetObject_component_zero_source
    (source target : QTraceExpression) :
    ((TraceLocalizationInput.tateWeightDrop source target).additiveTargetObject.component 0).source =
      target :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_additiveTargetObject_component_zero_source
    source
    target

/-- Public root summary: the Tate weight-drop additive source weight is computed from its
certified source object. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_additiveSourceObject_weightLevel
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).additiveSourceObject.weightLevel =
      Nat.max
        (TraceLocalizationInput.tateWeightDrop source target).sourceObject.weightLevel
        0 :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_additiveSourceObject_weightLevel
    source
    target

/-- Public root summary: the Tate weight-drop additive target weight is computed from its
certified target object. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_additiveTargetObject_weightLevel
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).additiveTargetObject.weightLevel =
      Nat.max
        (TraceLocalizationInput.tateWeightDrop source target).targetObject.weightLevel
        0 :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_additiveTargetObject_weightLevel
    source
    target

/-- Public root summary: the Tate weight-drop source has a bounded singleton additive
object package. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedAdditiveSourceObject_object
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveSourceObject.object =
      (TraceLocalizationInput.tateWeightDrop source target).additiveSourceObject :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedAdditiveSourceObject_object
    source
    target

/-- Public root summary: the Tate weight-drop target has a bounded singleton additive
object package. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedAdditiveTargetObject_object
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveTargetObject.object =
      (TraceLocalizationInput.tateWeightDrop source target).additiveTargetObject :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedAdditiveTargetObject_object
    source
    target

/-- Public root summary: the Tate weight-drop bounded source package satisfies its
canonical source bound. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedAdditiveSourceObject_weightLevel_le
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveSourceObject.object.weightLevel ≤
      (TraceLocalizationInput.tateWeightDrop source target).additiveSourceObjectWeightBound :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedAdditiveSourceObject_weightLevel_le
    source
    target

/-- Public root summary: the Tate weight-drop bounded target package satisfies its
canonical target bound. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedAdditiveTargetObject_weightLevel_le
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveTargetObject.object.weightLevel ≤
      (TraceLocalizationInput.tateWeightDrop source target).additiveTargetObjectWeightBound :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedAdditiveTargetObject_weightLevel_le
    source
    target

/-- Public root summary: the Tate weight-drop additive matrix has the underlying trace
hom as its zero-zero entry. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_additiveHom_entry_zero
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).additiveHom.entry 0 0 =
      (TraceLocalizationInput.tateWeightDrop source target).traceHom :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_additiveHom_entry_zero
    source
    target

/-- Public root summary: the degree-zero object of the Tate weight-drop source complex is
the Tate weight-drop additive source object. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_additiveSourceComplex_objectAt_zero
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).additiveSourceComplex.objectAt 0 =
      (TraceLocalizationInput.tateWeightDrop source target).additiveSourceObject :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_additiveSourceComplex_objectAt_zero
    source
    target

/-- Public root summary: the degree-zero object of the Tate weight-drop target complex is
the Tate weight-drop additive target object. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_additiveTargetComplex_objectAt_zero
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).additiveTargetComplex.objectAt 0 =
      (TraceLocalizationInput.tateWeightDrop source target).additiveTargetObject :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_additiveTargetComplex_objectAt_zero
    source
    target

/-- Public root summary: the Tate weight-drop source complex has one degree-zero
component. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_additiveSourceComplex_objectAt_zero_length
    (source target : QTraceExpression) :
    ((TraceLocalizationInput.tateWeightDrop source target).additiveSourceComplex.objectAt
      0).length =
      1 :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_additiveSourceComplex_objectAt_zero_length
    source
    target

/-- Public root summary: the Tate weight-drop target complex has one degree-zero
component. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_additiveTargetComplex_objectAt_zero_length
    (source target : QTraceExpression) :
    ((TraceLocalizationInput.tateWeightDrop source target).additiveTargetComplex.objectAt
      0).length =
      1 :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_additiveTargetComplex_objectAt_zero_length
    source
    target

/-- Public root summary: the bounded Tate weight-drop source complex has the source
complex underneath. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedAdditiveSourceComplex_complex
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveSourceComplex.complex =
      (TraceLocalizationInput.tateWeightDrop source target).additiveSourceComplex :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedAdditiveSourceComplex_complex
    source
    target

/-- Public root summary: the bounded Tate weight-drop target complex has the target
complex underneath. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedAdditiveTargetComplex_complex
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveTargetComplex.complex =
      (TraceLocalizationInput.tateWeightDrop source target).additiveTargetComplex :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedAdditiveTargetComplex_complex
    source
    target

/-- Public root summary: the bounded Tate weight-drop source complex satisfies its source
weight bound in every degree. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedAdditiveSourceComplex_degreeWeight_le
    (source target : QTraceExpression)
    (degree : ℤ) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveSourceComplex.complex.degreeWeight
        degree ≤
      (TraceLocalizationInput.tateWeightDrop source target).additiveSourceObjectWeightBound :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedAdditiveSourceComplex_degreeWeight_le
    source
    target
    degree

/-- Public root summary: the bounded Tate weight-drop target complex satisfies its target
weight bound in every degree. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedAdditiveTargetComplex_degreeWeight_le
    (source target : QTraceExpression)
    (degree : ℤ) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveTargetComplex.complex.degreeWeight
        degree ≤
      (TraceLocalizationInput.tateWeightDrop source target).additiveTargetObjectWeightBound :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedAdditiveTargetComplex_degreeWeight_le
    source
    target
    degree

/-- Public root summary: the Tate weight-drop source complex rebounded to the common
bound has the source complex underneath. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_commonBoundedAdditiveSourceComplex_complex
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).commonBoundedAdditiveSourceComplex.complex =
      (TraceLocalizationInput.tateWeightDrop source target).additiveSourceComplex :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_commonBoundedAdditiveSourceComplex_complex
    source
    target

/-- Public root summary: the Tate weight-drop target complex rebounded to the common
bound has the target complex underneath. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_commonBoundedAdditiveTargetComplex_complex
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).commonBoundedAdditiveTargetComplex.complex =
      (TraceLocalizationInput.tateWeightDrop source target).additiveTargetComplex :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_commonBoundedAdditiveTargetComplex_complex
    source
    target

/-- Public root summary: the bounded Tate weight-drop complex map is the underlying
degree-zero additive complex map. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedAdditiveComplexHom_eq
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom =
      (TraceLocalizationInput.tateWeightDrop source target).additiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedAdditiveComplexHom_eq
    source
    target

/-- Public root summary: the bounded Tate weight-drop complex map has the expected
degree-zero component. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedAdditiveComplexHom_f_zero
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom.f 0 =
      (HomologicalComplex.singleObjXSelf
        (ComplexShape.up ℤ)
        (0 : ℤ)
        (TraceLocalizationInput.tateWeightDrop source target).additiveSourceObject).hom ≫
        (TraceLocalizationInput.tateWeightDrop source target).additiveHom ≫
      (HomologicalComplex.singleObjXSelf
        (ComplexShape.up ℤ)
        (0 : ℤ)
        (TraceLocalizationInput.tateWeightDrop source target).additiveTargetObject).inv :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedAdditiveComplexHom_f_zero
    source
    target

/-- Public root summary: the Tate weight-drop bounded mapping-cone triangle has the
common-bounded source as first bounded representative. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeTriangle_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.first =
      (TraceLocalizationInput.tateWeightDrop source target).commonBoundedAdditiveSourceComplex :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeTriangle_first
    source
    target

/-- Public root summary: the Tate weight-drop bounded mapping-cone triangle has the
common-bounded target as second bounded representative. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeTriangle_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.second =
      (TraceLocalizationInput.tateWeightDrop source target).commonBoundedAdditiveTargetComplex :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeTriangle_second
    source
    target

/-- Public root summary: the Tate weight-drop bounded mapping-cone triangle is the
ordinary bounded mapping-cone triangle of the bounded Tate map. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeTriangle_triangle
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.triangle
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeTriangle_triangle
    source
    target

/-- Public root summary: the Tate weight-drop bounded mapping-cone triangle is
distinguished. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeTriangle_distinguished
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeTriangle_distinguished
    source
    target

/-- Public root summary: the first two morphisms of the Tate weight-drop bounded
mapping-cone triangle compose to zero. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle.mor₁ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle.mor₂ =
      0 :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeTriangle_first_comp_second
    source
    target

/-- Public root summary: the second and third morphisms of the Tate weight-drop bounded
mapping-cone triangle compose to zero. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle.mor₂ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle.mor₃ =
      0 :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeTriangle_second_comp_third
    source
    target

/-- Public root summary: the third morphism followed by the shifted first morphism of
the Tate weight-drop bounded mapping-cone triangle is zero. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle.mor₃ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeTriangle_third_comp_shifted_first
    source
    target

/-- Public root summary: the Tate bounded map followed by its cone-inclusion map is
zero. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedCone_firstMap_comp_secondMap
    (source target : QTraceExpression) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
          (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom ≫
        TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
          (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom =
      0 :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedCone_firstMap_comp_secondMap
    source
    target

/-- Public root summary: the Tate cone-inclusion map followed by its connecting map is
zero. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedCone_secondMap_comp_connectingMap
    (source target : QTraceExpression) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
          (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom ≫
        TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
          (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom =
      0 :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedCone_secondMap_comp_connectingMap
    source
    target

/-- Public root summary: the Tate connecting map followed by the shifted bounded map is
zero. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedCone_connectingMap_comp_shifted_firstMap
    (source target : QTraceExpression) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
          (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
          (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom)⟦(1 : ℤ)⟧' =
      0 :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedCone_connectingMap_comp_shifted_firstMap
    source
    target

/-- Public root summary: the Tate weight-drop rotated full bounded mapping-cone triangle
is distinguished. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeRotatedTriangle_distinguished
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedTriangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeRotatedTriangle_distinguished
    source
    target

/-- Public root summary: the Tate weight-drop inverse-rotated full bounded mapping-cone
triangle is distinguished. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeInverseRotatedTriangle_distinguished
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedTriangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeInverseRotatedTriangle_distinguished
    source
    target

/-- Public root summary: the Tate weight-drop complex morphism is induced in degree zero
from the Tate weight-drop additive matrix. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_additiveComplexHom_f_zero
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).additiveComplexHom.f 0 =
      (HomologicalComplex.singleObjXSelf
        (ComplexShape.up ℤ)
        (0 : ℤ)
        (TraceLocalizationInput.tateWeightDrop source target).additiveSourceObject).hom ≫
        (TraceLocalizationInput.tateWeightDrop source target).additiveHom ≫
      (HomologicalComplex.singleObjXSelf
        (ComplexShape.up ℤ)
        (0 : ℤ)
        (TraceLocalizationInput.tateWeightDrop source target).additiveTargetObject).inv :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_additiveComplexHom_f_zero
    source
    target

end AnalyticMotives
end LFunctions
end Boundary

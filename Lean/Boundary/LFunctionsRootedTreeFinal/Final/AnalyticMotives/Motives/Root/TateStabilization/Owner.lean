import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.TateStabilization.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Complexes.LocalizationInput.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Complexes.Singleton.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homs.LocalizationInput.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Objects.LocalizationInput.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Complexes.LocalizationInput.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Maps.LocalizationInput.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Objects.LocalizationInput.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.LocalizationInput.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.LocalizationInput.Exactness.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.LocalizationInput.NamedMaps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.LocalizationInput.Rotation.Exactness.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.LocalizationInput.Rotation.Owner

/-!
# Motive-root Tate stabilization facade

This file exposes the analytic Tate weight-drop localization through the
motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Motive-root facade: Tate weight-drop has the named localized forward arrow as hom. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDropIso_hom
    (source target : QTraceExpression) :
    (TraceTateStabilizationLocalization.weightDropIso source target).hom =
      TraceLocalizationInput.tateWeightDropForwardArrow source target :=
  TraceTateStabilization.weightDropIso_hom
    source
    target

/-- Motive-root facade: Tate weight-drop has the named localized inverse arrow as inverse. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDropIso_inv
    (source target : QTraceExpression) :
    (TraceTateStabilizationLocalization.weightDropIso source target).inv =
      TraceLocalizationInput.tateWeightDropInverseArrow source target :=
  TraceTateStabilization.weightDropIso_inv
    source
    target

/-- Motive-root facade: Tate weight-drop hom followed by inverse is identity in the
localization quotient. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDropIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceTateStabilizationLocalization.weightDropIso source target).hom
        (TraceTateStabilizationLocalization.weightDropIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.tateWeightDrop source target).sourceObject :=
  TraceTateStabilization.weightDropIso_hom_comp_inv
    source
    target

/-- Motive-root facade: Tate weight-drop inverse followed by hom is identity in the
localization quotient. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDropIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceTateStabilizationLocalization.weightDropIso source target).inv
        (TraceTateStabilizationLocalization.weightDropIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.tateWeightDrop source target).targetObject :=
  TraceTateStabilization.weightDropIso_inv_comp_hom
    source
    target

/-- Motive-root facade: Tate weight-drop hom followed by inverse is categorical identity. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDropIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceTateStabilizationLocalization.weightDropIso source target).hom ≫
        (TraceTateStabilizationLocalization.weightDropIso source target).inv =
      (𝟙 (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject
          (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject) :=
  TraceTateStabilization.weightDropIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- Motive-root facade: Tate weight-drop inverse followed by hom is categorical identity. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDropIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceTateStabilizationLocalization.weightDropIso source target).inv ≫
        (TraceTateStabilizationLocalization.weightDropIso source target).hom =
      (𝟙 (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject
          (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject) :=
  TraceTateStabilization.weightDropIso_inv_comp_hom_eq_categoryIdentity
    source
    target

/-- Motive-root facade: Tate stabilization uses the unstable-envelope Tate weight-drop
isomorphism. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDropUnstableIso_eq
    (source target : QTraceExpression) :
    TraceUnstableAnalyticMotive.tateWeightDropIso source target =
      TraceLocalizationInput.tateWeightDropLocalizedIso source target :=
  TraceTateStabilization.weightDropUnstableIso_eq
    source
    target

/-- Motive-root facade: the Tate weight-drop source has a one-component additive object. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_additiveSourceObject_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).additiveSourceObject.length =
      1 :=
  TraceLocalizationInput.additiveSourceObject_length
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the Tate weight-drop target has a one-component additive object. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_additiveTargetObject_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).additiveTargetObject.length =
      1 :=
  TraceLocalizationInput.additiveTargetObject_length
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the zero-index additive source component of Tate weight-drop has
the source expression. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_additiveSourceObject_component_zero_source
    (source target : QTraceExpression) :
    ((TraceLocalizationInput.tateWeightDrop source target).additiveSourceObject.component 0).source =
      source :=
  TraceLocalizationInput.additiveSourceObject_component_zero_source
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the zero-index additive target component of Tate weight-drop has
the target expression. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_additiveTargetObject_component_zero_source
    (source target : QTraceExpression) :
    ((TraceLocalizationInput.tateWeightDrop source target).additiveTargetObject.component 0).source =
      target :=
  TraceLocalizationInput.additiveTargetObject_component_zero_source
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the Tate weight-drop additive source weight is computed from its
certified source object. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_additiveSourceObject_weightLevel
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).additiveSourceObject.weightLevel =
      Nat.max
        (TraceLocalizationInput.tateWeightDrop source target).sourceObject.weightLevel
        0 :=
  TraceLocalizationInput.additiveSourceObject_weightLevel
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the Tate weight-drop additive target weight is computed from its
certified target object. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_additiveTargetObject_weightLevel
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).additiveTargetObject.weightLevel =
      Nat.max
        (TraceLocalizationInput.tateWeightDrop source target).targetObject.weightLevel
        0 :=
  TraceLocalizationInput.additiveTargetObject_weightLevel
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the Tate weight-drop source has a bounded singleton additive
object package. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedAdditiveSourceObject_object
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveSourceObject.object =
      (TraceLocalizationInput.tateWeightDrop source target).additiveSourceObject :=
  TraceLocalizationInput.boundedAdditiveSourceObject_object
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the Tate weight-drop target has a bounded singleton additive
object package. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedAdditiveTargetObject_object
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveTargetObject.object =
      (TraceLocalizationInput.tateWeightDrop source target).additiveTargetObject :=
  TraceLocalizationInput.boundedAdditiveTargetObject_object
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the Tate weight-drop bounded source package satisfies its
canonical source bound. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedAdditiveSourceObject_weightLevel_le
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveSourceObject.object.weightLevel ≤
      (TraceLocalizationInput.tateWeightDrop source target).additiveSourceObjectWeightBound :=
  TraceLocalizationInput.boundedAdditiveSourceObject_weightLevel_le
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the Tate weight-drop bounded target package satisfies its
canonical target bound. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedAdditiveTargetObject_weightLevel_le
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveTargetObject.object.weightLevel ≤
      (TraceLocalizationInput.tateWeightDrop source target).additiveTargetObjectWeightBound :=
  TraceLocalizationInput.boundedAdditiveTargetObject_weightLevel_le
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the Tate weight-drop additive matrix has the underlying trace
hom as its zero-zero entry. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_additiveHom_entry_zero
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).additiveHom.entry 0 0 =
      (TraceLocalizationInput.tateWeightDrop source target).traceHom :=
  TraceLocalizationInput.additiveHom_entry_zero
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the degree-zero object of the Tate weight-drop source complex is
the Tate weight-drop additive source object. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_additiveSourceComplex_objectAt_zero
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).additiveSourceComplex.objectAt 0 =
      (TraceLocalizationInput.tateWeightDrop source target).additiveSourceObject :=
  TraceLocalizationInput.additiveSourceComplex_objectAt_zero
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the degree-zero object of the Tate weight-drop target complex is
the Tate weight-drop additive target object. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_additiveTargetComplex_objectAt_zero
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).additiveTargetComplex.objectAt 0 =
      (TraceLocalizationInput.tateWeightDrop source target).additiveTargetObject :=
  TraceLocalizationInput.additiveTargetComplex_objectAt_zero
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the Tate weight-drop source complex has one degree-zero component. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_additiveSourceComplex_objectAt_zero_length
    (source target : QTraceExpression) :
    ((TraceLocalizationInput.tateWeightDrop source target).additiveSourceComplex.objectAt
      0).length =
      1 :=
  TraceLocalizationInput.additiveSourceComplex_objectAt_zero_length
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the Tate weight-drop target complex has one degree-zero component. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_additiveTargetComplex_objectAt_zero_length
    (source target : QTraceExpression) :
    ((TraceLocalizationInput.tateWeightDrop source target).additiveTargetComplex.objectAt
      0).length =
      1 :=
  TraceLocalizationInput.additiveTargetComplex_objectAt_zero_length
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the bounded Tate weight-drop source complex has the source
complex underneath. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedAdditiveSourceComplex_complex
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveSourceComplex.complex =
      (TraceLocalizationInput.tateWeightDrop source target).additiveSourceComplex :=
  TraceLocalizationInput.boundedAdditiveSourceComplex_complex
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the bounded Tate weight-drop target complex has the target
complex underneath. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedAdditiveTargetComplex_complex
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveTargetComplex.complex =
      (TraceLocalizationInput.tateWeightDrop source target).additiveTargetComplex :=
  TraceLocalizationInput.boundedAdditiveTargetComplex_complex
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the bounded Tate weight-drop source complex satisfies its
source weight bound in every degree. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedAdditiveSourceComplex_degreeWeight_le
    (source target : QTraceExpression)
    (degree : ℤ) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveSourceComplex.complex.degreeWeight
        degree ≤
      (TraceLocalizationInput.tateWeightDrop source target).additiveSourceObjectWeightBound :=
  TraceLocalizationInput.boundedAdditiveSourceComplex_degreeWeight_le
    (TraceLocalizationInput.tateWeightDrop source target)
    degree

/-- Motive-root facade: the bounded Tate weight-drop target complex satisfies its target
weight bound in every degree. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedAdditiveTargetComplex_degreeWeight_le
    (source target : QTraceExpression)
    (degree : ℤ) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveTargetComplex.complex.degreeWeight
        degree ≤
      (TraceLocalizationInput.tateWeightDrop source target).additiveTargetObjectWeightBound :=
  TraceLocalizationInput.boundedAdditiveTargetComplex_degreeWeight_le
    (TraceLocalizationInput.tateWeightDrop source target)
    degree

/-- Motive-root facade: the Tate weight-drop source complex rebounded to the common
bound has the source complex underneath. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_commonBoundedAdditiveSourceComplex_complex
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).commonBoundedAdditiveSourceComplex.complex =
      (TraceLocalizationInput.tateWeightDrop source target).additiveSourceComplex :=
  TraceLocalizationInput.commonBoundedAdditiveSourceComplex_complex
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the Tate weight-drop target complex rebounded to the common
bound has the target complex underneath. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_commonBoundedAdditiveTargetComplex_complex
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).commonBoundedAdditiveTargetComplex.complex =
      (TraceLocalizationInput.tateWeightDrop source target).additiveTargetComplex :=
  TraceLocalizationInput.commonBoundedAdditiveTargetComplex_complex
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the bounded Tate weight-drop complex map is the underlying
degree-zero additive complex map. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedAdditiveComplexHom_eq
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom =
      (TraceLocalizationInput.tateWeightDrop source target).additiveComplexHom :=
  TraceLocalizationInput.boundedAdditiveComplexHom_eq
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the bounded Tate weight-drop complex map has the expected
degree-zero component. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedAdditiveComplexHom_f_zero
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
  TraceLocalizationInput.boundedAdditiveComplexHom_f_zero
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the Tate weight-drop bounded mapping-cone triangle has the
common-bounded source as first bounded representative. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeTriangle_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.first =
      (TraceLocalizationInput.tateWeightDrop source target).commonBoundedAdditiveSourceComplex :=
  TraceLocalizationInput.boundedMappingConeTriangle_first
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the Tate weight-drop bounded mapping-cone triangle has the
common-bounded target as second bounded representative. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeTriangle_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.second =
      (TraceLocalizationInput.tateWeightDrop source target).commonBoundedAdditiveTargetComplex :=
  TraceLocalizationInput.boundedMappingConeTriangle_second
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the Tate weight-drop bounded mapping-cone triangle is the
ordinary bounded mapping-cone triangle of the bounded Tate map. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeTriangle_triangle
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.triangle
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeTriangle_triangle
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the Tate weight-drop bounded mapping-cone triangle is
distinguished. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeTriangle_distinguished
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceLocalizationInput.boundedMappingConeTriangle_distinguished
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the first two morphisms of the Tate weight-drop bounded
mapping-cone triangle compose to zero. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle.mor₁ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle.mor₂ =
      0 :=
  TraceLocalizationInput.boundedMappingConeTriangle_first_comp_second
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the second and third morphisms of the Tate weight-drop bounded
mapping-cone triangle compose to zero. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle.mor₂ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle.mor₃ =
      0 :=
  TraceLocalizationInput.boundedMappingConeTriangle_second_comp_third
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the third morphism followed by the shifted first morphism of the
Tate weight-drop bounded mapping-cone triangle is zero. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle.mor₃ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.boundedMappingConeTriangle_third_comp_shifted_first
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the Tate bounded map followed by its cone-inclusion map is
zero. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedCone_firstMap_comp_secondMap
    (source target : QTraceExpression) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
          (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom ≫
        TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
          (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom =
      0 :=
  TraceLocalizationInput.boundedMappingCone_firstMap_comp_secondMap
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the Tate cone-inclusion map followed by its connecting map is
zero. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedCone_secondMap_comp_connectingMap
    (source target : QTraceExpression) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
          (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom ≫
        TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
          (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom =
      0 :=
  TraceLocalizationInput.boundedMappingCone_secondMap_comp_connectingMap
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the Tate connecting map followed by the shifted bounded map is
zero. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedCone_connectingMap_comp_shifted_firstMap
    (source target : QTraceExpression) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
          (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
          (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom)⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.boundedMappingCone_connectingMap_comp_shifted_firstMap
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the Tate weight-drop rotated full bounded mapping-cone triangle
is distinguished. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeRotatedTriangle_distinguished
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedTriangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_distinguished
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the Tate weight-drop inverse-rotated full bounded mapping-cone
triangle is distinguished. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeInverseRotatedTriangle_distinguished
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedTriangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_distinguished
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the first two morphisms of the Tate rotated bounded cone compose
to zero. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeRotatedTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedTriangle.mor₁ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedTriangle.mor₂ =
      0 :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_first_comp_second
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the second and third morphisms of the Tate rotated bounded cone
compose to zero. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedTriangle.mor₃ =
      0 :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_second_comp_third
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the third morphism followed by the shifted first morphism of the
Tate rotated bounded cone is zero. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_third_comp_shifted_first
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the first two morphisms of the Tate inverse-rotated bounded cone
compose to zero. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeInverseRotatedTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedTriangle.mor₁ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedTriangle.mor₂ =
      0 :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_first_comp_second
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the second and third morphisms of the Tate inverse-rotated
bounded cone compose to zero. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeInverseRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedTriangle.mor₃ =
      0 :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_second_comp_third
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the third morphism followed by the shifted first morphism of the
Tate inverse-rotated bounded cone is zero. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the Tate weight-drop complex morphism is induced in degree zero
from the Tate weight-drop additive matrix. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_additiveComplexHom_f_zero
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
  TraceLocalizationInput.additiveComplexHom_f_zero
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Unstable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Localization.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.LocalizationInput.AcyclicGenerators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.LocalizationInput.InversionAcyclicBridge.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.LocalizationInput.ShortComplex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.LocalizationInput.ShortComplex.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.LocalizationInput.NamedExactness.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.LocalizationInput.NamedProjections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.LocalizationInput.NamedRotationExactness.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.LocalizationInput.NamedRotationProjections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.LocalizationInput.NamedShortComplex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.LocalizationInput.NamedTriangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.LocalizationInput.Triangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.LocalizationInput.Triangles.NamedMaps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.LocalizationInput.Triangles.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.LocalizationInput.Triangles.RotationProjections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Localization.Representatives.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Unstable.Inputs.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceExpressions.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.RewriteGenerators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.RewritePaths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.RewriteMaps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.RewriteMaps.ByKind.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.RewriteRelations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.RewriteCertificates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceTransport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.ResidueChannelPresentation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Presheaves.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CalculusGenerators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Comparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Realizations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Examples.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Motives.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TateStabilization.RotationExactness.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TateStabilization.ShortComplex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TateStabilization.RotationShortComplex.Owner

/-!
# Top analytic-motives root facade

This file owns the top-level public root facade.  It collects the public
unstable, localization, localization-input short-complex, named
analytic-generator short-complex, cone triangle, acyclic generators, inversion-acyclic bridges,
projections, exactness, and rotated
exactness and projections, and cone-triangle named-map exactness/rotation projections,
localization-representative, unstable-input,
trace-expression, rewrite-map, by-kind rewrite-map, rewrite-certificate,
rewrite-generator, rewrite-path, rewrite-relation, trace-transport,
residue-channel presentation, Q-linear trace-correspondence, trace-presheaf,
calculus-generator, compact-geometric, comparison, realization, and example
root surfaces, plus the motive-facing aggregate root and Tate short-complex
public surfaces, under the
`AnalyticMotivesRoot` namespace.  The summary theorems below expose a compact
cross-section of the concrete analytic, Q-linear, realization, and example
facts available from the split root surface.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public root summary: certified presentations count imported rectangles by payload length. -/
theorem AnalyticMotivesRoot.rootFacade_residueChannel_importedRectangleCount_eq_length
    (presentation : CertifiedResidueChannelPresentation) :
    presentation.importedRectangleCount =
      presentation.importedRectangles.length :=
  AnalyticMotivesRoot.residueChannelSummary_importedRectangleCount_eq_length
    presentation

/-- Public root summary: trace-correspondence compact composition is trace-hom composition. -/
theorem AnalyticMotivesRoot.rootFacade_compactGenerator_comp_traceHom
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    (left ≫ right).traceHom =
      left.traceHom ≫ right.traceHom :=
  AnalyticMotivesRoot.rootSummary_compactGenerator_comp_traceHom
    left
    right

/-- Public root summary: representable presheaf sections recover trace correspondences. -/
theorem AnalyticMotivesRoot.rootFacade_representable_sections
    (source target : TraceCorQObject) :
    (TraceCorQPresheaf.representable target).sections source =
      ModuleCat.of Rat (source ⟶ target) :=
  AnalyticMotivesRoot.tracePresheafSummary_representable_sections
    source
    target

/-- Public root summary: analytic and algebraic Stokes realizations share the same preimage. -/
theorem AnalyticMotivesRoot.rootFacade_stokes_realization_preimage_agreement
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.stokesMap source target) =
      TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.stokesMap source target) :=
  AnalyticMotivesRoot.realizationSummary_stokes_preimage_agreement
    source
    target

/-- Public root summary: completed-zeta residue rectangle soundness is available at the root. -/
theorem AnalyticMotivesRoot.rootFacade_completedZeta_residueGenerator_sound
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {R : ℝ} (hR : 0 < R) :
    completedZetaZeroPoleFiniteSquareBoundaryTrace f R =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  AnalyticMotivesRoot.examples_completedZeta_residueGenerator_sound
    f
    hPhi
    hR

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

/-- Public root summary: the additive analytic homotopy category is triangulated. -/
def AnalyticMotivesRoot.rootFacade_triangulatedStructure :
    IsTriangulated TraceAnalyticAdditiveHomotopyCategory :=
  AnalyticMotivesRoot.rootSummary_triangulatedStructure

/-- Public root summary: the additive analytic homotopy category is pretriangulated. -/
def AnalyticMotivesRoot.rootFacade_pretriangulatedStructure :
    Pretriangulated TraceAnalyticAdditiveHomotopyCategory :=
  AnalyticMotivesRoot.rootSummary_pretriangulatedStructure

/-- Public root summary: root distinguished triangles are Mathlib's distinguished
triangles. -/
theorem AnalyticMotivesRoot.rootFacade_distinguishedTriangles_eq :
    TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles =
      Pretriangulated.distTriang TraceAnalyticAdditiveHomotopyCategory :=
  AnalyticMotivesRoot.rootSummary_distinguishedTriangles_eq

/-- Public root summary: additive analytic mapping-cone triangles are distinguished. -/
theorem AnalyticMotivesRoot.rootFacade_mappingCone_triangle_distinguished
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target) :
    CochainComplex.mappingCone.triangleh hom ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  AnalyticMotivesRoot.rootSummary_mappingCone_triangle_distinguished
    hom

/-- Public root summary: shifted bounded analytic maps have full iso-bounded cone packages. -/
def AnalyticMotivesRoot.rootFacade_shiftedBoundedConePackage
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded
      bound :=
  AnalyticMotivesRoot.rootSummary_shiftedBoundedConePackage
    hom
    shift

/-- Public root summary: shifted bounded cone short complexes have zero composite. -/
theorem AnalyticMotivesRoot.rootFacade_shiftedBoundedConeShortComplex_zero
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_shortComplex
      hom
      shift).f ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_shortComplex
          hom
          shift).g =
      0 :=
  AnalyticMotivesRoot.rootSummary_shiftedBoundedConeShortComplex_zero
    hom
    shift

/-- Public root summary: rotated bounded cone triangles are distinguished. -/
theorem AnalyticMotivesRoot.rootFacade_rotatedBoundedConeTriangle_distinguished
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    AnalyticMotivesRoot.rootSummary_rotatedBoundedConeTriangle hom ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  AnalyticMotivesRoot.rootSummary_rotatedBoundedConeTriangle_distinguished
    hom

/-- Public root summary: inverse-rotated bounded cone triangles are distinguished. -/
theorem AnalyticMotivesRoot.rootFacade_inverseRotatedBoundedConeTriangle_distinguished
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    AnalyticMotivesRoot.rootSummary_inverseRotatedBoundedConeTriangle hom ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  AnalyticMotivesRoot.rootSummary_inverseRotatedBoundedConeTriangle_distinguished
    hom

/-- Public root summary: the first two morphisms of the rotated bounded cone compose to
zero. -/
theorem AnalyticMotivesRoot.rootFacade_rotatedBoundedConeTriangle_first_comp_second
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (AnalyticMotivesRoot.rootSummary_rotatedBoundedConeTriangle
      hom).mor₁ ≫
        (AnalyticMotivesRoot.rootSummary_rotatedBoundedConeTriangle
          hom).mor₂ =
      0 :=
  AnalyticMotivesRoot.rootSummary_rotatedBoundedConeTriangle_first_comp_second
    hom

/-- Public root summary: the second and third morphisms of the rotated bounded cone
compose to zero. -/
theorem AnalyticMotivesRoot.rootFacade_rotatedBoundedConeTriangle_second_comp_third
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (AnalyticMotivesRoot.rootSummary_rotatedBoundedConeTriangle
      hom).mor₂ ≫
        (AnalyticMotivesRoot.rootSummary_rotatedBoundedConeTriangle
          hom).mor₃ =
      0 :=
  AnalyticMotivesRoot.rootSummary_rotatedBoundedConeTriangle_second_comp_third
    hom

/-- Public root summary: the third morphism followed by the shifted first morphism of the
rotated bounded cone is zero. -/
theorem AnalyticMotivesRoot.rootFacade_rotatedBoundedConeTriangle_third_comp_shifted_first
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (AnalyticMotivesRoot.rootSummary_rotatedBoundedConeTriangle
      hom).mor₃ ≫
        (AnalyticMotivesRoot.rootSummary_rotatedBoundedConeTriangle
          hom).mor₁⟦(1 : ℤ)⟧' =
      0 :=
  AnalyticMotivesRoot.rootSummary_rotatedBoundedConeTriangle_third_comp_shifted_first
    hom

/-- Public root summary: the first two morphisms of the inverse-rotated bounded cone
compose to zero. -/
theorem AnalyticMotivesRoot.rootFacade_inverseRotatedBoundedConeTriangle_first_comp_second
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (AnalyticMotivesRoot.rootSummary_inverseRotatedBoundedConeTriangle
      hom).mor₁ ≫
        (AnalyticMotivesRoot.rootSummary_inverseRotatedBoundedConeTriangle
          hom).mor₂ =
      0 :=
  AnalyticMotivesRoot.rootSummary_inverseRotatedBoundedConeTriangle_first_comp_second
    hom

/-- Public root summary: the second and third morphisms of the inverse-rotated bounded cone
compose to zero. -/
theorem AnalyticMotivesRoot.rootFacade_inverseRotatedBoundedConeTriangle_second_comp_third
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (AnalyticMotivesRoot.rootSummary_inverseRotatedBoundedConeTriangle
      hom).mor₂ ≫
        (AnalyticMotivesRoot.rootSummary_inverseRotatedBoundedConeTriangle
          hom).mor₃ =
      0 :=
  AnalyticMotivesRoot.rootSummary_inverseRotatedBoundedConeTriangle_second_comp_third
    hom

/-- Public root summary: the third morphism followed by the shifted first morphism of the
inverse-rotated bounded cone is zero. -/
theorem AnalyticMotivesRoot.rootFacade_inverseRotatedBoundedConeTriangle_third_comp_shifted_first
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (AnalyticMotivesRoot.rootSummary_inverseRotatedBoundedConeTriangle
      hom).mor₃ ≫
        (AnalyticMotivesRoot.rootSummary_inverseRotatedBoundedConeTriangle
          hom).mor₁⟦(1 : ℤ)⟧' =
      0 :=
  AnalyticMotivesRoot.rootSummary_inverseRotatedBoundedConeTriangle_third_comp_shifted_first
    hom

/-- Public root summary: shifted rotated bounded cone triangles are distinguished. -/
theorem AnalyticMotivesRoot.rootFacade_shiftedRotatedBoundedConeTriangle_distinguished
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    AnalyticMotivesRoot.rootSummary_shiftedRotatedBoundedConeTriangle hom shift ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  AnalyticMotivesRoot.rootSummary_shiftedRotatedBoundedConeTriangle_distinguished
    hom
    shift

/-- Public root summary: shifted inverse-rotated bounded cone triangles are distinguished. -/
theorem AnalyticMotivesRoot.rootFacade_shiftedInverseRotatedBoundedConeTriangle_distinguished
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedBoundedConeTriangle hom shift ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedBoundedConeTriangle_distinguished
    hom
    shift

/-- Public root summary: the first two morphisms of the shifted rotated bounded cone
compose to zero. -/
theorem AnalyticMotivesRoot.rootFacade_shiftedRotatedBoundedConeTriangle_first_comp_second
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (AnalyticMotivesRoot.rootSummary_shiftedRotatedBoundedConeTriangle
      hom
      shift).mor₁ ≫
        (AnalyticMotivesRoot.rootSummary_shiftedRotatedBoundedConeTriangle
          hom
          shift).mor₂ =
      0 :=
  AnalyticMotivesRoot.rootSummary_shiftedRotatedBoundedConeTriangle_first_comp_second
    hom
    shift

/-- Public root summary: the second and third morphisms of the shifted rotated bounded
cone compose to zero. -/
theorem AnalyticMotivesRoot.rootFacade_shiftedRotatedBoundedConeTriangle_second_comp_third
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (AnalyticMotivesRoot.rootSummary_shiftedRotatedBoundedConeTriangle
      hom
      shift).mor₂ ≫
        (AnalyticMotivesRoot.rootSummary_shiftedRotatedBoundedConeTriangle
          hom
          shift).mor₃ =
      0 :=
  AnalyticMotivesRoot.rootSummary_shiftedRotatedBoundedConeTriangle_second_comp_third
    hom
    shift

/-- Public root summary: the third morphism followed by the shifted first morphism of the
shifted rotated bounded cone is zero. -/
theorem AnalyticMotivesRoot.rootFacade_shiftedRotatedBoundedConeTriangle_third_comp_shifted_first
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (AnalyticMotivesRoot.rootSummary_shiftedRotatedBoundedConeTriangle
      hom
      shift).mor₃ ≫
        (AnalyticMotivesRoot.rootSummary_shiftedRotatedBoundedConeTriangle
          hom
          shift).mor₁⟦(1 : ℤ)⟧' =
      0 :=
  AnalyticMotivesRoot.rootSummary_shiftedRotatedBoundedConeTriangle_third_comp_shifted_first
    hom
    shift

/-- Public root summary: the first two morphisms of the shifted inverse-rotated bounded
cone compose to zero. -/
theorem AnalyticMotivesRoot.rootFacade_shiftedInverseRotatedBoundedConeTriangle_first_comp_second
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedBoundedConeTriangle
      hom
      shift).mor₁ ≫
        (AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedBoundedConeTriangle
          hom
          shift).mor₂ =
      0 :=
  AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedBoundedConeTriangle_first_comp_second
    hom
    shift

/-- Public root summary: the second and third morphisms of the shifted inverse-rotated
bounded cone compose to zero. -/
theorem AnalyticMotivesRoot.rootFacade_shiftedInverseRotatedBoundedConeTriangle_second_comp_third
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedBoundedConeTriangle
      hom
      shift).mor₂ ≫
        (AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedBoundedConeTriangle
          hom
          shift).mor₃ =
      0 :=
  AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedBoundedConeTriangle_second_comp_third
    hom
    shift

/-- Public root summary: the third morphism followed by the shifted first morphism of the
shifted inverse-rotated bounded cone is zero. -/
theorem AnalyticMotivesRoot.rootFacade_shiftedInverseRotatedBoundedConeTriangle_third_comp_shifted_first
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedBoundedConeTriangle
      hom
      shift).mor₃ ≫
        (AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedBoundedConeTriangle
          hom
          shift).mor₁⟦(1 : ℤ)⟧' =
      0 :=
  AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedBoundedConeTriangle_third_comp_shifted_first
    hom
    shift

/-- Public root summary: in a shifted rotated cone, cone inclusion followed by
connecting map is zero. -/
theorem AnalyticMotivesRoot.rootFacade_shiftedRotatedCone_secondMap_comp_connectingMap
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
          (hom.shift shift) ≫
        TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
          (hom.shift shift) =
      0 :=
  AnalyticMotivesRoot.rootSummary_shiftedRotatedCone_secondMap_comp_connectingMap
    hom
    shift

/-- Public root summary: in a shifted rotated cone, connecting map followed by the
negative shifted bounded map is zero. -/
theorem AnalyticMotivesRoot.rootFacade_shiftedRotatedCone_connectingMap_comp_negative_shifted_firstMap
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
          (hom.shift shift) ≫
        -((TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
          (hom.shift shift))⟦(1 : ℤ)⟧') =
      0 :=
  AnalyticMotivesRoot.rootSummary_shiftedRotatedCone_connectingMap_comp_negative_shifted_firstMap
    hom
    shift

/-- Public root summary: in a shifted inverse-rotated cone, shifted negative connecting
map followed by the shifted bounded map is zero. -/
theorem AnalyticMotivesRoot.rootFacade_shiftedInverseRotatedCone_negative_shifted_connectingMap_comp_firstMap
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (-(TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        (hom.shift shift))⟦(-1 : ℤ)⟧' ≫
        (shiftEquiv TraceAnalyticAdditiveHomotopyCategory
          (1 : ℤ)).unitIso.inv.app _) ≫
        TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
          (hom.shift shift) =
      0 :=
  AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedCone_negative_shifted_connectingMap_comp_firstMap
    hom
    shift

/-- Public root summary: in a shifted inverse-rotated cone, shifted bounded map followed
by transported cone inclusion is zero. -/
theorem AnalyticMotivesRoot.rootFacade_shiftedInverseRotatedCone_firstMap_comp_transport_secondMap
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
          (hom.shift shift) ≫
        TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
          (hom.shift shift) ≫
        (shiftEquiv TraceAnalyticAdditiveHomotopyCategory
          (1 : ℤ)).counitIso.inv.app _ =
      0 :=
  AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedCone_firstMap_comp_transport_secondMap
    hom
    shift

end AnalyticMotives
end LFunctions
end Boundary

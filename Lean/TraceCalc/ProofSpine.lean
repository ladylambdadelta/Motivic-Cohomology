import TraceCalc.LayerD.PeriodFaithfulnessAssembly
import TraceCalc.LayerD.SourceTracePackage
import TraceCalc.LayerE.TargetComparisonPackage
import TraceCalc.LayerF.RealizationPackage
import TraceCalc.LayerF.StructuredComparisonImplementation
import TraceCalc.LayerG.MockPeriodFaithfulness

universe u v w x y z

namespace TraceCalc

/-- The dedicated proof-spine build root exposes the final API surface. -/
theorem proofSpine_has_final_api : True := trivial

/-- Proof-spine alias exposing the toy end-to-end theorem witness. -/
def proofSpine_mock_period_faithfulness :
    LayerD.AbstractPeriodFaithfulnessTheorem.{0, 0, 0} :=
  LayerG.mock_periodFaithfulness

/-- Proof-spine alias exposing the bundled Layer E theorem-package constructor. -/
def proofSpine_target_package_constructor
    (P : LayerE.MotivicTargetTheoremPackage.{u, v, w}) :
    LayerD.TargetMotivicRecognitionPackage × LayerD.InfinityComparisonPackage :=
  LayerE.motivicTargetTheoremPackage_to_packages P

/-- Proof-spine alias exposing assembly of the decomposed Layer E theorem subpackages. -/
def proofSpine_motivic_target_subpackages_assemble
    (P : LayerE.MotivicTargetTheoremSubpackages.{u, v, w}) :
    LayerE.MotivicTargetTheoremPackage.{u, v, w} :=
  LayerE.motivicTargetSubpackages_assemble P

/-- Proof-spine alias exposing the decomposed Layer E theorem subpackage constructor. -/
def proofSpine_motivic_target_subpackages_to_packages
    (P : LayerE.MotivicTargetTheoremSubpackages.{u, v, w}) :
    LayerD.TargetMotivicRecognitionPackage × LayerD.InfinityComparisonPackage :=
  LayerE.motivicTargetSubpackages_to_packages P

/-- Proof-spine alias exposing Lane I.1. -/
def proofSpine_a1_invariance_ticket
    (P : LayerE.MotivicTargetTheoremSubpackages.{u, v, w})
    (intervalObject : P.Obj)
    (productWithA1 : P.Obj → P.Obj)
    (projectionMap : (X : P.Obj) → P.Hom (productWithA1 X) X)
    (projectionIsA1Equivalence : Prop)
    (projectionIsA1Equivalence_holds : projectionIsA1Equivalence)
    (localizationInvertsProjection : Prop)
    (localizationInvertsProjection_holds : localizationInvertsProjection)
    (A1Invariant_eq :
      P.localization.A1Invariant =
        (projectionIsA1Equivalence ∧ localizationInvertsProjection)) :
    LayerE.A1InvarianceTheoremTicket P.Obj P.Hom :=
  P.a1InvarianceTicket intervalObject productWithA1 projectionMap
    projectionIsA1Equivalence projectionIsA1Equivalence_holds
    localizationInvertsProjection localizationInvertsProjection_holds
    A1Invariant_eq

/-- Proof-spine alias exposing Lane I.2. -/
def proofSpine_nisnevich_descent_ticket
    (P : LayerE.MotivicTargetTheoremSubpackages.{u, v, w})
    (NisnevichSquare : Type u)
    (upperLeft : NisnevichSquare → P.Obj)
    (upperRight : NisnevichSquare → P.Obj)
    (lowerLeft : NisnevichSquare → P.Obj)
    (lowerRight : NisnevichSquare → P.Obj)
    (leftMap : (sq : NisnevichSquare) → P.Hom (upperLeft sq) (lowerLeft sq))
    (topMap : (sq : NisnevichSquare) → P.Hom (upperLeft sq) (upperRight sq))
    (rightMap : (sq : NisnevichSquare) → P.Hom (upperRight sq) (lowerRight sq))
    (bottomMap : (sq : NisnevichSquare) → P.Hom (lowerLeft sq) (lowerRight sq))
    (descentSquareCondition : NisnevichSquare → Prop)
    (descentSquareCondition_holds : ∀ sq : NisnevichSquare, descentSquareCondition sq)
    (localizationSatisfiesDescent : Prop)
    (localizationSatisfiesDescent_holds : localizationSatisfiesDescent)
    (NisnevichDescent_eq :
      P.localization.NisnevichDescent =
        ((∀ sq : NisnevichSquare, descentSquareCondition sq) ∧ localizationSatisfiesDescent)) :
    LayerE.NisnevichDescentTheoremTicket P.Obj P.Hom :=
  P.nisnevichDescentTicket NisnevichSquare upperLeft upperRight lowerLeft lowerRight
    leftMap topMap rightMap bottomMap descentSquareCondition descentSquareCondition_holds
    localizationSatisfiesDescent localizationSatisfiesDescent_holds NisnevichDescent_eq

/-- Proof-spine alias exposing Lane I.3. -/
def proofSpine_localization_ticket
    (P : LayerE.MotivicTargetTheoremSubpackages.{u, v, w})
    (LocalizationDatum : Type u)
    (closedPart : LocalizationDatum → P.Obj)
    (ambientPart : LocalizationDatum → P.Obj)
    (openPart : LocalizationDatum → P.Obj)
    (closedIntoAmbient : (d : LocalizationDatum) → P.Hom (closedPart d) (ambientPart d))
    (ambientToOpen : (d : LocalizationDatum) → P.Hom (ambientPart d) (openPart d))
    (localizationTriangleCondition : LocalizationDatum → Prop)
    (localizationTriangleCondition_holds : ∀ d : LocalizationDatum, localizationTriangleCondition d)
    (localizationExactness : Prop)
    (localizationExactness_holds : localizationExactness)
    (Localization_eq :
      P.localization.Localization =
        ((∀ d : LocalizationDatum, localizationTriangleCondition d) ∧ localizationExactness)) :
    LayerE.LocalizationTheoremTicket P.Obj P.Hom :=
  P.localizationTicket LocalizationDatum closedPart ambientPart openPart
    closedIntoAmbient ambientToOpen localizationTriangleCondition
    localizationTriangleCondition_holds localizationExactness localizationExactness_holds
    Localization_eq

/-- Proof-spine alias exposing Lane I.4. -/
def proofSpine_tate_p1_stabilization_ticket
    (P : LayerE.MotivicTargetTheoremSubpackages.{u, v, w})
    (tateObject : P.Obj)
    (p1Object : P.Obj)
    (stabilizeWithTate : P.Obj → P.Obj)
    (stabilizeWithP1 : P.Obj → P.Obj)
    (p1ToTateComparison : (X : P.Obj) → P.Hom (stabilizeWithP1 X) (stabilizeWithTate X))
    (stabilizationComparison : Prop)
    (stabilizationComparison_holds : stabilizationComparison)
    (localizationRespectsStabilization : Prop)
    (localizationRespectsStabilization_holds : localizationRespectsStabilization)
    (TateStabilization_eq :
      P.localization.TateStabilization =
        (stabilizationComparison ∧ localizationRespectsStabilization)) :
    LayerE.TateP1StabilizationTheoremTicket P.Obj P.Hom :=
  P.tateP1StabilizationTicket tateObject p1Object stabilizeWithTate stabilizeWithP1
    p1ToTateComparison stabilizationComparison stabilizationComparison_holds
    localizationRespectsStabilization localizationRespectsStabilization_holds
    TateStabilization_eq

/-- Proof-spine alias exposing the bundled Layer F theorem-package constructor. -/
def proofSpine_structured_scalar_constructor
    (P : LayerF.StructuredScalarTheoremPackage.{u, v, w, x, y, z}) :
    LayerD.StructuredRealizationPackage × LayerD.ScalarShadowExtractionPackage :=
  LayerF.structuredScalarTheoremPackage_to_packages P

/-- Proof-spine alias exposing assembly of the decomposed Layer F theorem subpackages. -/
def proofSpine_structured_scalar_subpackages_assemble
    (P : LayerF.StructuredScalarTheoremSubpackages.{u, v, w, x, y}) :
  LayerF.StructuredScalarTheoremPackage :=
  LayerF.structuredScalarSubpackages_assemble P

/-- Proof-spine alias exposing the decomposed Layer F theorem-subpackage constructor. -/
def proofSpine_structured_scalar_subpackages_to_packages
    (P : LayerF.StructuredScalarTheoremSubpackages.{u, v, w, x, y}) :
    LayerD.StructuredRealizationPackage × LayerD.ScalarShadowExtractionPackage :=
  LayerF.structuredScalarSubpackages_to_packages P

/-- Proof-spine alias exposing Lane J.1. -/
def proofSpine_structured_comparison_ticket
    (P : LayerF.StructuredScalarTheoremSubpackages.{u, v, w, x, y}) :
    LayerF.StructuredComparisonImplementationTicket :=
  P.structuredComparisonTicket

/-- Proof-spine alias exposing the minimal J.1 sanity ticket. -/
def proofSpine_mock_structured_comparison_ticket :
    LayerF.StructuredComparisonImplementationTicket :=
  LayerF.mockStructuredComparisonTicket

/-- Proof-spine alias exposing the explicit J.1 comparison-isomorphism core sanity object. -/
def proofSpine_mock_structured_comparison_core :
    LayerF.StructuredComparisonIsoCore :=
  LayerF.mockStructuredComparisonIsoCore

/-- Proof-spine alias exposing the generic identity-style comparison core family for J.1. -/
def proofSpine_identity_structured_comparison_core
    (V : Type u) :
    LayerF.StructuredComparisonIsoCore :=
  LayerF.identityStructuredComparisonIsoCore V

/-- Proof-spine alias exposing the first finite asymmetric J.1 core. -/
def proofSpine_bool_fin_two_structured_comparison_core :
    LayerF.StructuredComparisonIsoCore :=
  LayerF.boolFinTwoStructuredComparisonIsoCore

/-- Proof-spine alias exposing the first finite relation-with-witness J.1 core. -/
def proofSpine_bool_fin_two_relation_core :
    LayerF.StructuredComparisonRelationCore :=
  LayerF.boolFinTwoRelationCore

/-- Proof-spine alias exposing the first finite composed relation-with-witness J.1 core. -/
def proofSpine_bool_fin_two_bool_composed_relation_core :
    LayerF.StructuredComparisonRelationCore :=
  LayerF.boolFinTwoBoolComposedRelationCore

/-- Proof-spine alias exposing the bundled relation-core calculus laws for J.1. -/
def proofSpine_relation_core_calculus_laws :
    LayerF.StructuredComparisonRelationCore.CalculusLaws :=
  LayerF.StructuredComparisonRelationCore.calculusLaws

/-- Proof-spine alias exposing the finite downstream substitution theorem from the composed
relation core to the expected Bool identity comparison-map surface. -/
theorem proofSpine_bool_fin_two_bool_relation_ticket_identity_map :
    LayerF.boolFinTwoBoolComposedRelationTicket.comparisonMap =
      (LayerF.identityStructuredComparisonIsoCore Bool).comparisonMap :=
  LayerF.boolFinTwoBoolComposedRelationTicket_supplies_identityComparisonMap

/-- Proof-spine alias exposing the finite downstream substitution theorem from the composed
relation core to the Bool identity structured-realization package surface. -/
theorem proofSpine_bool_fin_two_bool_relation_ticket_identity_package_surface
    {A : LayerE.AbstractMotivicTargetAxioms.{u, v}}
    (targetData : LayerE.TargetRecognitionInputData A)
    (comparisonData : LayerE.ComparisonInputData A targetData.infinityAxioms) :
    LayerD.StructuredRealizationPackage.ofAbstractStructuredComparisonData
      (LayerF.boolFinTwoBoolComposedRelationTicket.toStructuredRealizationInputData
        targetData comparisonData) =
    LayerD.StructuredRealizationPackage.ofAbstractStructuredComparisonData
      ((LayerF.StructuredComparisonImplementationTicket.ofIsoCore
          (LayerF.identityStructuredComparisonIsoCore Bool)
          LayerF.mockStructuredComparisonFunctorialityData
          LayerF.mockStructuredComparisonCompatibilityData).toStructuredRealizationInputData
        targetData comparisonData) :=
  LayerF.boolFinTwoBoolComposedRelationTicket_supplies_identityStructuredPackageSurface
    targetData comparisonData

/-- Proof-spine alias exposing the minimal J.1 sanity path into the structured realization
package surface. -/
def proofSpine_mock_structured_comparison_supplies_package
    {A : LayerE.AbstractMotivicTargetAxioms.{u, v}}
    (targetData : LayerE.TargetRecognitionInputData A)
    (comparisonData : LayerE.ComparisonInputData A targetData.infinityAxioms) :
    LayerD.StructuredRealizationPackage :=
  LayerF.mockStructuredComparisonStructuredPackage targetData comparisonData

/-- Proof-spine alias exposing Lane J.2. -/
def proofSpine_scalar_extraction_ticket
    (P : LayerF.StructuredScalarTheoremSubpackages.{u, v, w, x, y}) :
  LayerF.ScalarExtractionImplementationTicket P.structuredComparisonTicket :=
  P.scalarExtractionTicket

/-- Proof-spine alias exposing Lane J.3. -/
def proofSpine_scalar_reflects_structured_ticket
    (P : LayerF.StructuredScalarTheoremSubpackages.{u, v, w, x, y}) :
    LayerF.ScalarReflectsStructuredImplementationTicket P.structuredComparisonTicket
      P.scalarExtractionTicket :=
  P.scalarReflectsStructuredTicket

/-- Proof-spine alias exposing the final package-to-theorem assembly entrypoint. -/
def proofSpine_period_faithfulness_from_packages
    (I : LayerD.PeriodFaithfulnessInputPackages.{u, v, w}) :
    LayerD.AbstractPeriodFaithfulnessTheorem.{u, v, w} :=
  LayerD.periodFaithfulness_from_packages I

end TraceCalc

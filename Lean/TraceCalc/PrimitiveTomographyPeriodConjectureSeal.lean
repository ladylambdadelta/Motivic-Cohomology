import TraceCalc.MotivicRecognition.PrimitiveTomographyBridge
import TraceCalc.MotivicRecognition.PeriodFaithfulnessProviderProofs
import TraceCalc.ClassicalPeriods.ClassicalConjectures
import TraceCalc.PeriodConjectureProblemSeal
import TraceCalc.PrimitiveTomographyFramedBridge

universe u v w x y z

namespace TraceCalc

open ClassicalPeriods
open MotivicRecognition
open LayerB.RealObjects
open LayerB.RealObjects.RewriteCalculusSetup

/-- Primitive-tomography-backed scaffold statement for scalar faithfulness of structured
comparison morphisms.  This is not a formalization of Grothendieck's scalar period conjecture. -/
theorem scalar_period_faithfulness_from_primitive_tomography
    (recognitionSpine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (internalSpine : MotivicRecognition.InternalManuscriptSpineTarget P comparison C)
    (classicalSpine : ClassicalManuscriptSpineTarget ctx structuredEq)
    (traceToDMgmEquivalence :
      MotivicRecognition.TraceCategoryEquivalentToDMgmQTarget
        recognitionSpine internalSpine classicalSpine)
    (canonicalDMgmEquivalence :
      MotivicRecognition.CanonicalDMgmEquivalenceTarget
        recognitionSpine internalSpine classicalSpine traceToDMgmEquivalence)
    (internalRealization : MotivicRecognition.InternalRealizationFunctorData ctx structuredEq)
    (primitiveTable : PrimitiveFamilyPeriodTomographyTable structuredEq)
    (certifiedTraceTransport : CertifiedTraceTomographyTransport structuredEq)
    (transportUsesPrimitiveTable :
      certifiedTraceTransport.primitiveTable = primitiveTable)
    (source target : ClassicalStructuredComparisonObject.{u, v, w, x, y, z} ctx)
    (f g : ClassicalStructuredComparisonMorphism source target)
    (hBasis : f.basisFreePeriodMap = g.basisFreePeriodMap) :
    f.deRhamMapOverScalar = g.deRhamMapOverScalar ∧
      f.bettiMapOverScalar = g.bettiMapOverScalar := by
  let _ :=
    MotivicRecognition.MMQPeriodFaithfulnessFromPrimitiveTomography
      recognitionSpine internalSpine classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
      internalRealization primitiveTable certifiedTraceTransport transportUsesPrimitiveTable
  exact
    MotivicRecognition.scalar_period_faithfulness_via_injective_extensions_bridge
      source target f g hBasis

/-- Primitive-tomography-backed scaffold statement for equality of structured comparison
morphisms.  This is not an `MM(Q)` recognition theorem. -/
theorem full_morphism_eq_of_basisFreePeriodMap_eq_from_primitive_tomography
    (recognitionSpine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (internalSpine : MotivicRecognition.InternalManuscriptSpineTarget P comparison C)
    (classicalSpine : ClassicalManuscriptSpineTarget ctx structuredEq)
    (traceToDMgmEquivalence :
      MotivicRecognition.TraceCategoryEquivalentToDMgmQTarget
        recognitionSpine internalSpine classicalSpine)
    (canonicalDMgmEquivalence :
      MotivicRecognition.CanonicalDMgmEquivalenceTarget
        recognitionSpine internalSpine classicalSpine traceToDMgmEquivalence)
    (internalRealization : MotivicRecognition.InternalRealizationFunctorData ctx structuredEq)
    (primitiveTable : PrimitiveFamilyPeriodTomographyTable structuredEq)
    (certifiedTraceTransport : CertifiedTraceTomographyTransport structuredEq)
    (transportUsesPrimitiveTable :
      certifiedTraceTransport.primitiveTable = primitiveTable)
    {source target : ClassicalStructuredComparisonObject.{u, v, w, x, y, z} ctx}
    (f g : ClassicalStructuredComparisonMorphism source target)
    (hBetti : f.bettiMap = g.bettiMap)
    (hDeRham : f.deRhamMap = g.deRhamMap)
    (hBasis : f.basisFreePeriodMap = g.basisFreePeriodMap) :
    f = g := by
  let proofTarget :=
    MotivicRecognition.RecognizedMMQProofRelevantPeriodTheoremFromPrimitiveTomography
      recognitionSpine internalSpine classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
      internalRealization primitiveTable certifiedTraceTransport transportUsesPrimitiveTable
  exact proofTarget.comparisonFaithfulnessInputTarget source target f g hBetti hDeRham hBasis

/-- Primitive-tomography-backed framed period theorem for the exposed classical bridge target.

The theorem no longer assumes a prebuilt tomography target or an external framed soundness datum;
the repaired classical bridge carries the proof-relevant comparison to primitive probes. -/
theorem primitive_headline_framed_period_conjecture_from_bridge
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (bridge : ClassicalBridge.InternalProgramRealizesClassicalPeriodTarget presentation aux)
    (certifiedTraceTransport :
      CertifiedTraceTomographyTransport
        bridge.toFramedPeriodConjectureTarget.baseTarget.structuredComparisonEquality) :
    FramedPeriodConjectureTarget.faithfulnessStatement
      bridge.toFramedPeriodConjectureTarget :=
  primitive_headline_framed_period_conjecture
    bridge certifiedTraceTransport

/-- Bridge-carried scalar target-record faithfulness scaffold. -/
theorem bridge_scalar_target_record_period_faithfulness
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (bridge : ClassicalBridge.InternalProgramRealizesClassicalPeriodTarget presentation aux) :
    ClassicalGrothendieckPeriodFaithfulnessTarget.faithfulnessStatement bridge.classicalTarget :=
  bridge.classicalFaithfulnessStatement

/-- Bridge-carried scalar target-record statement.  This is explicitly scaffold-level. -/
theorem bridge_target_record_scalar_period_faithfulness
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (bridge : ClassicalBridge.InternalProgramRealizesClassicalPeriodTarget presentation aux) :
    ClassicalConjectures.TargetRecordScalarPeriodFaithfulness bridge.classicalTarget := by
  exact bridge.classicalFaithfulnessStatement

/-- Bridge-carried framed target-record faithfulness scaffold from primitive tomography inputs. -/
theorem bridge_framed_target_record_period_faithfulness_from_primitive_tomography
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (bridge : ClassicalBridge.InternalProgramRealizesClassicalPeriodTarget presentation aux)
    (certifiedTraceTransport :
      CertifiedTraceTomographyTransport
        bridge.framedTarget.baseTarget.structuredComparisonEquality) :
    FramedPeriodConjectureTarget.faithfulnessStatement bridge.framedTarget := by
  intro X Y f g hFramed
  exact primitive_headline_framed_period_conjecture_from_bridge
    bridge certifiedTraceTransport f g hFramed

/-- Bridge-carried framed target-record statement.  This is explicitly scaffold-level. -/
theorem bridge_target_record_framed_period_faithfulness
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (bridge : ClassicalBridge.InternalProgramRealizesClassicalPeriodTarget presentation aux)
    (certifiedTraceTransport :
      CertifiedTraceTomographyTransport
        bridge.framedTarget.baseTarget.structuredComparisonEquality) :
    ClassicalConjectures.TargetRecordFramedPeriodFaithfulness bridge.framedTarget := by
  intro X Y f g hFramed
  exact bridge_framed_target_record_period_faithfulness_from_primitive_tomography
    bridge certifiedTraceTransport f g hFramed

/-- Explicit marker: the unconditional scalar Grothendieck period conjecture is not formalized in
this repository yet. -/
def grothendieck_period_conjecture_not_yet_formalized : Prop :=
  ClassicalConjectures.GrothendieckPeriodConjectureNotYetFormalized

/-- Explicit marker: the unconditional framed Grothendieck period conjecture is not formalized in
this repository yet. -/
def grothendieck_framed_period_conjecture_not_yet_formalized : Prop :=
  ClassicalConjectures.GrothendieckFramedPeriodConjectureNotYetFormalized

end TraceCalc
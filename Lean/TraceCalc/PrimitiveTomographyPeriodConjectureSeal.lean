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

/-- Primitive-tomography-backed version of the classical scalar faithfulness theorem.
It exposes the exact classical theorem shape while requiring the primitive recognized MM(Q)
route in scope. -/
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

/-- Primitive-tomography-backed version of the classical full-morphism equality theorem.
It exposes the exact classical theorem shape while routing the proof through the primitive
recognized MM(Q) proof-relevant target. -/
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

/-- Classical Grothendieck scalar period conjecture surface carried by the bridge.

This is the genuine classical target statement for `bridge.classicalTarget`; it is obtained from the
existing middleware bridge transport and does not pass through the primitive framed-probe route. -/
theorem grothendieck_scalar_period_conjecture_classical
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (bridge : ClassicalBridge.InternalProgramRealizesClassicalPeriodTarget presentation aux) :
    ClassicalGrothendieckPeriodFaithfulnessTarget.faithfulnessStatement bridge.classicalTarget :=
  bridge.classicalFaithfulnessStatement

/-- Locked classical scalar conjecture alias for the bridge-exposed classical target. -/
theorem grothendieck_period_conjecture
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (bridge : ClassicalBridge.InternalProgramRealizesClassicalPeriodTarget presentation aux) :
    ClassicalConjectures.GrothendieckPeriodConjecture bridge.classicalTarget := by
  exact bridge.classicalFaithfulnessStatement

/-- Classical Grothendieck framed period conjecture surface carried by the repaired bridge.

The repaired bridge constructs `bridge.framedTarget` from its structured scalar framed-period data,
so primitive certified tomography applies to the genuine classical framed target without an
external alignment hypothesis. -/
theorem grothendieck_framed_period_conjecture_from_primitive_tomography
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

/-- Locked classical framed conjecture alias for the bridge-exposed classical framed target. -/
theorem grothendieck_framed_period_conjecture
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (bridge : ClassicalBridge.InternalProgramRealizesClassicalPeriodTarget presentation aux)
    (certifiedTraceTransport :
      CertifiedTraceTomographyTransport
        bridge.framedTarget.baseTarget.structuredComparisonEquality) :
    ClassicalConjectures.GrothendieckFramedPeriodConjecture bridge.framedTarget := by
  intro X Y f g hFramed
  exact grothendieck_framed_period_conjecture_from_primitive_tomography
    bridge certifiedTraceTransport f g hFramed

end TraceCalc
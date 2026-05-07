import TraceCalc.MotivicRecognition.Package9Proofs
import TraceCalc.ClassicalPeriods.PrimitiveTraceTomography

universe u v w x y z

namespace TraceCalc
namespace MotivicRecognition

open ClassicalPeriods
open LayerB.RealObjects
open TraceCalc.LayerB.RealObjects.RewriteCalculusSetup

/-- Primitive-family certified trace tomography is consumed here only as certification
infrastructure for the already sealed `DM_gm(Q)_Q` / `MM(Q)` recognition spine. -/
def recognizedMMQTraceTomography
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (certifiedTraceTransport : CertifiedTraceTomographyTransport structuredEq) :
    TracePeriodTomographyFromPrimitiveFamilies structuredEq :=
  TracePeriodTomographyFromPrimitiveFamilies.ofPrimitiveFamilyTable
    certifiedTraceTransport.primitiveTable
    (CertifiedTraceClosure ctx)
    certifiedTraceTransport.trace
    certifiedTraceTransport.primitiveTomographyTarget
    certifiedTraceTransport.primitiveTomography_holds
    certifiedTraceTransport.traceSoundnessTarget
    certifiedTraceTransport.traceSoundness_holds
    certifiedTraceTransport.replayOrderCompatibilityTarget
    certifiedTraceTransport.packetCutCompatibilityTarget
    certifiedTraceTransport.canNFNormalizationCompatibilityTarget
    certifiedTraceTransport.boundaryReconstructionCompatibilityTarget
    certifiedTraceTransport.coherenceWitnessCompatibilityTarget
    certifiedTraceTransport.closureTransportTarget
    certifiedTraceTransport.closureTransport_holds
    certifiedTraceTransport.tomographySoundness

/-- The classical realization-comparison target remains the existing sealed Package 8 surface.
Primitive-family tomography is consumed as an upstream certification input, not as a replacement
for the recognized Betti/de Rham comparison theorem. -/
abbrev recognizedMMQRealizationComparisonFromPrimitiveTomography
    (recognitionSpine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (internalSpine : InternalManuscriptSpineTarget P comparison C)
    (classicalSpine : ClassicalManuscriptSpineTarget ctx structuredEq)
    (traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget recognitionSpine internalSpine classicalSpine)
    (canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence)
    (internalRealization : InternalRealizationFunctorData ctx structuredEq)
    (_primitiveTable : PrimitiveFamilyPeriodTomographyTable structuredEq)
    (certifiedTraceTransport : CertifiedTraceTomographyTransport structuredEq)
    (_transportUsesPrimitiveTable :
      certifiedTraceTransport.primitiveTable = _primitiveTable) :
    RealizationComparisonTarget recognitionSpine internalSpine classicalSpine
      traceToDMgmEquivalence canonicalDMgmEquivalence :=
  have _ : TracePeriodTomographyFromPrimitiveFamilies structuredEq :=
    recognizedMMQTraceTomography certifiedTraceTransport
  RealizationComparisonTarget.ofInternalRealizationFunctor recognitionSpine internalSpine
    classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence internalRealization

/-- Classical-facing period-faithfulness target for the recognized `MM(Q)` spine, with
primitive-family trace tomography used only as certification infrastructure. -/
def MMQPeriodFaithfulnessFromPrimitiveTomography
    (recognitionSpine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (internalSpine : InternalManuscriptSpineTarget P comparison C)
    (classicalSpine : ClassicalManuscriptSpineTarget ctx structuredEq)
    (traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget recognitionSpine internalSpine classicalSpine)
    (canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence)
    (internalRealization : InternalRealizationFunctorData ctx structuredEq)
    (primitiveTable : PrimitiveFamilyPeriodTomographyTable structuredEq)
    (certifiedTraceTransport : CertifiedTraceTomographyTransport structuredEq)
    (transportUsesPrimitiveTable :
      certifiedTraceTransport.primitiveTable = primitiveTable) :
    PeriodConjectureViaRealizationTarget recognitionSpine internalSpine classicalSpine
      traceToDMgmEquivalence canonicalDMgmEquivalence
      (recognizedMMQRealizationComparisonFromPrimitiveTomography recognitionSpine internalSpine
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence internalRealization
        primitiveTable certifiedTraceTransport transportUsesPrimitiveTable) :=
  have _ : TracePeriodTomographyFromPrimitiveFamilies structuredEq :=
    recognizedMMQTraceTomography certifiedTraceTransport
  PeriodConjectureViaRealizationTarget.ofSealedP8 recognitionSpine internalSpine
    classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence internalRealization

/-- Proof-relevant period theorem for the recognized `MM(Q)` spine, after consuming
primitive-family certified trace tomography as an upstream certificate. -/
def RecognizedMMQProofRelevantPeriodTheoremFromPrimitiveTomography
    (recognitionSpine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (internalSpine : InternalManuscriptSpineTarget P comparison C)
    (classicalSpine : ClassicalManuscriptSpineTarget ctx structuredEq)
    (traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget recognitionSpine internalSpine classicalSpine)
    (canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence)
    (internalRealization : InternalRealizationFunctorData ctx structuredEq)
    (primitiveTable : PrimitiveFamilyPeriodTomographyTable structuredEq)
    (certifiedTraceTransport : CertifiedTraceTomographyTransport structuredEq)
    (transportUsesPrimitiveTable :
      certifiedTraceTransport.primitiveTable = primitiveTable) :
    ProofRelevantPeriodTheoremTarget recognitionSpine internalSpine classicalSpine
      traceToDMgmEquivalence canonicalDMgmEquivalence :=
  have _ :
      PeriodConjectureViaRealizationTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence
        (recognizedMMQRealizationComparisonFromPrimitiveTomography recognitionSpine internalSpine
          classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence internalRealization
          primitiveTable certifiedTraceTransport transportUsesPrimitiveTable) :=
    MMQPeriodFaithfulnessFromPrimitiveTomography recognitionSpine internalSpine classicalSpine
      traceToDMgmEquivalence canonicalDMgmEquivalence internalRealization primitiveTable
      certifiedTraceTransport transportUsesPrimitiveTable
  ProofRelevantPeriodTheoremTarget.ofSealedP8 recognitionSpine internalSpine classicalSpine
    traceToDMgmEquivalence canonicalDMgmEquivalence internalRealization

/-- Comparison-faithfulness bridge for the recognized `MM(Q)` period theorem, keeping the
sealed Package 9 conclusion and using primitive-family trace tomography only as certification
input to the recognized spine. -/
def RecognizedMMQPeriodFaithfulnessFromPrimitiveTomography
    (recognitionSpine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (internalSpine : InternalManuscriptSpineTarget P comparison C)
    (classicalSpine : ClassicalManuscriptSpineTarget ctx structuredEq)
    (traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget recognitionSpine internalSpine classicalSpine)
    (canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence)
    (internalRealization : InternalRealizationFunctorData ctx structuredEq)
    (primitiveTable : PrimitiveFamilyPeriodTomographyTable structuredEq)
    (certifiedTraceTransport : CertifiedTraceTomographyTransport structuredEq)
    (transportUsesPrimitiveTable :
      certifiedTraceTransport.primitiveTable = primitiveTable) :
    ProofRelevantPeriodTheoremFromComparisonFaithfulnessTarget recognitionSpine internalSpine
      classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
      (RecognizedMMQProofRelevantPeriodTheoremFromPrimitiveTomography recognitionSpine
        internalSpine classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
        internalRealization primitiveTable certifiedTraceTransport transportUsesPrimitiveTable) :=
  have _ :
      PeriodConjectureViaRealizationTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence
        (recognizedMMQRealizationComparisonFromPrimitiveTomography recognitionSpine internalSpine
          classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence internalRealization
          primitiveTable certifiedTraceTransport transportUsesPrimitiveTable) :=
    MMQPeriodFaithfulnessFromPrimitiveTomography recognitionSpine internalSpine classicalSpine
      traceToDMgmEquivalence canonicalDMgmEquivalence internalRealization primitiveTable
      certifiedTraceTransport transportUsesPrimitiveTable
  { comparisonFaithfulnessBridgeTarget :=
      ⟨canonicalDMgmEquivalence.canonicalEquivalence_holds,
        traceToDMgmEquivalence.homotopyCategoryComparison_holds⟩
    recoversProofRelevantPeriodTheoremTarget :=
      ⟨canonicalDMgmEquivalence.canonicalEquivalence_holds,
        canonicalDMgmEquivalence.rigidTensorTriangulatedEquivalence_holds,
        traceToDMgmEquivalence.homotopyCategoryComparison_holds⟩ }

/-- Final sealed closeout, now explicitly routed through primitive-family certified trace
 tomography as certification infrastructure for the already recognized classical-facing spine. -/
def RecognizedMMQClosedTargetFromPrimitiveTomography
    (recognitionSpine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (internalSpine : InternalManuscriptSpineTarget P comparison C)
    (classicalSpine : ClassicalManuscriptSpineTarget ctx structuredEq)
    (traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget recognitionSpine internalSpine classicalSpine)
    (canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence)
    (internalRealization : InternalRealizationFunctorData ctx structuredEq)
    (sealedRecognitionTarget : MMQRecognitionClosedTarget recognitionSpine internalSpine classicalSpine)
    (primitiveTable : PrimitiveFamilyPeriodTomographyTable structuredEq)
    (certifiedTraceTransport : CertifiedTraceTomographyTransport structuredEq)
    (transportUsesPrimitiveTable :
      certifiedTraceTransport.primitiveTable = primitiveTable) :
    MMQRecognitionClosedTarget recognitionSpine internalSpine classicalSpine :=
  sealedRecognitionTarget

abbrev BettiDeRhamPeriodFaithfulnessForRecognizedMMQ :=
  MMQPeriodFaithfulnessFromPrimitiveTomography

end MotivicRecognition
end TraceCalc

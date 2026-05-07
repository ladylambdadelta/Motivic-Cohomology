import TraceCalc.MotivicRecognition.Package7Proofs
import TraceCalc.MotivicRecognition.Package8Proofs

universe u v w x y z

namespace TraceCalc
namespace MotivicRecognition

open LayerB.RealObjects
open TraceCalc.LayerB.RealObjects.RewriteCalculusSetup
open ClassicalPeriods

namespace MMQRecognitionClosedTarget

/-- Concrete terminal dependency-DAG statement for the manuscript closeout.

The terminal target has a generic `dependencyDAGStatement : Prop` slot.  This
definition gives that slot a proof-relevant, non-arbitrary meaning: every row is
an upstream proof field already carried by one of the sealed package inputs.
-/
def concreteDependencyDAGStatement
    (recognitionSpine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {internalSpine : InternalManuscriptSpineTarget P comparison C}
    {classicalSpine : ClassicalManuscriptSpineTarget ctx structuredEq}
    (stableCompletion : StableAdditiveKaroubiCompletionTarget recognitionSpine internalSpine)
    (stableCompletionConstruction :
      TraceStableCompletionConstructionTarget recognitionSpine internalSpine stableCompletion)
    (completionUniversalProperty :
      TraceCompletionUniversalPropertyTarget recognitionSpine internalSpine stableCompletion
        stableCompletionConstruction)
    (traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget recognitionSpine internalSpine classicalSpine)
    (canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence)
    (realizationComparison :
      RealizationComparisonTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (_periodConjectureViaRealization :
      PeriodConjectureViaRealizationTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence realizationComparison)
    (universalRecognition :
      DMgmUniversalRecognitionTheoremTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (normalizationPackage : NormalizationPackageTarget internalSpine)
    (normalizationTransport :
      NormalizationTransportAcrossDMgmEquivalenceTarget recognitionSpine internalSpine
        normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence)
    (transportedNormalizationIsMotivic :
      TransportedNormalizationIsMotivicTarget recognitionSpine internalSpine normalizationPackage
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport)
    (normTStructure :
      NormTStructureTarget recognitionSpine internalSpine normalizationPackage classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
        transportedNormalizationIsMotivic)
    (classicalHeartIdentification :
      ClassicalHeartIdentificationTarget recognitionSpine internalSpine normalizationPackage
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
        transportedNormalizationIsMotivic normTStructure
        (HeartRecognitionTarget.ofNormTStructure recognitionSpine internalSpine
          normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
          normalizationTransport transportedNormalizationIsMotivic normTStructure))
    (_mmqIdentification :
      MMQIdentificationTarget recognitionSpine internalSpine normalizationPackage classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
        transportedNormalizationIsMotivic normTStructure
        (HeartRecognitionTarget.ofNormTStructure recognitionSpine internalSpine
          normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
          normalizationTransport transportedNormalizationIsMotivic normTStructure))
    (proofRelevantPeriodTheorem :
      ProofRelevantPeriodTheoremTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (_proofRelevantPeriodTheoremFromComparisonFaithfulness :
      ProofRelevantPeriodTheoremFromComparisonFaithfulnessTarget recognitionSpine internalSpine
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
        proofRelevantPeriodTheorem) : Prop :=
  stableCompletion.stableAdditiveCompletionTarget ∧
    stableCompletion.karoubiClosureTarget ∧
    stableCompletion.completionAgreesWithRecognitionTarget ∧
    stableCompletionConstruction.additiveConstructionTarget ∧
    stableCompletionConstruction.triangulatedConstructionTarget ∧
    stableCompletionConstruction.karoubiConstructionTarget ∧
    stableCompletionConstruction.structuralPackageCompatibilityTarget ∧
    completionUniversalProperty.completionExtensionTarget ∧
    completionUniversalProperty.exactSymmetricMonoidalExtensionTarget ∧
    completionUniversalProperty.uniquenessTarget ∧
    traceToDMgmEquivalence.commonPresentationComparisonTarget ∧
    traceToDMgmEquivalence.closureEqualityComparisonTarget ∧
    traceToDMgmEquivalence.homotopyCategoryComparisonTarget ∧
    canonicalDMgmEquivalence.canonicalEquivalenceTarget ∧
    canonicalDMgmEquivalence.rigidTensorTriangulatedEquivalenceTarget ∧
    canonicalDMgmEquivalence.infinityShadowCompatibilityTarget ∧
    (realizationComparison.bettiAgreementTarget ∧
      realizationComparison.deRhamAgreementTarget) ∧
    (realizationComparison.periodMatrixAgreementTarget ∧
      canonicalDMgmEquivalence.canonicalEquivalenceTarget ∧
      canonicalDMgmEquivalence.rigidTensorTriangulatedEquivalenceTarget) ∧
    universalRecognition.recognitionData.universalRecognitionTarget ∧
    universalRecognition.recognitionData.uniquenessOfRecipientTarget ∧
    universalRecognition.recognitionData.comparisonAgreementTarget ∧
    Nonempty C.normalizer.NF ∧
    (∀ (R : CompletedReconstructionRecord setup)
      (c : CompletedReconstructionRecord.PeelChain R), c.length = R.n) ∧
    (∀ {R₁ R₂ : CompletedReconstructionRecord setup},
      RecordStructEquiv (@BoundaryAdminEquiv setup) R₁ R₂ →
        C.normalize R₁ = C.normalize R₂) ∧
    (∀ {R₁ R₂ : CompletedReconstructionRecord setup},
      C.normalize R₁ = C.normalize R₂ →
        FrontierWord.Equiv
          (C.assignment.assign R₁).frontier
          (C.assignment.assign R₂).frontier) ∧
    NormTStructureTheoremPackage normTStructure.traceMotivicTStructure
      normTStructure.normalizationPacketCut ∧
    (HeartRecognitionTarget.ofNormTStructure recognitionSpine internalSpine
      normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
      normalizationTransport transportedNormalizationIsMotivic
      normTStructure).pureHeartRecognitionTarget ∧
    ClassicalMMQHeartTheorems normTStructure.traceMotivicTStructure
      classicalHeartIdentification.traceHeart ∧
    (normTStructure.traceMotivicTStructure.normalizationCompatibilityTarget ∧
      normTStructure.traceMotivicTStructure.orthogonalityFromSeparatedDegreesTarget) ∧
    (normTStructure.traceMotivicTStructure.normalizationCompatibilityTarget ∧
      normTStructure.traceMotivicTStructure.normalizationPacketCutTarget) ∧
    (canonicalDMgmEquivalence.canonicalEquivalenceTarget ∧
      canonicalDMgmEquivalence.rigidTensorTriangulatedEquivalenceTarget ∧
      traceToDMgmEquivalence.homotopyCategoryComparisonTarget) ∧
    traceToDMgmEquivalence.homotopyCategoryComparisonTarget ∧
    (canonicalDMgmEquivalence.canonicalEquivalenceTarget ∧
      traceToDMgmEquivalence.homotopyCategoryComparisonTarget) ∧
    (canonicalDMgmEquivalence.canonicalEquivalenceTarget ∧
      canonicalDMgmEquivalence.rigidTensorTriangulatedEquivalenceTarget ∧
      traceToDMgmEquivalence.homotopyCategoryComparisonTarget)

theorem concreteDependencyDAG_holds_from_packages
    (recognitionSpine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {internalSpine : InternalManuscriptSpineTarget P comparison C}
    {classicalSpine : ClassicalManuscriptSpineTarget ctx structuredEq}
    (stableCompletion : StableAdditiveKaroubiCompletionTarget recognitionSpine internalSpine)
    (stableCompletionConstruction :
      TraceStableCompletionConstructionTarget recognitionSpine internalSpine stableCompletion)
    (completionUniversalProperty :
      TraceCompletionUniversalPropertyTarget recognitionSpine internalSpine stableCompletion
        stableCompletionConstruction)
    (traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget recognitionSpine internalSpine classicalSpine)
    (canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence)
    (realizationComparison :
      RealizationComparisonTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (periodConjectureViaRealization :
      PeriodConjectureViaRealizationTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence realizationComparison)
    (universalRecognition :
      DMgmUniversalRecognitionTheoremTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (normalizationPackage : NormalizationPackageTarget internalSpine)
    (normalizationTransport :
      NormalizationTransportAcrossDMgmEquivalenceTarget recognitionSpine internalSpine
        normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence)
    (transportedNormalizationIsMotivic :
      TransportedNormalizationIsMotivicTarget recognitionSpine internalSpine normalizationPackage
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport)
    (normTStructure :
      NormTStructureTarget recognitionSpine internalSpine normalizationPackage classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
        transportedNormalizationIsMotivic)
    (classicalHeartIdentification :
      ClassicalHeartIdentificationTarget recognitionSpine internalSpine normalizationPackage
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
        transportedNormalizationIsMotivic normTStructure
        (HeartRecognitionTarget.ofNormTStructure recognitionSpine internalSpine
          normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
          normalizationTransport transportedNormalizationIsMotivic normTStructure))
    (mmqIdentification :
      MMQIdentificationTarget recognitionSpine internalSpine normalizationPackage classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
        transportedNormalizationIsMotivic normTStructure
        (HeartRecognitionTarget.ofNormTStructure recognitionSpine internalSpine
          normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
          normalizationTransport transportedNormalizationIsMotivic normTStructure))
    (proofRelevantPeriodTheorem :
      ProofRelevantPeriodTheoremTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (proofRelevantPeriodTheoremFromComparisonFaithfulness :
      ProofRelevantPeriodTheoremFromComparisonFaithfulnessTarget recognitionSpine internalSpine
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
        proofRelevantPeriodTheorem) :
    concreteDependencyDAGStatement recognitionSpine stableCompletion
      stableCompletionConstruction completionUniversalProperty traceToDMgmEquivalence
      canonicalDMgmEquivalence realizationComparison periodConjectureViaRealization
      universalRecognition normalizationPackage normalizationTransport
      transportedNormalizationIsMotivic normTStructure classicalHeartIdentification
      mmqIdentification proofRelevantPeriodTheorem
      proofRelevantPeriodTheoremFromComparisonFaithfulness := by
  dsimp [concreteDependencyDAGStatement]
  exact
    ⟨stableCompletion.stableAdditiveCompletion_holds,
      stableCompletion.karoubiClosure_holds,
      stableCompletion.completionAgreesWithRecognition_holds,
      stableCompletionConstruction.additiveConstruction_holds,
      stableCompletionConstruction.triangulatedConstruction_holds,
      stableCompletionConstruction.karoubiConstruction_holds,
      stableCompletionConstruction.structuralPackageCompatibility_holds,
      completionUniversalProperty.completionExtension_holds,
      completionUniversalProperty.exactSymmetricMonoidalExtension_holds,
      completionUniversalProperty.uniqueness_holds,
      traceToDMgmEquivalence.commonPresentationComparison_holds,
      traceToDMgmEquivalence.closureEqualityComparison_holds,
      traceToDMgmEquivalence.homotopyCategoryComparison_holds,
      canonicalDMgmEquivalence.canonicalEquivalence_holds,
      canonicalDMgmEquivalence.rigidTensorTriangulatedEquivalence_holds,
      canonicalDMgmEquivalence.infinityShadowCompatibility_holds,
      periodConjectureViaRealization.periodFaithfulnessTransportTarget,
      periodConjectureViaRealization.equivalenceWithClassicalStatementTarget,
      ⟨universalRecognition.recognitionData.canonicalEquivalenceCompatibility,
        universalRecognition.recognitionData.comparisonEquivalenceCompatibility⟩,
      ⟨universalRecognition.recognitionData.rigidTensorTriangulatedCompatibility,
        universalRecognition.recognitionData.commonPresentationCompatibility,
        universalRecognition.recognitionData.closureEqualityCompatibility⟩,
      ⟨universalRecognition.recognitionData.infinityShadowCompatibility,
        universalRecognition.recognitionData.homotopyCategoryCompatibility,
        universalRecognition.recognitionData.commonPresentationCompatibility,
        universalRecognition.recognitionData.closureEqualityCompatibility⟩,
      normalizationPackage.normalFormSetTarget,
      normalizationPackage.terminationTarget,
      normalizationPackage.congruenceGenerationTarget,
      normalizationPackage.completenessTarget,
      normTStructure.normTStructureTheoremPackage,
      HeartRecognitionTarget.pureHeartRecognitionTarget_holds
        normTStructure.normTStructureTheoremPackage,
      classicalHeartIdentification.classicalMMQHeartTheorems,
      classicalHeartIdentification.classicalMMQHeartTheorems.mixedMotiveHeartOverQTarget,
      mmqIdentification.mmqPureHeartCompatibility,
      proofRelevantPeriodTheorem.proofRelevantPeriodStatementTarget,
      proofRelevantPeriodTheorem.realizationCompatibilityTarget,
      proofRelevantPeriodTheoremFromComparisonFaithfulness.comparisonFaithfulnessBridgeTarget,
      proofRelevantPeriodTheoremFromComparisonFaithfulness.recoversProofRelevantPeriodTheoremTarget⟩

/-- Terminal package constructor using the concrete dependency-DAG statement.

This is the non-arbitrary Package 9 assembly route: the final
`dependencyDAGStatement` is `concreteDependencyDAGStatement`, and its witness is
`concreteDependencyDAG_holds_from_packages`.
-/
def ofPackagesWithConcreteDependencyDAG
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
    (stableCompletion : StableAdditiveKaroubiCompletionTarget recognitionSpine internalSpine)
    (stableCompletionConstruction :
      TraceStableCompletionConstructionTarget recognitionSpine internalSpine stableCompletion)
    (completionUniversalProperty :
      TraceCompletionUniversalPropertyTarget recognitionSpine internalSpine stableCompletion
        stableCompletionConstruction)
    (corePresentationEquivalence :
      CorePresentationEquivalenceTarget recognitionSpine internalSpine classicalSpine)
    (completedPresentationEquivalence :
      CompletedPresentationEquivalenceTarget recognitionSpine internalSpine stableCompletion
        stableCompletionConstruction completionUniversalProperty classicalSpine
        corePresentationEquivalence)
    (traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget recognitionSpine internalSpine classicalSpine)
    (canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence)
    (realizationComparison :
      RealizationComparisonTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (periodConjectureViaRealization :
      PeriodConjectureViaRealizationTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence realizationComparison)
    (universalRecognition :
      DMgmUniversalRecognitionTheoremTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (normalizationPackage : NormalizationPackageTarget internalSpine)
    (normalizationTransport :
      NormalizationTransportAcrossDMgmEquivalenceTarget recognitionSpine internalSpine
        normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence)
    (transportedNormalizationIsMotivic :
      TransportedNormalizationIsMotivicTarget recognitionSpine internalSpine normalizationPackage
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport)
    (normTStructure :
      NormTStructureTarget recognitionSpine internalSpine normalizationPackage classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
        transportedNormalizationIsMotivic)
    (classicalHeartIdentification :
      ClassicalHeartIdentificationTarget recognitionSpine internalSpine normalizationPackage
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
        transportedNormalizationIsMotivic normTStructure
        (HeartRecognitionTarget.ofNormTStructure recognitionSpine internalSpine
          normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
          normalizationTransport transportedNormalizationIsMotivic normTStructure))
    (mmqIdentification :
      MMQIdentificationTarget recognitionSpine internalSpine normalizationPackage classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
        transportedNormalizationIsMotivic normTStructure
        (HeartRecognitionTarget.ofNormTStructure recognitionSpine internalSpine
          normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
          normalizationTransport transportedNormalizationIsMotivic normTStructure))
    (proofRelevantPeriodTheorem :
      ProofRelevantPeriodTheoremTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (proofRelevantPeriodTheoremFromComparisonFaithfulness :
      ProofRelevantPeriodTheoremFromComparisonFaithfulnessTarget recognitionSpine internalSpine
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
        proofRelevantPeriodTheorem) :
    MMQRecognitionClosedTarget recognitionSpine internalSpine classicalSpine :=
  MMQRecognitionClosedTarget.ofPackages recognitionSpine internalSpine classicalSpine
    stableCompletion stableCompletionConstruction completionUniversalProperty
    corePresentationEquivalence completedPresentationEquivalence traceToDMgmEquivalence
    canonicalDMgmEquivalence realizationComparison periodConjectureViaRealization
    universalRecognition normalizationPackage normalizationTransport
    transportedNormalizationIsMotivic normTStructure
    (HeartRecognitionTarget.ofNormTStructure recognitionSpine internalSpine
      normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
      normalizationTransport transportedNormalizationIsMotivic normTStructure)
    classicalHeartIdentification mmqIdentification proofRelevantPeriodTheorem
    proofRelevantPeriodTheoremFromComparisonFaithfulness
    (concreteDependencyDAGStatement recognitionSpine stableCompletion
      stableCompletionConstruction completionUniversalProperty traceToDMgmEquivalence
      canonicalDMgmEquivalence realizationComparison periodConjectureViaRealization
      universalRecognition normalizationPackage normalizationTransport
      transportedNormalizationIsMotivic normTStructure classicalHeartIdentification
      mmqIdentification proofRelevantPeriodTheorem
      proofRelevantPeriodTheoremFromComparisonFaithfulness)
    (concreteDependencyDAG_holds_from_packages recognitionSpine stableCompletion
      stableCompletionConstruction completionUniversalProperty traceToDMgmEquivalence
      canonicalDMgmEquivalence realizationComparison periodConjectureViaRealization
      universalRecognition normalizationPackage normalizationTransport
      transportedNormalizationIsMotivic normTStructure classicalHeartIdentification
      mmqIdentification proofRelevantPeriodTheorem
      proofRelevantPeriodTheoremFromComparisonFaithfulness)

/-- Final terminal constructor over the sealed package spine.

Unlike `ofPackagesWithConcreteDependencyDAG`, this route does not accept an arbitrary
Package 8 period input.  It constructs the realization comparison, period package,
proof-relevant period theorem, and comparison-faithfulness bridge from the sealed
internal realization functor and the canonical equivalence packages. -/
def ofAllSealedPackages
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
    (stableCompletion : StableAdditiveKaroubiCompletionTarget recognitionSpine internalSpine)
    (stableCompletionConstruction :
      TraceStableCompletionConstructionTarget recognitionSpine internalSpine stableCompletion)
    (completionUniversalProperty :
      TraceCompletionUniversalPropertyTarget recognitionSpine internalSpine stableCompletion
        stableCompletionConstruction)
    (corePresentationEquivalence :
      CorePresentationEquivalenceTarget recognitionSpine internalSpine classicalSpine)
    (completedPresentationEquivalence :
      CompletedPresentationEquivalenceTarget recognitionSpine internalSpine stableCompletion
        stableCompletionConstruction completionUniversalProperty classicalSpine
        corePresentationEquivalence)
    (traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget recognitionSpine internalSpine classicalSpine)
    (canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence)
    (internalRealization : InternalRealizationFunctorData ctx structuredEq)
    (universalRecognition :
      DMgmUniversalRecognitionTheoremTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (normalizationPackage : NormalizationPackageTarget internalSpine)
    (normalizationTransport :
      NormalizationTransportAcrossDMgmEquivalenceTarget recognitionSpine internalSpine
        normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence)
    (transportedNormalizationIsMotivic :
      TransportedNormalizationIsMotivicTarget recognitionSpine internalSpine normalizationPackage
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport)
    (normTStructure :
      NormTStructureTarget recognitionSpine internalSpine normalizationPackage classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
        transportedNormalizationIsMotivic)
    (classicalHeartIdentification :
      ClassicalHeartIdentificationTarget recognitionSpine internalSpine normalizationPackage
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
        transportedNormalizationIsMotivic normTStructure
        (HeartRecognitionTarget.ofNormTStructure recognitionSpine internalSpine
          normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
          normalizationTransport transportedNormalizationIsMotivic normTStructure))
    (mmqIdentification :
      MMQIdentificationTarget recognitionSpine internalSpine normalizationPackage classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
        transportedNormalizationIsMotivic normTStructure
        (HeartRecognitionTarget.ofNormTStructure recognitionSpine internalSpine
          normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
          normalizationTransport transportedNormalizationIsMotivic normTStructure)) :
    MMQRecognitionClosedTarget recognitionSpine internalSpine classicalSpine :=
  let realizationComparison :=
    RealizationComparisonTarget.ofInternalRealizationFunctor recognitionSpine internalSpine
      classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence internalRealization
  let periodConjectureViaRealization :=
    PeriodConjectureViaRealizationTarget.ofSealedP8 recognitionSpine internalSpine
      classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence internalRealization
  let proofRelevantPeriodTheorem :=
    ProofRelevantPeriodTheoremTarget.ofSealedP8 recognitionSpine internalSpine
      classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence internalRealization
  let proofRelevantPeriodTheoremFromComparisonFaithfulness :
      ProofRelevantPeriodTheoremFromComparisonFaithfulnessTarget recognitionSpine internalSpine
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
        proofRelevantPeriodTheorem :=
    { comparisonFaithfulnessBridgeTarget :=
        ⟨canonicalDMgmEquivalence.canonicalEquivalence_holds,
          traceToDMgmEquivalence.homotopyCategoryComparison_holds⟩
      recoversProofRelevantPeriodTheoremTarget :=
        ⟨canonicalDMgmEquivalence.canonicalEquivalence_holds,
          canonicalDMgmEquivalence.rigidTensorTriangulatedEquivalence_holds,
          traceToDMgmEquivalence.homotopyCategoryComparison_holds⟩ }
  MMQRecognitionClosedTarget.ofPackagesWithConcreteDependencyDAG recognitionSpine internalSpine
    classicalSpine stableCompletion stableCompletionConstruction completionUniversalProperty
    corePresentationEquivalence completedPresentationEquivalence traceToDMgmEquivalence
    canonicalDMgmEquivalence realizationComparison periodConjectureViaRealization
    universalRecognition normalizationPackage normalizationTransport
    transportedNormalizationIsMotivic normTStructure classicalHeartIdentification
    mmqIdentification proofRelevantPeriodTheorem
    proofRelevantPeriodTheoremFromComparisonFaithfulness

end MMQRecognitionClosedTarget

/-- Final all-packages closed target, routed through `MMQRecognitionClosedTarget.ofAllSealedPackages`. -/
def finalAllPackagesClosed
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
    (stableCompletion : StableAdditiveKaroubiCompletionTarget recognitionSpine internalSpine)
    (stableCompletionConstruction :
      TraceStableCompletionConstructionTarget recognitionSpine internalSpine stableCompletion)
    (completionUniversalProperty :
      TraceCompletionUniversalPropertyTarget recognitionSpine internalSpine stableCompletion
        stableCompletionConstruction)
    (corePresentationEquivalence :
      CorePresentationEquivalenceTarget recognitionSpine internalSpine classicalSpine)
    (completedPresentationEquivalence :
      CompletedPresentationEquivalenceTarget recognitionSpine internalSpine stableCompletion
        stableCompletionConstruction completionUniversalProperty classicalSpine
        corePresentationEquivalence)
    (traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget recognitionSpine internalSpine classicalSpine)
    (canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence)
    (internalRealization : InternalRealizationFunctorData ctx structuredEq)
    (universalRecognition :
      DMgmUniversalRecognitionTheoremTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (normalizationPackage : NormalizationPackageTarget internalSpine)
    (normalizationTransport :
      NormalizationTransportAcrossDMgmEquivalenceTarget recognitionSpine internalSpine
        normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence)
    (transportedNormalizationIsMotivic :
      TransportedNormalizationIsMotivicTarget recognitionSpine internalSpine normalizationPackage
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport)
    (normTStructure :
      NormTStructureTarget recognitionSpine internalSpine normalizationPackage classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
        transportedNormalizationIsMotivic)
    (classicalHeartIdentification :
      ClassicalHeartIdentificationTarget recognitionSpine internalSpine normalizationPackage
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
        transportedNormalizationIsMotivic normTStructure
        (HeartRecognitionTarget.ofNormTStructure recognitionSpine internalSpine
          normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
          normalizationTransport transportedNormalizationIsMotivic normTStructure))
    (mmqIdentification :
      MMQIdentificationTarget recognitionSpine internalSpine normalizationPackage classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
        transportedNormalizationIsMotivic normTStructure
        (HeartRecognitionTarget.ofNormTStructure recognitionSpine internalSpine
          normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
          normalizationTransport transportedNormalizationIsMotivic normTStructure)) :
    MMQRecognitionClosedTarget recognitionSpine internalSpine classicalSpine :=
  MMQRecognitionClosedTarget.ofAllSealedPackages recognitionSpine internalSpine classicalSpine
    stableCompletion stableCompletionConstruction completionUniversalProperty
    corePresentationEquivalence completedPresentationEquivalence traceToDMgmEquivalence
    canonicalDMgmEquivalence internalRealization universalRecognition normalizationPackage
    normalizationTransport transportedNormalizationIsMotivic normTStructure
    classicalHeartIdentification mmqIdentification

/-- Final terminal constructor over the sealed package spine, deriving the
classical-heart and MM(Q) identification packages from the exposed component
theorem package of the transported motivic t-structure. -/
def mmqRecognitionClosedTargetOfAllSealedPackagesFromTStructureComponents
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
    (stableCompletion : StableAdditiveKaroubiCompletionTarget recognitionSpine internalSpine)
    (stableCompletionConstruction :
      TraceStableCompletionConstructionTarget recognitionSpine internalSpine stableCompletion)
    (completionUniversalProperty :
      TraceCompletionUniversalPropertyTarget recognitionSpine internalSpine stableCompletion
        stableCompletionConstruction)
    (corePresentationEquivalence :
      CorePresentationEquivalenceTarget recognitionSpine internalSpine classicalSpine)
    (completedPresentationEquivalence :
      CompletedPresentationEquivalenceTarget recognitionSpine internalSpine stableCompletion
        stableCompletionConstruction completionUniversalProperty classicalSpine
        corePresentationEquivalence)
    (traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget recognitionSpine internalSpine classicalSpine)
    (canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence)
    (internalRealization : InternalRealizationFunctorData ctx structuredEq)
    (universalRecognition :
      DMgmUniversalRecognitionTheoremTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (normalizationPackage : NormalizationPackageTarget internalSpine)
    (normalizationTransport :
      NormalizationTransportAcrossDMgmEquivalenceTarget recognitionSpine internalSpine
        normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence)
    (transportedNormalizationIsMotivic :
      TransportedNormalizationIsMotivicTarget recognitionSpine internalSpine normalizationPackage
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport)
    (normTStructure :
      NormTStructureTarget recognitionSpine internalSpine normalizationPackage classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
        transportedNormalizationIsMotivic)
    (components :
      TraceMotivicTStructureComponentTheorems normTStructure.traceMotivicTStructure) :
    MMQRecognitionClosedTarget recognitionSpine internalSpine classicalSpine :=
  let heartRecognition :=
    HeartRecognitionTarget.ofNormTStructure recognitionSpine internalSpine normalizationPackage
      classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
      transportedNormalizationIsMotivic normTStructure
  let classicalHeartIdentification :=
    ClassicalHeartIdentificationTarget.ofTraceMotivicTStructureData recognitionSpine internalSpine
      normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
      normalizationTransport transportedNormalizationIsMotivic normTStructure heartRecognition
      components
  let mmqIdentification :=
    MMQIdentificationTarget.ofClassicalHeartIdentification recognitionSpine internalSpine
      normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
      normalizationTransport transportedNormalizationIsMotivic normTStructure heartRecognition
      classicalHeartIdentification
  MMQRecognitionClosedTarget.ofAllSealedPackages recognitionSpine internalSpine classicalSpine
    stableCompletion stableCompletionConstruction completionUniversalProperty
    corePresentationEquivalence completedPresentationEquivalence traceToDMgmEquivalence
    canonicalDMgmEquivalence internalRealization universalRecognition normalizationPackage
    normalizationTransport transportedNormalizationIsMotivic normTStructure
    classicalHeartIdentification mmqIdentification

def mmqRecognitionClosedTargetOfAllSealedPackagesFromCertifiedStructuralPackage
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
    (stableCompletion : StableAdditiveKaroubiCompletionTarget recognitionSpine internalSpine)
    (stableCompletionConstruction :
      TraceStableCompletionConstructionTarget recognitionSpine internalSpine stableCompletion)
    (completionUniversalProperty :
      TraceCompletionUniversalPropertyTarget recognitionSpine internalSpine stableCompletion
        stableCompletionConstruction)
    (corePresentationEquivalence :
      CorePresentationEquivalenceTarget recognitionSpine internalSpine classicalSpine)
    (completedPresentationEquivalence :
      CompletedPresentationEquivalenceTarget recognitionSpine internalSpine stableCompletion
        stableCompletionConstruction completionUniversalProperty classicalSpine
        corePresentationEquivalence)
    (traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget recognitionSpine internalSpine classicalSpine)
    (canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence)
    (internalRealization : InternalRealizationFunctorData ctx structuredEq)
    (universalRecognition :
      DMgmUniversalRecognitionTheoremTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (normalizationPackage : NormalizationPackageTarget internalSpine)
    (normalizationTransport :
      NormalizationTransportAcrossDMgmEquivalenceTarget recognitionSpine internalSpine
        normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence)
    (transportedNormalizationIsMotivic :
      TransportedNormalizationIsMotivicTarget recognitionSpine internalSpine normalizationPackage
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport)
    (normTStructure :
      NormTStructureTarget recognitionSpine internalSpine normalizationPackage classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
        transportedNormalizationIsMotivic)
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        recognitionSpine.structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        recognitionSpine.structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        recognitionSpine.structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        recognitionSpine.structuralRecognition.recognition.recognitionInput.tracePresentation
        recognitionSpine.structuralRecognition.recognition.recognitionInput.classicalPresentation
        recognitionSpine.structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (certified : CertifiedDMgmStructuralRecognitionTarget.{u, v, w, x, y, z})
    (hCertified : certified.structuralRecognition = recognitionSpine.structuralRecognition)
    (traceNative :
      TraceNativeWeightDevissageData recognitionSpine.structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport)
    (threshold : Nat)
    (hThreshold : threshold ≤ traceNative.reconstructionLength)
    (hTStructure :
      normTStructure.traceMotivicTStructure =
        TraceMotivicTStructureData.ofCanonicalPacketCut traceNative threshold hThreshold) :
    MMQRecognitionClosedTarget recognitionSpine internalSpine classicalSpine :=
  let normalizationPacketCut_holds :
      (TraceMotivicTStructureData.ofCanonicalPacketCut traceNative threshold
        hThreshold).normalizationPacketCutTarget :=
    hTStructure ▸
      (normalizationInducesWeightCompatibleTStructure_holds
        normTStructure.normTStructureTheoremPackage).1
  mmqRecognitionClosedTargetOfAllSealedPackagesFromTStructureComponents recognitionSpine
    internalSpine classicalSpine stableCompletion stableCompletionConstruction
    completionUniversalProperty corePresentationEquivalence completedPresentationEquivalence
    traceToDMgmEquivalence canonicalDMgmEquivalence internalRealization universalRecognition
    normalizationPackage normalizationTransport transportedNormalizationIsMotivic normTStructure
    (hTStructure ▸
      TraceMotivicTStructureComponentTheorems.ofCanonicalPacketCutWithCertifiedStructuralPackage
        certified hCertified traceNative threshold hThreshold normalizationPacketCut_holds)

abbrev mmqRecognitionClosedTargetOfAllSealedPackagesFromCanonicalPacketCut :=
  @mmqRecognitionClosedTargetOfAllSealedPackagesFromCertifiedStructuralPackage

abbrev traceMotivicTStructureComponentsFromCertifiedStructuralPackage
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}} :=
  @TraceMotivicTStructureComponentTheorems.ofCanonicalPacketCutWithCertifiedStructuralPackage
    structuralRecognition

abbrev classicalHeartIdentificationFromCertifiedStructuralPackage
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z}) :=
  @ClassicalHeartIdentificationTarget.ofCanonicalPacketCutWithCertifiedStructuralPackage spine

abbrev mmqRecognitionClosedFromCertifiedStructuralPackage :=
  @mmqRecognitionClosedTargetOfAllSealedPackagesFromCertifiedStructuralPackage

end MotivicRecognition
end TraceCalc

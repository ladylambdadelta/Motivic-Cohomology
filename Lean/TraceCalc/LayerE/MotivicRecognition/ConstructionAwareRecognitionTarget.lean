import TraceCalc.LayerE.MotivicRecognition.DMgmQConstruction

universe u v w x y z

namespace TraceCalc
namespace MotivicRecognition

open LayerB.RealObjects.RewriteCalculusSetup
open ClassicalPeriods

/-- Honest construction-aware wrapper for the universal recognition theorem.

This does not claim that the trace-to-`DM_gm(Q)_Q` equivalence has been proved
from the concrete quotient-zigzag/Karoubi construction alone. Instead it keeps
the two indispensable inputs together:

* the proof-relevant universal-recognition data, and
* the live construction witness for the concrete `DM_gm(Q)_Q` recipient.

Downstream closeout code can then consume one canonical construction-aware
object instead of threading these ingredients separately. -/
structure ConstructionAwareDMgmUniversalRecognitionTarget
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (constructedDMgmQ : DMgmQConstruction.Construction.{u, v, w, x})
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (internal : InternalManuscriptSpineTarget P comparison C)
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq)
    (comparisonEquivalence : TraceCategoryEquivalentToDMgmQTarget spine internal classical)
    (canonicalEquivalence : CanonicalDMgmEquivalenceTarget spine internal classical
      comparisonEquivalence) where
  universalRecognitionData :
    DMgmUniversalRecognitionData
      spine internal classical comparisonEquivalence canonicalEquivalence
  constructedRecognition :
    DMgmQConstruction.Construction.ConstructedDMgmQRecognitionTarget constructedDMgmQ

namespace ConstructionAwareDMgmUniversalRecognitionTarget

def constructionStagesTarget
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
    {constructedDMgmQ : DMgmQConstruction.Construction.{u, v, w, x}}
    {internal : InternalManuscriptSpineTarget P comparison C}
    {classical : ClassicalManuscriptSpineTarget ctx structuredEq}
    {comparisonEquivalence : TraceCategoryEquivalentToDMgmQTarget spine internal classical}
    {canonicalEquivalence : CanonicalDMgmEquivalenceTarget spine internal classical
      comparisonEquivalence}
    (target : ConstructionAwareDMgmUniversalRecognitionTarget spine constructedDMgmQ
      internal classical comparisonEquivalence canonicalEquivalence) : Prop :=
  (target.constructedRecognition.constructedCategoryData =
      constructedDMgmQ.toDMgmQCategoryData) ∧
    (target.constructedRecognition.constructedInfrastructurePrefix =
      constructedDMgmQ.toInfrastructurePrefixData) ∧
    (target.constructedRecognition.constructedInfrastructurePrefix.categoryData =
      target.constructedRecognition.constructedCategoryData) ∧
    (target.constructedRecognition.rationalCorrespondenceStage =
      constructedDMgmQ.rationalCorrespondenceCategory) ∧
    (target.constructedRecognition.boundedComplexStage =
      constructedDMgmQ.boundedComplexes) ∧
    (target.constructedRecognition.localizationStage = constructedDMgmQ.localization) ∧
    (target.constructedRecognition.localizationUniversalPropertyStage =
      constructedDMgmQ.localizationUniversalProperty) ∧
    (target.constructedRecognition.karoubiEnvelopeStage =
      constructedDMgmQ.karoubiEnvelope) ∧
    (target.constructedRecognition.karoubiUniversalPropertyData =
      constructedDMgmQ.karoubiUniversalPropertyData)

theorem constructionStagesTarget_holds
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
    {constructedDMgmQ : DMgmQConstruction.Construction.{u, v, w, x}}
    {internal : InternalManuscriptSpineTarget P comparison C}
    {classical : ClassicalManuscriptSpineTarget ctx structuredEq}
    {comparisonEquivalence : TraceCategoryEquivalentToDMgmQTarget spine internal classical}
    {canonicalEquivalence : CanonicalDMgmEquivalenceTarget spine internal classical
      comparisonEquivalence}
    (target : ConstructionAwareDMgmUniversalRecognitionTarget spine constructedDMgmQ
      internal classical comparisonEquivalence canonicalEquivalence) :
    constructionStagesTarget target :=
  ⟨target.constructedRecognition.categoryDataFromConstruction,
    target.constructedRecognition.infrastructurePrefixFromConstruction,
    target.constructedRecognition.prefixCarriesConstructedCategoryData,
    target.constructedRecognition.rationalCorrespondenceStageMatchesConstruction,
    target.constructedRecognition.boundedComplexStageMatchesConstruction,
    target.constructedRecognition.localizationStageMatchesConstruction,
    target.constructedRecognition.localizationUniversalPropertyMatchesCanonical,
    target.constructedRecognition.karoubiEnvelopeStageMatchesConstruction,
    target.constructedRecognition.karoubiUniversalPropertyDataMatchesConstruction⟩

def universalRecognitionPackageTarget
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
    {constructedDMgmQ : DMgmQConstruction.Construction.{u, v, w, x}}
    {internal : InternalManuscriptSpineTarget P comparison C}
    {classical : ClassicalManuscriptSpineTarget ctx structuredEq}
    {comparisonEquivalence : TraceCategoryEquivalentToDMgmQTarget spine internal classical}
    {canonicalEquivalence : CanonicalDMgmEquivalenceTarget spine internal classical
      comparisonEquivalence}
    (target : ConstructionAwareDMgmUniversalRecognitionTarget spine constructedDMgmQ
      internal classical comparisonEquivalence canonicalEquivalence) : Prop :=
  target.universalRecognitionData.universalRecognitionTarget ∧
    target.universalRecognitionData.uniquenessOfRecipientTarget ∧
    target.universalRecognitionData.comparisonAgreementTarget

theorem universalRecognitionPackageTarget_holds
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
    {constructedDMgmQ : DMgmQConstruction.Construction.{u, v, w, x}}
    {internal : InternalManuscriptSpineTarget P comparison C}
    {classical : ClassicalManuscriptSpineTarget ctx structuredEq}
    {comparisonEquivalence : TraceCategoryEquivalentToDMgmQTarget spine internal classical}
    {canonicalEquivalence : CanonicalDMgmEquivalenceTarget spine internal classical
      comparisonEquivalence}
    (target : ConstructionAwareDMgmUniversalRecognitionTarget spine constructedDMgmQ
      internal classical comparisonEquivalence canonicalEquivalence) :
    universalRecognitionPackageTarget target :=
  ⟨target.universalRecognitionData.universalRecognitionTarget,
    target.universalRecognitionData.uniquenessOfRecipientTarget,
    target.universalRecognitionData.comparisonAgreementTarget⟩

def ofCanonicalDMgmEquivalenceAndConstruction
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (constructedDMgmQ : DMgmQConstruction.Construction.{u, v, w, x})
    (internal : InternalManuscriptSpineTarget P comparison C)
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq)
    (comparisonEquivalence : TraceCategoryEquivalentToDMgmQTarget spine internal classical)
    (canonicalEquivalence : CanonicalDMgmEquivalenceTarget spine internal classical
      comparisonEquivalence) :
    ConstructionAwareDMgmUniversalRecognitionTarget spine constructedDMgmQ internal classical
      comparisonEquivalence canonicalEquivalence where
  universalRecognitionData :=
    DMgmUniversalRecognitionData.ofCanonicalDMgmEquivalence
      spine internal classical comparisonEquivalence canonicalEquivalence
  constructedRecognition :=
    DMgmQConstruction.Construction.ConstructedDMgmQRecognitionTarget.ofConstruction
      constructedDMgmQ

end ConstructionAwareDMgmUniversalRecognitionTarget

end MotivicRecognition
end TraceCalc
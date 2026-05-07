import TraceCalc.MotivicRecognition.RealizationAgreementStatements

universe u v w x y z

namespace TraceCalc
namespace MotivicRecognition

open ClassicalPeriods
open LayerB.RealObjects.RewriteCalculusSetup

namespace RealizationComparisonTarget

/-- Final Package 8 realization-comparison constructor from the sealed internal realization
functor.  The period field is the full framed-period statement carried by
`PeriodMatrixAgreementStatement`; no surrogate period-matrix surface is used. -/
def ofInternalRealizationFunctor
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
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
      TraceCategoryEquivalentToDMgmQTarget spine internalSpine classicalSpine)
    (canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget spine internalSpine classicalSpine
        traceToDMgmEquivalence)
    (internalRealization : InternalRealizationFunctorData ctx structuredEq) :
    RealizationComparisonTarget spine internalSpine classicalSpine
      traceToDMgmEquivalence canonicalDMgmEquivalence where
  bettiAgreementTarget :=
    BettiAgreementStatement internalRealization.geometricRealizationFunctor
      (fun idx => (internalRealization.geometricObjectData idx).toStructuredComparisonObject)
  deRhamAgreementTarget :=
    DeRhamAgreementStatement internalRealization.geometricRealizationFunctor
      (fun idx => (internalRealization.geometricObjectData idx).toStructuredComparisonObject)
  comparisonIsomorphismAgreementTarget :=
    ComparisonIsomorphismAgreementStatement internalRealization.geometricRealizationFunctor
      (fun idx => (internalRealization.geometricObjectData idx).toStructuredComparisonObject)
  periodMatrixAgreementTarget :=
    PeriodMatrixAgreementStatement internalRealization.geometricFramedFunctoriality

end RealizationComparisonTarget

namespace ProofRelevantPeriodTheoremTarget

/-- Final Package 8 proof-relevant period theorem constructor.  It uses the Wall 7
comparison-faithfulness surface, which has no external injectivity hypotheses. -/
def ofSealedP8
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
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
      TraceCategoryEquivalentToDMgmQTarget spine internalSpine classicalSpine)
    (canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget spine internalSpine classicalSpine
        traceToDMgmEquivalence)
    (_internalRealization : InternalRealizationFunctorData ctx structuredEq) :
    ProofRelevantPeriodTheoremTarget spine internalSpine classicalSpine
      traceToDMgmEquivalence canonicalDMgmEquivalence :=
  ProofRelevantPeriodTheoremTarget.ofRealizationAgreementComparisonFaithfulness
    spine internalSpine classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
    ⟨canonicalDMgmEquivalence.canonicalEquivalence_holds,
      canonicalDMgmEquivalence.rigidTensorTriangulatedEquivalence_holds,
      traceToDMgmEquivalence.homotopyCategoryComparison_holds⟩
    traceToDMgmEquivalence.homotopyCategoryComparison_holds

end ProofRelevantPeriodTheoremTarget

namespace PeriodConjectureViaRealizationTarget

/-- Final Package 8 period-conjecture-via-realization constructor from the sealed
realization comparison and the canonical equivalence witnesses. -/
def ofSealedP8
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
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
      TraceCategoryEquivalentToDMgmQTarget spine internalSpine classicalSpine)
    (canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget spine internalSpine classicalSpine
        traceToDMgmEquivalence)
    (internalRealization : InternalRealizationFunctorData ctx structuredEq) :
    PeriodConjectureViaRealizationTarget spine internalSpine classicalSpine
      traceToDMgmEquivalence canonicalDMgmEquivalence
      (RealizationComparisonTarget.ofInternalRealizationFunctor spine internalSpine
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence internalRealization) where
  periodFaithfulnessTransportTarget :=
    ⟨bettiAgreement_from_internal_realization_functor internalRealization,
      deRhamAgreement_from_internal_realization_functor internalRealization⟩
  equivalenceWithClassicalStatementTarget :=
    ⟨periodMatrix_agreement_from_internal_realization_functor internalRealization,
      canonicalDMgmEquivalence.canonicalEquivalence_holds,
      canonicalDMgmEquivalence.rigidTensorTriangulatedEquivalence_holds⟩

end PeriodConjectureViaRealizationTarget

/-- Project-native final Package 8 period package. -/
def finalPackage8PeriodPackage
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
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
      TraceCategoryEquivalentToDMgmQTarget spine internalSpine classicalSpine)
    (canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget spine internalSpine classicalSpine
        traceToDMgmEquivalence)
    (internalRealization : InternalRealizationFunctorData ctx structuredEq) :
    PeriodConjectureViaRealizationTarget spine internalSpine classicalSpine
      traceToDMgmEquivalence canonicalDMgmEquivalence
      (RealizationComparisonTarget.ofInternalRealizationFunctor spine internalSpine
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence internalRealization) :=
  PeriodConjectureViaRealizationTarget.ofSealedP8 spine internalSpine classicalSpine
    traceToDMgmEquivalence canonicalDMgmEquivalence internalRealization

/-- Final Package 8 theorem, exposed as the project-native period-conjecture package. -/
theorem finalPackage8PeriodTheorem
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
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
      TraceCategoryEquivalentToDMgmQTarget spine internalSpine classicalSpine)
    (canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget spine internalSpine classicalSpine
        traceToDMgmEquivalence)
    (internalRealization : InternalRealizationFunctorData ctx structuredEq) :
    PeriodConjectureViaRealizationTarget spine internalSpine classicalSpine
      traceToDMgmEquivalence canonicalDMgmEquivalence
      (RealizationComparisonTarget.ofInternalRealizationFunctor spine internalSpine
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence internalRealization) :=
  finalPackage8PeriodPackage spine internalSpine classicalSpine traceToDMgmEquivalence
    canonicalDMgmEquivalence internalRealization

end MotivicRecognition
end TraceCalc
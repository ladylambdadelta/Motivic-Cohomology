import TraceCalc.LayerE.MotivicRecognition.RealizationAgreementStatements

universe u v w x y z

namespace TraceCalc
namespace MotivicRecognition

/-!
LayerE canonical location for the Package 8 realization-period comparison
proofs.

The top-level `TraceCalc.MotivicRecognition.Package8Proofs` module is now a
compatibility wrapper.
-/

open ClassicalPeriods
open LayerB.RealObjects.RewriteCalculusSetup

namespace RealizationComparisonTarget

def ofCertifiedRealizationComparison
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
    {realization : GeometricRealizationFunctorData ctx}
    {periodMatrixAgreementStatement : Prop}
    {objectMap : realization.ObjectIndex → ClassicalStructuredComparisonObject ctx}
      (certified : CertifiedRealizationComparisonTarget realization
        periodMatrixAgreementStatement objectMap) :
    RealizationComparisonTarget spine internalSpine classicalSpine
      traceToDMgmEquivalence canonicalDMgmEquivalence where
  bettiAgreementTarget := BettiAgreementStatement realization objectMap
  deRhamAgreementTarget := DeRhamAgreementStatement realization objectMap
  comparisonIsomorphismAgreementTarget :=
    ComparisonIsomorphismAgreementStatement realization objectMap
  periodMatrixAgreementTarget := periodMatrixAgreementStatement

theorem bettiAgreementTarget_holds_ofCertifiedRealizationComparison
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
    {realization : GeometricRealizationFunctorData ctx}
    {periodMatrixAgreementStatement : Prop}
    {objectMap : realization.ObjectIndex → ClassicalStructuredComparisonObject ctx}
    (certified : CertifiedRealizationComparisonTarget realization
      periodMatrixAgreementStatement objectMap) :
    (ofCertifiedRealizationComparison spine internalSpine classicalSpine
      traceToDMgmEquivalence canonicalDMgmEquivalence certified).bettiAgreementTarget :=
  certified.bettiAgreement_holds

theorem deRhamAgreementTarget_holds_ofCertifiedRealizationComparison
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
    {realization : GeometricRealizationFunctorData ctx}
    {periodMatrixAgreementStatement : Prop}
    {objectMap : realization.ObjectIndex → ClassicalStructuredComparisonObject ctx}
    (certified : CertifiedRealizationComparisonTarget realization
      periodMatrixAgreementStatement objectMap) :
    (ofCertifiedRealizationComparison spine internalSpine classicalSpine
      traceToDMgmEquivalence canonicalDMgmEquivalence certified).deRhamAgreementTarget :=
  certified.deRhamAgreement_holds

theorem comparisonIsomorphismAgreementTarget_holds_ofCertifiedRealizationComparison
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
    {realization : GeometricRealizationFunctorData ctx}
    {periodMatrixAgreementStatement : Prop}
    {objectMap : realization.ObjectIndex → ClassicalStructuredComparisonObject ctx}
    (certified : CertifiedRealizationComparisonTarget realization
      periodMatrixAgreementStatement objectMap) :
    (ofCertifiedRealizationComparison spine internalSpine classicalSpine
      traceToDMgmEquivalence canonicalDMgmEquivalence certified)
        .comparisonIsomorphismAgreementTarget :=
  certified.comparisonIsomorphismAgreement_holds

theorem periodMatrixAgreementTarget_holds_ofCertifiedRealizationComparison
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
    {realization : GeometricRealizationFunctorData ctx}
    {periodMatrixAgreementStatement : Prop}
    {objectMap : realization.ObjectIndex → ClassicalStructuredComparisonObject ctx}
    (certified : CertifiedRealizationComparisonTarget realization
      periodMatrixAgreementStatement objectMap) :
    (ofCertifiedRealizationComparison spine internalSpine classicalSpine
      traceToDMgmEquivalence canonicalDMgmEquivalence certified).periodMatrixAgreementTarget :=
  certified.periodMatrixAgreement_holds

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
      traceToDMgmEquivalence canonicalDMgmEquivalence :=
  ofCertifiedRealizationComparison spine internalSpine classicalSpine
    traceToDMgmEquivalence canonicalDMgmEquivalence
    (CertifiedRealizationComparisonTarget.ofInternalRealizationFunctor
      internalRealization)

/-- Public Package 8 realization-comparison constructor from the Layer D target-level
owner route. -/
def ofLayerDTarget
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    (internalSpine : InternalManuscriptSpineTarget P comparison C)
    (classicalSpine : ClassicalManuscriptSpineTarget ctx target.structuredComparisonEquality)
    (traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget spine internalSpine classicalSpine)
    (canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget spine internalSpine classicalSpine
        traceToDMgmEquivalence)
    (target : LayerD.InternalRealizationFunctorTarget ctx) :
    RealizationComparisonTarget spine internalSpine classicalSpine
      traceToDMgmEquivalence canonicalDMgmEquivalence :=
  ofInternalRealizationFunctor spine internalSpine classicalSpine
    traceToDMgmEquivalence canonicalDMgmEquivalence
    (InternalRealizationFunctorData.ofLayerDTarget target)

/-- Public Package 8 realization-comparison constructor from the Layer D proof wrapper. -/
def ofLayerDData
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {target : LayerD.InternalRealizationFunctorTarget ctx}
    (internalSpine : InternalManuscriptSpineTarget P comparison C)
    (classicalSpine : ClassicalManuscriptSpineTarget ctx target.structuredComparisonEquality)
    (traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget spine internalSpine classicalSpine)
    (canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget spine internalSpine classicalSpine
        traceToDMgmEquivalence)
    (data : LayerD.InternalRealizationFunctorData ctx target) :
    RealizationComparisonTarget spine internalSpine classicalSpine
      traceToDMgmEquivalence canonicalDMgmEquivalence :=
  ofInternalRealizationFunctor spine internalSpine classicalSpine
    traceToDMgmEquivalence canonicalDMgmEquivalence
    (InternalRealizationFunctorData.ofLayerDData data)

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
        traceToDMgmEquivalence) :
    ProofRelevantPeriodTheoremTarget spine internalSpine classicalSpine
      traceToDMgmEquivalence canonicalDMgmEquivalence :=
  ProofRelevantPeriodTheoremTarget.ofRealizationAgreementComparisonFaithfulness
    spine internalSpine classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence

theorem proofRelevantPeriodStatementTarget_holds
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {internalSpine : InternalManuscriptSpineTarget P comparison C}
    {classicalSpine : ClassicalManuscriptSpineTarget ctx structuredEq}
    {traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget spine internalSpine classicalSpine}
    {canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget spine internalSpine classicalSpine
        traceToDMgmEquivalence}
    (proofRelevantPeriodTheorem :
      ProofRelevantPeriodTheoremTarget spine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence) :
    proofRelevantPeriodTheorem.proofRelevantPeriodStatementTarget :=
  proofRelevantPeriodTheorem.proofRelevantPeriodStatementTarget

theorem realizationCompatibilityTarget_holds
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {internalSpine : InternalManuscriptSpineTarget P comparison C}
    {classicalSpine : ClassicalManuscriptSpineTarget ctx structuredEq}
    {traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget spine internalSpine classicalSpine}
    {canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget spine internalSpine classicalSpine
        traceToDMgmEquivalence}
    (proofRelevantPeriodTheorem :
      ProofRelevantPeriodTheoremTarget spine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence) :
    proofRelevantPeriodTheorem.realizationCompatibilityTarget :=
  proofRelevantPeriodTheorem.realizationCompatibilityTarget

end ProofRelevantPeriodTheoremTarget

namespace ProofRelevantPeriodTheoremFromComparisonFaithfulnessTarget

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
        traceToDMgmEquivalence) :
    ProofRelevantPeriodTheoremFromComparisonFaithfulnessTarget
      spine internalSpine classicalSpine traceToDMgmEquivalence
      canonicalDMgmEquivalence
      (ProofRelevantPeriodTheoremTarget.ofSealedP8 spine internalSpine
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence) :=
  ProofRelevantPeriodTheoremFromComparisonFaithfulnessTarget.ofEquivalenceTargets
    spine internalSpine classicalSpine traceToDMgmEquivalence
    canonicalDMgmEquivalence
    (ProofRelevantPeriodTheoremTarget.ofSealedP8 spine internalSpine
      classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence)

theorem comparisonFaithfulnessBridgeTarget_holds
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {internalSpine : InternalManuscriptSpineTarget P comparison C}
    {classicalSpine : ClassicalManuscriptSpineTarget ctx structuredEq}
    {traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget spine internalSpine classicalSpine}
    {canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget spine internalSpine classicalSpine
        traceToDMgmEquivalence}
    {proofRelevantPeriodTheorem :
      ProofRelevantPeriodTheoremTarget spine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence}
    (proofRelevantPeriodTheoremFromComparisonFaithfulness :
      ProofRelevantPeriodTheoremFromComparisonFaithfulnessTarget
        spine internalSpine classicalSpine traceToDMgmEquivalence
        canonicalDMgmEquivalence proofRelevantPeriodTheorem) :
    proofRelevantPeriodTheoremFromComparisonFaithfulness.comparisonFaithfulnessBridgeTarget :=
  proofRelevantPeriodTheoremFromComparisonFaithfulness.comparisonFaithfulnessBridgeTarget

theorem recoversProofRelevantPeriodTheoremTarget_holds
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {internalSpine : InternalManuscriptSpineTarget P comparison C}
    {classicalSpine : ClassicalManuscriptSpineTarget ctx structuredEq}
    {traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget spine internalSpine classicalSpine}
    {canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget spine internalSpine classicalSpine
        traceToDMgmEquivalence}
    {proofRelevantPeriodTheorem :
      ProofRelevantPeriodTheoremTarget spine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence}
    (proofRelevantPeriodTheoremFromComparisonFaithfulness :
      ProofRelevantPeriodTheoremFromComparisonFaithfulnessTarget
        spine internalSpine classicalSpine traceToDMgmEquivalence
        canonicalDMgmEquivalence proofRelevantPeriodTheorem) :
    proofRelevantPeriodTheoremFromComparisonFaithfulness.recoversProofRelevantPeriodTheoremTarget :=
  proofRelevantPeriodTheoremFromComparisonFaithfulness.recoversProofRelevantPeriodTheoremTarget

end ProofRelevantPeriodTheoremFromComparisonFaithfulnessTarget

namespace PeriodConjectureViaRealizationTarget

def ofCertifiedRealizationComparison
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
    {realization : GeometricRealizationFunctorData ctx}
    {periodMatrixAgreementStatement : Prop}
    {objectMap : realization.ObjectIndex → ClassicalStructuredComparisonObject ctx}
    (certified : CertifiedRealizationComparisonTarget realization
      periodMatrixAgreementStatement objectMap) :
    PeriodConjectureViaRealizationTarget spine internalSpine classicalSpine
      traceToDMgmEquivalence canonicalDMgmEquivalence
      (RealizationComparisonTarget.ofCertifiedRealizationComparison spine internalSpine
          classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence) where
  periodFaithfulnessTransportTarget :=
    ⟨RealizationComparisonTarget
        .bettiAgreementTarget_holds_ofCertifiedRealizationComparison
        spine internalSpine classicalSpine traceToDMgmEquivalence
        canonicalDMgmEquivalence certified,
      RealizationComparisonTarget
        .deRhamAgreementTarget_holds_ofCertifiedRealizationComparison
        spine internalSpine classicalSpine traceToDMgmEquivalence
        canonicalDMgmEquivalence certified⟩
  equivalenceWithClassicalStatementTarget :=
    ⟨RealizationComparisonTarget
        .periodMatrixAgreementTarget_holds_ofCertifiedRealizationComparison
        spine internalSpine classicalSpine traceToDMgmEquivalence
        canonicalDMgmEquivalence certified,
      canonicalDMgmEquivalence.canonicalEquivalence_holds,
      canonicalDMgmEquivalence.rigidTensorTriangulatedEquivalence_holds⟩

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
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence internalRealization) :=
  let certified :=
    CertifiedRealizationComparisonTarget.ofInternalRealizationFunctor internalRealization
  ofCertifiedRealizationComparison spine internalSpine classicalSpine
    traceToDMgmEquivalence canonicalDMgmEquivalence certified

/-- Final Package 8 period-conjecture-via-realization constructor from the Layer D target-level
owner route. -/
def ofLayerDTarget
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    (internalSpine : InternalManuscriptSpineTarget P comparison C)
    (classicalSpine : ClassicalManuscriptSpineTarget ctx target.structuredComparisonEquality)
    (traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget spine internalSpine classicalSpine)
    (canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget spine internalSpine classicalSpine
        traceToDMgmEquivalence)
    (target : LayerD.InternalRealizationFunctorTarget ctx) :
    PeriodConjectureViaRealizationTarget spine internalSpine classicalSpine
      traceToDMgmEquivalence canonicalDMgmEquivalence
      (RealizationComparisonTarget.ofLayerDTarget spine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence target) :=
  ofSealedP8 spine internalSpine classicalSpine traceToDMgmEquivalence
    canonicalDMgmEquivalence
    (InternalRealizationFunctorData.ofLayerDTarget target)

/-- Final Package 8 period-conjecture-via-realization constructor from the Layer D proof
wrapper. -/
def ofLayerDData
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {target : LayerD.InternalRealizationFunctorTarget ctx}
    (internalSpine : InternalManuscriptSpineTarget P comparison C)
    (classicalSpine : ClassicalManuscriptSpineTarget ctx target.structuredComparisonEquality)
    (traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget spine internalSpine classicalSpine)
    (canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget spine internalSpine classicalSpine
        traceToDMgmEquivalence)
    (data : LayerD.InternalRealizationFunctorData ctx target) :
    PeriodConjectureViaRealizationTarget spine internalSpine classicalSpine
      traceToDMgmEquivalence canonicalDMgmEquivalence
      (RealizationComparisonTarget.ofLayerDData spine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence data) :=
  ofSealedP8 spine internalSpine classicalSpine traceToDMgmEquivalence
    canonicalDMgmEquivalence
    (InternalRealizationFunctorData.ofLayerDData data)

theorem periodFaithfulnessTransportTarget_holds
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {internalSpine : InternalManuscriptSpineTarget P comparison C}
    {classicalSpine : ClassicalManuscriptSpineTarget ctx structuredEq}
    {traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget spine internalSpine classicalSpine}
    {canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget spine internalSpine classicalSpine
        traceToDMgmEquivalence}
    {realizationComparison :
      RealizationComparisonTarget spine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence}
    (periodConjectureViaRealization :
      PeriodConjectureViaRealizationTarget spine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence realizationComparison) :
    periodConjectureViaRealization.periodFaithfulnessTransportTarget :=
  periodConjectureViaRealization.periodFaithfulnessTransportTarget

theorem equivalenceWithClassicalStatementTarget_holds
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {internalSpine : InternalManuscriptSpineTarget P comparison C}
    {classicalSpine : ClassicalManuscriptSpineTarget ctx structuredEq}
    {traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget spine internalSpine classicalSpine}
    {canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget spine internalSpine classicalSpine
        traceToDMgmEquivalence}
    {realizationComparison :
      RealizationComparisonTarget spine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence}
    (periodConjectureViaRealization :
      PeriodConjectureViaRealizationTarget spine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence realizationComparison) :
    periodConjectureViaRealization.equivalenceWithClassicalStatementTarget :=
  periodConjectureViaRealization.equivalenceWithClassicalStatementTarget

/-- Exact manuscript-facing transported period-faithfulness statement for
`cor:period-conjecture-via-realization`.

This is the Lean proposition form of the manuscript corollary: the trace-side
faithfulness statement and the classical structured period conjecture are the
same statement after transport along the canonical `Tcan ≃ DM_gm(Q)` route.
In the current owner-route architecture, that transported identification is
represented by the canonical equivalence package together with the homotopy
comparison compatibility witnessing that the realized period data agree across
the equivalence. -/
def manuscriptStatement
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {internalSpine : InternalManuscriptSpineTarget P comparison C}
    {classicalSpine : ClassicalManuscriptSpineTarget ctx structuredEq}
    {traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget spine internalSpine classicalSpine}
    {canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget spine internalSpine classicalSpine
        traceToDMgmEquivalence} : Prop :=
  canonicalDMgmEquivalence.canonicalEquivalenceTarget ∧
    canonicalDMgmEquivalence.rigidTensorTriangulatedEquivalenceTarget ∧
    traceToDMgmEquivalence.homotopyCategoryComparisonTarget

/-- The manuscript-facing transported statement is exactly the proof-relevant
period theorem surface used downstream in Package 9. -/
theorem manuscriptStatement_iff_proofRelevant
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {internalSpine : InternalManuscriptSpineTarget P comparison C}
    {classicalSpine : ClassicalManuscriptSpineTarget ctx structuredEq}
    {traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget spine internalSpine classicalSpine}
    {canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget spine internalSpine classicalSpine
        traceToDMgmEquivalence}
    (proofRelevantPeriodTheorem :
      ProofRelevantPeriodTheoremTarget spine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence) :
    manuscriptStatement
        (traceToDMgmEquivalence := traceToDMgmEquivalence)
        (canonicalDMgmEquivalence := canonicalDMgmEquivalence) ↔
      proofRelevantPeriodTheorem.proofRelevantPeriodStatementTarget := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-- Constructive proof of the exact manuscript-facing transported statement from
the sealed Package 8 owner route. -/
theorem manuscriptStatement_holds_ofSealedP8
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
        traceToDMgmEquivalence) :
    manuscriptStatement
      (traceToDMgmEquivalence := traceToDMgmEquivalence)
      (canonicalDMgmEquivalence := canonicalDMgmEquivalence) :=
  ProofRelevantPeriodTheoremTarget.proofRelevantPeriodStatementTarget_holds
    (ProofRelevantPeriodTheoremTarget.ofSealedP8
      spine internalSpine classicalSpine traceToDMgmEquivalence
      canonicalDMgmEquivalence)

/-- Explicit first-pass Track C proposition for `cor:period-conjecture-via-realization`.

This is the exact proposition currently discharged by Package 8: one conjunct
transports period faithfulness through Betti/de Rham agreement, and the second
conjunct identifies the resulting statement with the classical lane through
period-matrix agreement plus the canonical equivalence package. This remains
weaker than the manuscript's single transported equivalence statement. -/
def firstPassStatement
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {internalSpine : InternalManuscriptSpineTarget P comparison C}
    {classicalSpine : ClassicalManuscriptSpineTarget ctx structuredEq}
    {traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget spine internalSpine classicalSpine}
    {canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget spine internalSpine classicalSpine
        traceToDMgmEquivalence}
    {realizationComparison :
      RealizationComparisonTarget spine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence} : Prop :=
  (realizationComparison.bettiAgreementTarget ∧
      realizationComparison.deRhamAgreementTarget) ∧
    (realizationComparison.periodMatrixAgreementTarget ∧
      canonicalDMgmEquivalence.canonicalEquivalenceTarget ∧
      canonicalDMgmEquivalence.rigidTensorTriangulatedEquivalenceTarget)

/-- Real theorem-level equivalence between the explicit first-pass corollary
proposition and the two fields carried by `PeriodConjectureViaRealizationTarget`.

This replaces the earlier projection-only wrapper theorem. It is still a
first-pass Track C result: the right-hand side is the current Package 8 theorem
surface, and the left-hand side makes that theorem shape explicit as a single
proposition. -/
theorem firstPassStatement_iff
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {internalSpine : InternalManuscriptSpineTarget P comparison C}
    {classicalSpine : ClassicalManuscriptSpineTarget ctx structuredEq}
    {traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget spine internalSpine classicalSpine}
    {canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget spine internalSpine classicalSpine
        traceToDMgmEquivalence}
    {realizationComparison :
      RealizationComparisonTarget spine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence}
    (periodConjectureViaRealization :
      PeriodConjectureViaRealizationTarget spine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence realizationComparison) :
    firstPassStatement
        (canonicalDMgmEquivalence := canonicalDMgmEquivalence)
        (realizationComparison := realizationComparison) ↔
      (periodConjectureViaRealization.periodFaithfulnessTransportTarget ∧
        periodConjectureViaRealization.equivalenceWithClassicalStatementTarget) := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

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

/-- Project-native final Package 8 period package from the Layer D target-level owner route. -/
def finalPackage8PeriodPackage_ofLayerDTarget
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    (internalSpine : InternalManuscriptSpineTarget P comparison C)
    (classicalSpine : ClassicalManuscriptSpineTarget ctx target.structuredComparisonEquality)
    (traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget spine internalSpine classicalSpine)
    (canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget spine internalSpine classicalSpine
        traceToDMgmEquivalence)
    (target : LayerD.InternalRealizationFunctorTarget ctx) :
    PeriodConjectureViaRealizationTarget spine internalSpine classicalSpine
      traceToDMgmEquivalence canonicalDMgmEquivalence
      (RealizationComparisonTarget.ofLayerDTarget spine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence target) :=
  PeriodConjectureViaRealizationTarget.ofLayerDTarget spine internalSpine classicalSpine
    traceToDMgmEquivalence canonicalDMgmEquivalence target

/-- Project-native final Package 8 period package from the Layer D proof wrapper. -/
def finalPackage8PeriodPackage_ofLayerDData
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {target : LayerD.InternalRealizationFunctorTarget ctx}
    (internalSpine : InternalManuscriptSpineTarget P comparison C)
    (classicalSpine : ClassicalManuscriptSpineTarget ctx target.structuredComparisonEquality)
    (traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget spine internalSpine classicalSpine)
    (canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget spine internalSpine classicalSpine
        traceToDMgmEquivalence)
    (data : LayerD.InternalRealizationFunctorData ctx target) :
    PeriodConjectureViaRealizationTarget spine internalSpine classicalSpine
      traceToDMgmEquivalence canonicalDMgmEquivalence
      (RealizationComparisonTarget.ofLayerDData spine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence data) :=
  PeriodConjectureViaRealizationTarget.ofLayerDData spine internalSpine classicalSpine
    traceToDMgmEquivalence canonicalDMgmEquivalence data

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
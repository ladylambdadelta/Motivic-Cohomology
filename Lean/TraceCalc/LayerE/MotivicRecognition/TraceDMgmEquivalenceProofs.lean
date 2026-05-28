import TraceCalc.LayerE.MotivicRecognition.StableCompletionProofs
import TraceCalc.LayerE.MotivicRecognition.InfinityPiZeroProofs
import TraceCalc.LayerALegacy.Extensions.SyntacticTraceDMgmEquivalence

universe u v w x y z

namespace TraceCalc
namespace MotivicRecognition

open LayerB.RealObjects
open LayerB.RealObjects.RewriteCalculusSetup
open ClassicalPeriods
open CategoryInfra.SyntacticTraceDMgm

def concreteTraceToDMgmComparisonTarget (presentation : Type u) :
    TraceToDMgmComparisonTarget presentation :=
  TraceToDMgmComparisonTarget.syntactic presentation

def concreteTraceToDMgmComparisonData (presentation : Type u) :
    TraceToDMgmComparisonData (concreteTraceToDMgmComparisonTarget presentation) :=
  TraceToDMgmComparisonData.syntactic presentation

namespace CorePresentationEquivalenceTarget

def ofSyntacticTraceDMgmComparison
    {setup : RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (internal : InternalManuscriptSpineTarget P comparison C)
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq)
    (presentation : Type u) :
    CorePresentationEquivalenceTarget spine internal classical where
  corePresentationEquivalenceTarget :=
    (concreteTraceToDMgmComparisonTarget presentation).objectCompatibility ∧
      (concreteTraceToDMgmComparisonTarget presentation).homCompatibility
  corePresentationEquivalence_holds :=
    corePresentationCompatibilityWitness presentation
  identityOnGeneratingObjectsTarget :=
    (concreteTraceToDMgmComparisonTarget presentation).objectCompatibility
  identityOnGeneratingObjects_holds :=
    (concreteTraceToDMgmComparisonData presentation).objectCompatibilityWitness
  identityOnGeneratingMorphismsTarget :=
    (concreteTraceToDMgmComparisonTarget presentation).homCompatibility
  identityOnGeneratingMorphisms_holds :=
    (concreteTraceToDMgmComparisonData presentation).homCompatibilityWitness

end CorePresentationEquivalenceTarget

namespace CompletedPresentationEquivalenceTarget

def ofSyntacticTraceDMgmComparison
    {setup : RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (internal : InternalManuscriptSpineTarget P comparison C)
    (stableCompletion : StableAdditiveKaroubiCompletionTarget spine internal)
    (stableCompletionConstruction :
      TraceStableCompletionConstructionTarget spine internal stableCompletion)
    (completionUniversalProperty :
      TraceCompletionUniversalPropertyTarget spine internal stableCompletion
        stableCompletionConstruction)
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq)
    (corePresentationEquivalence :
      CorePresentationEquivalenceTarget spine internal classical)
    (presentation : Type u) :
    CompletedPresentationEquivalenceTarget spine internal stableCompletion
      stableCompletionConstruction completionUniversalProperty classical
      corePresentationEquivalence where
  completedPresentationEquivalenceTarget :=
    (concreteTraceToDMgmComparisonTarget presentation).objectCompatibility ∧
      (concreteTraceToDMgmComparisonTarget presentation).homCompatibility ∧
      (concreteTraceToDMgmComparisonTarget presentation).exactMonoidalCompatibility ∧
      (concreteTraceToDMgmComparisonTarget presentation).fullyFaithful ∧
      (concreteTraceToDMgmComparisonTarget presentation).essentiallySurjective
  completedPresentationEquivalence_holds :=
    canonicalCompletedPresentationComparisonWitness presentation
  completedPresentationFullFaithfulnessTarget :=
    (concreteTraceToDMgmComparisonTarget presentation).fullyFaithful
  completedPresentationFullFaithfulness_holds :=
    (concreteTraceToDMgmComparisonData presentation).fullyFaithfulWitness
  completedPresentationEssentialSurjectivityTarget :=
    (concreteTraceToDMgmComparisonTarget presentation).essentiallySurjective
  completedPresentationEssentialSurjectivity_holds :=
    (concreteTraceToDMgmComparisonData presentation).essentiallySurjectiveWitness
  exactSymmetricMonoidalExtensionTarget :=
    (concreteTraceToDMgmComparisonTarget presentation).exactMonoidalCompatibility
  exactSymmetricMonoidalExtension_holds :=
    (concreteTraceToDMgmComparisonData presentation).exactMonoidalCompatibilityWitness
  dualityCompatibilityTarget :=
    (concreteTraceToDMgmComparisonTarget presentation).dualityCompatibility
  dualityCompatibility_holds :=
    (concreteTraceToDMgmComparisonData presentation).dualityCompatibilityWitness

end CompletedPresentationEquivalenceTarget

theorem canonicalCompletedPresentationComparisonWitness (presentation : Type u) :
    (concreteTraceToDMgmComparisonTarget presentation).objectCompatibility ∧
      (concreteTraceToDMgmComparisonTarget presentation).homCompatibility ∧
      (concreteTraceToDMgmComparisonTarget presentation).exactMonoidalCompatibility ∧
      (concreteTraceToDMgmComparisonTarget presentation).fullyFaithful ∧
      (concreteTraceToDMgmComparisonTarget presentation).essentiallySurjective := by
  exact
    ⟨(concreteTraceToDMgmComparisonData presentation).objectCompatibilityWitness,
      (concreteTraceToDMgmComparisonData presentation).homCompatibilityWitness,
      (concreteTraceToDMgmComparisonData presentation).exactMonoidalCompatibilityWitness,
      (concreteTraceToDMgmComparisonData presentation).fullyFaithfulWitness,
      (concreteTraceToDMgmComparisonData presentation).essentiallySurjectiveWitness⟩

theorem closureEqualityComparisonWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (closureEquiv : PresentationAdmissibleClosureEquivalence ctx) :
    closureEquiv.closureComparisonTarget :=
  PresentationAdmissibleClosureEquivalence.closureComparison closureEquiv

theorem corePresentationCompatibilityWitness (presentation : Type u) :
    (concreteTraceToDMgmComparisonTarget presentation).objectCompatibility ∧
      (concreteTraceToDMgmComparisonTarget presentation).homCompatibility :=
  ⟨(concreteTraceToDMgmComparisonData presentation).objectCompatibilityWitness,
    (concreteTraceToDMgmComparisonData presentation).homCompatibilityWitness⟩

theorem exactMonoidalCompatibilityWitness (presentation : Type u) :
    (concreteTraceToDMgmComparisonTarget presentation).exactMonoidalCompatibility :=
  (concreteTraceToDMgmComparisonData presentation).exactMonoidalCompatibilityWitness

theorem dualityCompatibilityWitness (presentation : Type u) :
    (concreteTraceToDMgmComparisonTarget presentation).dualityCompatibility :=
  (concreteTraceToDMgmComparisonData presentation).dualityCompatibilityWitness

theorem homotopyCategoryCompatibilityWitness (presentation : Type u) :
    (concreteTraceToDMgmComparisonTarget presentation).homotopyCategoryCompatibility :=
  (concreteTraceToDMgmComparisonData presentation).homotopyCategoryCompatibilityWitness

namespace CanonicalTraceDMgmEquivalenceData

def ofSyntacticTraceDMgmComparison
    {setup : RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (internal : InternalManuscriptSpineTarget P comparison C)
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq)
    (stableCompletion : StableAdditiveKaroubiCompletionTarget spine internal)
    (stableCompletionConstruction :
      TraceStableCompletionConstructionTarget spine internal stableCompletion)
    (completionUniversalProperty :
      TraceCompletionUniversalPropertyTarget spine internal stableCompletion
        stableCompletionConstruction)
    (closureEquiv : PresentationAdmissibleClosureEquivalence ctx)
    (presentation : Type u) :
    CanonicalTraceDMgmEquivalenceData spine internal classical :=
  let corePresentationEquivalence :
      CorePresentationEquivalenceTarget spine internal classical :=
    CorePresentationEquivalenceTarget.ofSyntacticTraceDMgmComparison
      spine internal classical presentation
  let completedPresentationEquivalence :
      CompletedPresentationEquivalenceTarget spine internal stableCompletion
        stableCompletionConstruction completionUniversalProperty classical
        corePresentationEquivalence :=
    CompletedPresentationEquivalenceTarget.ofSyntacticTraceDMgmComparison
      spine internal stableCompletion stableCompletionConstruction
      completionUniversalProperty classical corePresentationEquivalence
      presentation
  CanonicalTraceDMgmEquivalenceData.ofCompletedPresentationAndPi0Shadow
    spine internal classical stableCompletion stableCompletionConstruction
    completionUniversalProperty corePresentationEquivalence
    completedPresentationEquivalence closureEquiv
    (syntacticInfinityToPi0Comparison presentation)

end CanonicalTraceDMgmEquivalenceData

namespace CanonicalTraceDMgmEquivalenceTheoremPackage

def ofSyntacticTraceDMgmComparison
    {setup : RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
    {internal : InternalManuscriptSpineTarget P comparison C}
    {classical : ClassicalManuscriptSpineTarget ctx structuredEq}
    (stableCompletion : StableAdditiveKaroubiCompletionTarget spine internal)
    (stableCompletionConstruction :
      TraceStableCompletionConstructionTarget spine internal stableCompletion)
    (completionUniversalProperty :
      TraceCompletionUniversalPropertyTarget spine internal stableCompletion
        stableCompletionConstruction)
    (closureEquiv : PresentationAdmissibleClosureEquivalence ctx)
    (presentation : Type u) :
    CanonicalTraceDMgmEquivalenceTheoremPackage
      (CanonicalTraceDMgmEquivalenceData.ofSyntacticTraceDMgmComparison
        spine internal classical stableCompletion stableCompletionConstruction
        completionUniversalProperty closureEquiv presentation) := by
  exact
    CanonicalTraceDMgmEquivalenceTheoremPackage.ofCanonicalData
      (CanonicalTraceDMgmEquivalenceData.ofSyntacticTraceDMgmComparison
        spine internal classical stableCompletion stableCompletionConstruction
        completionUniversalProperty closureEquiv presentation)

end CanonicalTraceDMgmEquivalenceTheoremPackage

namespace TraceCategoryEquivalentToDMgmQTarget

def ofSyntacticTraceDMgmComparison
    {setup : RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (internal : InternalManuscriptSpineTarget P comparison C)
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq)
    (stableCompletion : StableAdditiveKaroubiCompletionTarget spine internal)
    (stableCompletionConstruction :
      TraceStableCompletionConstructionTarget spine internal stableCompletion)
    (completionUniversalProperty :
      TraceCompletionUniversalPropertyTarget spine internal stableCompletion
        stableCompletionConstruction)
    (closureEquiv : PresentationAdmissibleClosureEquivalence ctx)
    (presentation : Type u) :
    TraceCategoryEquivalentToDMgmQTarget spine internal classical :=
  let corePresentationEquivalence :
      CorePresentationEquivalenceTarget spine internal classical :=
    CorePresentationEquivalenceTarget.ofSyntacticTraceDMgmComparison
      spine internal classical presentation
  let completedPresentationEquivalence :
      CompletedPresentationEquivalenceTarget spine internal stableCompletion
        stableCompletionConstruction completionUniversalProperty classical
        corePresentationEquivalence :=
    CompletedPresentationEquivalenceTarget.ofSyntacticTraceDMgmComparison
      spine internal stableCompletion stableCompletionConstruction
      completionUniversalProperty classical corePresentationEquivalence
      presentation
  TraceCategoryEquivalentToDMgmQTarget.ofCompletedPresentationAndPi0Shadow
    spine internal classical stableCompletion stableCompletionConstruction
    completionUniversalProperty
    corePresentationEquivalence
    completedPresentationEquivalence
    closureEquiv
    (syntacticInfinityToPi0Comparison presentation)

end TraceCategoryEquivalentToDMgmQTarget

def syntacticCanonicalDMgmEquivalenceTarget
    {setup : RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (internal : InternalManuscriptSpineTarget P comparison C)
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq)
    (stableCompletion : StableAdditiveKaroubiCompletionTarget spine internal)
    (stableCompletionConstruction :
      TraceStableCompletionConstructionTarget spine internal stableCompletion)
    (completionUniversalProperty :
      TraceCompletionUniversalPropertyTarget spine internal stableCompletion
        stableCompletionConstruction)
    (closureEquiv : PresentationAdmissibleClosureEquivalence ctx)
    (presentation : Type u) :
    CanonicalDMgmEquivalenceTarget spine internal classical
      (TraceCategoryEquivalentToDMgmQTarget.ofSyntacticTraceDMgmComparison
        spine internal classical stableCompletion stableCompletionConstruction
        completionUniversalProperty closureEquiv presentation) :=
  CanonicalDMgmEquivalenceTarget.ofTraceCategoryEquivalence
    spine internal classical
    (TraceCategoryEquivalentToDMgmQTarget.ofSyntacticTraceDMgmComparison
      spine internal classical stableCompletion stableCompletionConstruction
      completionUniversalProperty closureEquiv presentation)

end MotivicRecognition
end TraceCalc

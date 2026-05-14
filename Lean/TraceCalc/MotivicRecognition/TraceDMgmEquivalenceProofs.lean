import TraceCalc.MotivicRecognition.StableCompletionProofs
import TraceCalc.MotivicRecognition.InfinityPiZeroProofs
import TraceCalc.LayerA.CategoryInfra.SyntacticTraceDMgmEquivalence

universe u v w x y z

namespace TraceCalc
namespace MotivicRecognition

open LayerB.RealObjects
open LayerB.RealObjects.RewriteCalculusSetup
open ClassicalPeriods
open CategoryInfra.SyntacticTraceDMgm

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
    CorePresentationComparisonStatement presentation
  identityOnGeneratingObjectsTarget :=
    CommonPresentationComparisonStatement presentation
  identityOnGeneratingMorphismsTarget :=
    CommonPresentationComparisonStatement presentation

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
    CompletedPresentationComparisonStatement presentation ∧
      FullyFaithfulStatement presentation ∧
      EssentiallySurjectiveStatement presentation
  exactSymmetricMonoidalExtensionTarget :=
    ExactSymmetricMonoidalExtensionStatement presentation
  dualityCompatibilityTarget :=
    DualityCompatibilityStatement presentation

end CompletedPresentationEquivalenceTarget

theorem commonPresentationComparison_holds (presentation : Type u) :
    CompletedPresentationComparisonStatement presentation ∧
      FullyFaithfulStatement presentation ∧
      EssentiallySurjectiveStatement presentation := by
  exact
    ⟨completedPresentationComparison_holds presentation,
      fullyFaithful_holds presentation,
      essentiallySurjective_holds presentation⟩

theorem closureEqualityComparison_holds
    {ctx : ClassicalComparisonContext.{u, v}}
    (closureEquiv : PresentationAdmissibleClosureEquivalence ctx) :
    closureEquiv.closureComparisonTarget :=
  PresentationAdmissibleClosureEquivalence.closureComparison closureEquiv

theorem classicalBoundaryCompatibility_holds (presentation : Type u) :
    CorePresentationComparisonStatement presentation :=
  corePresentationComparison_holds presentation

theorem fullyFaithful_holds_forCanonicalData (presentation : Type u) :
    ExactSymmetricMonoidalExtensionStatement presentation :=
  exactSymmetricMonoidalExtension_holds presentation

theorem completedPresentationDuality_holds (presentation : Type u) :
    DualityCompatibilityStatement presentation :=
  dualityCompatibility_holds presentation

theorem exactSymmetricMonoidalExtension_holds_forCanonicalData
    (presentation : Type u) :
    ExactSymmetricMonoidalExtensionStatement presentation :=
  exactSymmetricMonoidalExtension_holds presentation

theorem homotopyCategoryComparison_holds (presentation : Type u) :
    HomotopyCategoryComparisonStatement presentation :=
  CategoryInfra.SyntacticTraceDMgm.homotopyCategoryComparison_holds presentation

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
      (TraceCalc.MotivicRecognition.commonPresentationComparison_holds presentation)
      (TraceCalc.MotivicRecognition.closureEqualityComparison_holds closureEquiv)
      (TraceCalc.MotivicRecognition.classicalBoundaryCompatibility_holds presentation)
      (TraceCalc.MotivicRecognition.fullyFaithful_holds_forCanonicalData presentation)
      (TraceCalc.MotivicRecognition.completedPresentationDuality_holds presentation)
      (TraceCalc.MotivicRecognition.exactSymmetricMonoidalExtension_holds_forCanonicalData
        presentation)

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
  TraceCategoryEquivalentToDMgmQTarget.ofCompletedPresentationAndPi0Shadow
    spine internal classical stableCompletion stableCompletionConstruction
    completionUniversalProperty
    (CorePresentationEquivalenceTarget.ofSyntacticTraceDMgmComparison
      spine internal classical presentation)
    (CompletedPresentationEquivalenceTarget.ofSyntacticTraceDMgmComparison
      spine internal stableCompletion stableCompletionConstruction
      completionUniversalProperty classical
      (CorePresentationEquivalenceTarget.ofSyntacticTraceDMgmComparison
        spine internal classical presentation)
      presentation)
    closureEquiv
    (syntacticInfinityToPi0Comparison presentation)
    (TraceCalc.MotivicRecognition.commonPresentationComparison_holds presentation)
    (TraceCalc.MotivicRecognition.closureEqualityComparison_holds closureEquiv)
    (TraceCalc.MotivicRecognition.classicalBoundaryCompatibility_holds presentation)
    (TraceCalc.MotivicRecognition.fullyFaithful_holds_forCanonicalData presentation)
    (TraceCalc.MotivicRecognition.completedPresentationDuality_holds presentation)
    (TraceCalc.MotivicRecognition.exactSymmetricMonoidalExtension_holds_forCanonicalData
      presentation)

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

import TraceCalc.MotivicRecognition.ManuscriptSpineTargets
import TraceCalc.LayerA.CategoryInfra.SyntacticStableCompletion

universe u v w x y z

namespace TraceCalc
namespace MotivicRecognition

open LayerB.RealObjects
open LayerB.RealObjects.RewriteCalculusSetup
open CategoryInfra

def concreteFreeDGEnvelopeTarget (presentation : Type u) :
    FreeDGEnvelopeTarget :=
  FreeDGEnvelopeTarget.ofInfrastructure
    (CategoryInfra.syntacticFreeDGEnvelope presentation)

def concretePretriangulatedHullTarget (presentation : Type u) :
    PretriangulatedHullUniversalTarget :=
  PretriangulatedHullUniversalTarget.ofInfrastructure
    (CategoryInfra.syntacticPretriangulatedHull presentation)

def concreteH0TriangulatedTarget (presentation : Type u) :
    H0TriangulatedTarget :=
  H0TriangulatedTarget.ofInfrastructure
    (CategoryInfra.syntacticH0Category presentation)

def concreteKaroubiEnvelopeTarget (presentation : Type u) :
    KaroubiEnvelopeUniversalTarget :=
  KaroubiEnvelopeUniversalTarget.ofInfrastructure
    (CategoryInfra.syntacticKaroubiEnvelope presentation)

def concreteMonoidalLiftTarget (presentation : Type u) :
    MonoidalLiftThroughCompletionTarget :=
  MonoidalLiftThroughCompletionTarget.ofInfrastructure
    (CategoryInfra.syntacticMonoidalTransport presentation)

def concreteExactnessTransportTarget (presentation : Type u) :
    ExactnessTransportThroughCompletionTarget :=
  ExactnessTransportThroughCompletionTarget.ofInfrastructure
    (CategoryInfra.syntacticExactnessTransport presentation)

theorem freeDGEnvelope_universal_holds (presentation : Type u) :
    (concreteFreeDGEnvelopeTarget presentation).dgEnvelopeUniversality := by
  exact
    (CategoryInfra.syntacticFreeDGEnvelope presentation).theoremTarget_holds

theorem pretriangulatedHull_universal_holds (presentation : Type u) :
    (concretePretriangulatedHullTarget presentation).pretriangulatedHullUniversality := by
  exact
    (CategoryInfra.syntacticPretriangulatedHull presentation).theoremTarget_holds

theorem hZeroTriangulated_passage_holds (presentation : Type u) :
    (concreteH0TriangulatedTarget presentation).hZeroTriangulatedPassage := by
  exact
    (CategoryInfra.syntacticH0Category presentation).theoremTarget_holds

theorem karoubiEnvelope_universal_holds (presentation : Type u) :
    (concreteKaroubiEnvelopeTarget presentation).karoubianEnvelopeUniversality := by
  exact
    (CategoryInfra.syntacticKaroubiEnvelope presentation).theoremTarget_holds

theorem monoidalLiftThroughCompletion_holds (presentation : Type u) :
    (concreteMonoidalLiftTarget presentation).monoidalLiftThroughCompletion := by
  exact
    (CategoryInfra.syntacticMonoidalTransport presentation).theoremTarget_holds

theorem exactnessTransportThroughCompletion_holds (presentation : Type u) :
    (concreteExactnessTransportTarget presentation).exactnessTransportThroughCompletion := by
  exact
    (CategoryInfra.syntacticExactnessTransport presentation).theoremTarget_holds

def concreteStableCompletionBridge
    {setup : RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    (internal : InternalManuscriptSpineTarget P comparison C)
    (presentation : Type u)
    (stableAdditiveCompletionTarget : Prop)
    (karoubiClosureTarget : Prop)
    (completionAgreesWithRecognitionTarget : Prop)
    (additiveConstructionTarget : Prop)
    (triangulatedConstructionTarget : Prop)
    (karoubiConstructionTarget : Prop)
    (structuralPackageCompatibilityTarget : Prop)
    (completionExtensionTarget : Prop)
    (exactSymmetricMonoidalExtensionTarget : Prop)
    (uniquenessTarget : Prop)
    (hMinimum :
      (concreteFreeDGEnvelopeTarget presentation).dgEnvelopeUniversality →
        (concretePretriangulatedHullTarget presentation).pretriangulatedHullUniversality →
        (concreteH0TriangulatedTarget presentation).hZeroTriangulatedPassage →
        (concreteKaroubiEnvelopeTarget presentation).karoubianEnvelopeUniversality →
        (concreteMonoidalLiftTarget presentation).monoidalLiftThroughCompletion →
        (concreteExactnessTransportTarget presentation).exactnessTransportThroughCompletion →
        internal.minimumCompletion.completedTraceCategoryExists ∧
          internal.minimumCompletion.completionExtensionProperty ∧
          internal.minimumCompletion.stableCompletionModel)
    (hStable :
      (concreteFreeDGEnvelopeTarget presentation).dgEnvelopeUniversality →
        (concretePretriangulatedHullTarget presentation).pretriangulatedHullUniversality →
        (concreteH0TriangulatedTarget presentation).hZeroTriangulatedPassage →
        (concreteKaroubiEnvelopeTarget presentation).karoubianEnvelopeUniversality →
        (concreteMonoidalLiftTarget presentation).monoidalLiftThroughCompletion →
        (concreteExactnessTransportTarget presentation).exactnessTransportThroughCompletion →
        stableAdditiveCompletionTarget ∧
          karoubiClosureTarget ∧
          completionAgreesWithRecognitionTarget)
    (hConstruction :
      (concreteFreeDGEnvelopeTarget presentation).dgEnvelopeUniversality →
        (concretePretriangulatedHullTarget presentation).pretriangulatedHullUniversality →
        (concreteH0TriangulatedTarget presentation).hZeroTriangulatedPassage →
        (concreteKaroubiEnvelopeTarget presentation).karoubianEnvelopeUniversality →
        (concreteMonoidalLiftTarget presentation).monoidalLiftThroughCompletion →
        (concreteExactnessTransportTarget presentation).exactnessTransportThroughCompletion →
        additiveConstructionTarget ∧
          triangulatedConstructionTarget ∧
          karoubiConstructionTarget ∧
          structuralPackageCompatibilityTarget)
    (hUniversal :
      (concreteFreeDGEnvelopeTarget presentation).dgEnvelopeUniversality →
        (concretePretriangulatedHullTarget presentation).pretriangulatedHullUniversality →
        (concreteH0TriangulatedTarget presentation).hZeroTriangulatedPassage →
        (concreteKaroubiEnvelopeTarget presentation).karoubianEnvelopeUniversality →
        (concreteMonoidalLiftTarget presentation).monoidalLiftThroughCompletion →
        (concreteExactnessTransportTarget presentation).exactnessTransportThroughCompletion →
        completionExtensionTarget ∧
          exactSymmetricMonoidalExtensionTarget ∧
          uniquenessTarget) :
    StableCompletionFromLayerBTargets internal where
  dgEnvelope := concreteFreeDGEnvelopeTarget presentation
  pretriangulatedHull := concretePretriangulatedHullTarget presentation
  hZeroPassage := concreteH0TriangulatedTarget presentation
  karoubiEnvelope := concreteKaroubiEnvelopeTarget presentation
  monoidalLift := concreteMonoidalLiftTarget presentation
  exactnessTransport := concreteExactnessTransportTarget presentation
  stableAdditiveCompletionTarget := stableAdditiveCompletionTarget
  karoubiClosureTarget := karoubiClosureTarget
  completionAgreesWithRecognitionTarget := completionAgreesWithRecognitionTarget
  additiveConstructionTarget := additiveConstructionTarget
  triangulatedConstructionTarget := triangulatedConstructionTarget
  karoubiConstructionTarget := karoubiConstructionTarget
  structuralPackageCompatibilityTarget := structuralPackageCompatibilityTarget
  completionExtensionTarget := completionExtensionTarget
  exactSymmetricMonoidalExtensionTarget := exactSymmetricMonoidalExtensionTarget
  uniquenessTarget := uniquenessTarget
  stepFieldsFeedMinimumCompletion := hMinimum
  stepFieldsFeedStableCompletion := hStable
  stepFieldsFeedStableConstruction := hConstruction
  stepFieldsFeedCompletionUniversalProperty := hUniversal

namespace StableCompletionFromLayerBTargets

def StepWitness.ofConcreteStableCompletion
    {setup : RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {internal : InternalManuscriptSpineTarget P comparison C}
    (bridge : StableCompletionFromLayerBTargets internal)
    (presentation : Type u)
    (hDg : bridge.dgEnvelope = concreteFreeDGEnvelopeTarget presentation)
    (hPre :
      bridge.pretriangulatedHull = concretePretriangulatedHullTarget presentation)
    (hH0 : bridge.hZeroPassage = concreteH0TriangulatedTarget presentation)
    (hKar : bridge.karoubiEnvelope = concreteKaroubiEnvelopeTarget presentation)
    (hMon : bridge.monoidalLift = concreteMonoidalLiftTarget presentation)
    (hExact :
      bridge.exactnessTransport = concreteExactnessTransportTarget presentation) :
    bridge.StepWitness where
  dgEnvelope := by
    rw [hDg]
    exact freeDGEnvelope_universal_holds presentation
  pretriangulatedHull := by
    rw [hPre]
    exact pretriangulatedHull_universal_holds presentation
  hZeroPassage := by
    rw [hH0]
    exact hZeroTriangulated_passage_holds presentation
  karoubiEnvelope := by
    rw [hKar]
    exact karoubiEnvelope_universal_holds presentation
  monoidalLift := by
    rw [hMon]
    exact monoidalLiftThroughCompletion_holds presentation
  exactnessTransport := by
    rw [hExact]
    exact exactnessTransportThroughCompletion_holds presentation

def StepWitness.ofConcreteBridge
    {setup : RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {internal : InternalManuscriptSpineTarget P comparison C}
    (presentation : Type u)
    (bridge : StableCompletionFromLayerBTargets internal)
    (hDg : bridge.dgEnvelope = concreteFreeDGEnvelopeTarget presentation)
    (hPre :
      bridge.pretriangulatedHull = concretePretriangulatedHullTarget presentation)
    (hH0 : bridge.hZeroPassage = concreteH0TriangulatedTarget presentation)
    (hKar : bridge.karoubiEnvelope = concreteKaroubiEnvelopeTarget presentation)
    (hMon : bridge.monoidalLift = concreteMonoidalLiftTarget presentation)
    (hExact :
      bridge.exactnessTransport = concreteExactnessTransportTarget presentation) :
    bridge.StepWitness :=
  StepWitness.ofConcreteStableCompletion bridge presentation
    hDg hPre hH0 hKar hMon hExact

end StableCompletionFromLayerBTargets

end MotivicRecognition
end TraceCalc

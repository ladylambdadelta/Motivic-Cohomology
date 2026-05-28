import TraceCalc.LayerE.MotivicRecognition.ManuscriptSpineTargets
import TraceCalc.LayerA.CategoryInfra.SyntacticStableCompletion

universe u v w x y z

namespace TraceCalc
namespace MotivicRecognition

open LayerB.RealObjects
open LayerB.RealObjects.RewriteCalculusSetup
open CategoryInfra

def concreteStableCompletionPackage (presentation : Type u)
    [PresentationQuiver presentation] :
    CategoryInfra.StableCompletionConstructionTarget presentation :=
  CategoryInfra.StableCompletionConstructionTarget.syntactic presentation

def concreteStableCompletionPackageData (presentation : Type u)
    [PresentationQuiver presentation] :
    CategoryInfra.StableCompletionConstructionData
      (concreteStableCompletionPackage presentation) :=
  CategoryInfra.StableCompletionConstructionData.syntactic presentation

def concreteStableCompletionFieldTargets (presentation : Type u)
    [PresentationQuiver presentation]
    [MonoidalPresentation presentation] :
    StableCompletionFieldTargets :=
  StableCompletionFieldTargets.ofStableCompletionPackages
    (concreteStableCompletionPackageData presentation)
    (StableCompletionConstructionTarget.monoidalTransport presentation)

def concreteFreeDGEnvelopeTarget (presentation : Type u)
    [PresentationQuiver presentation]
    [MonoidalPresentation presentation] :
    FreeDGEnvelopeTarget :=
  (concreteStableCompletionFieldTargets presentation).dgEnvelope

def concretePretriangulatedHullTarget (presentation : Type u)
    [PresentationQuiver presentation]
    [MonoidalPresentation presentation] :
    PretriangulatedHullUniversalTarget :=
  (concreteStableCompletionFieldTargets presentation).pretriangulatedHull

def concreteH0TriangulatedTarget (presentation : Type u)
    [PresentationQuiver presentation]
    [MonoidalPresentation presentation] :
    H0TriangulatedTarget :=
  (concreteStableCompletionFieldTargets presentation).hZeroPassage

def concreteKaroubiEnvelopeTarget (presentation : Type u)
    [PresentationQuiver presentation]
    [MonoidalPresentation presentation] :
    KaroubiEnvelopeUniversalTarget :=
  (concreteStableCompletionFieldTargets presentation).karoubiEnvelope

def concreteMonoidalLiftTarget (presentation : Type u)
  [PresentationQuiver presentation]
    [MonoidalPresentation presentation] :
    MonoidalLiftThroughCompletionTarget :=
  (concreteStableCompletionFieldTargets presentation).monoidalLift

def concreteExactnessTransportTarget (presentation : Type u)
  [PresentationQuiver presentation]
    [MonoidalPresentation presentation] :
    ExactnessTransportThroughCompletionTarget :=
  (concreteStableCompletionFieldTargets presentation).exactnessTransport

theorem freeDGEnvelope_universal_holds (presentation : Type u)
  [PresentationQuiver presentation]
  [MonoidalPresentation presentation] :
    (concreteFreeDGEnvelopeTarget presentation).dgEnvelopeUniversality := by
  exact ⟨⟨(concreteStableCompletionPackage presentation).freeDG⟩,
    (concreteStableCompletionPackageData presentation).freeDGUniversalPropertyWitness⟩

theorem pretriangulatedHull_universal_holds (presentation : Type u)
  [PresentationQuiver presentation]
  [MonoidalPresentation presentation] :
    (concretePretriangulatedHullTarget presentation).pretriangulatedHullUniversality := by
  exact ⟨⟨(concreteStableCompletionPackage presentation).pretriangulatedHull⟩,
    (concreteStableCompletionPackageData presentation).pretriangulatedClosureData.shiftClosureWitness,
    (concreteStableCompletionPackageData presentation).pretriangulatedClosureData.coneClosureWitness,
    (concreteStableCompletionPackageData presentation).pretriangulatedUniversalPropertyWitness⟩

theorem hZeroTriangulated_passage_holds (presentation : Type u)
  [PresentationQuiver presentation]
  [MonoidalPresentation presentation] :
    (concreteH0TriangulatedTarget presentation).hZeroTriangulatedPassage := by
  exact ⟨⟨(concreteStableCompletionPackage presentation).homotopyCategory⟩,
    ⟨(concreteStableCompletionPackage presentation).homotopyCategory.distinguishedTriangles⟩,
    ⟨(concreteStableCompletionPackage presentation).homotopyCategory.triangulatedAxioms⟩,
    ⟨(concreteStableCompletionPackage presentation).homotopyCategory.localizationAtAcyclics⟩⟩

theorem karoubiEnvelope_universal_holds (presentation : Type u)
  [PresentationQuiver presentation]
  [MonoidalPresentation presentation] :
    (concreteKaroubiEnvelopeTarget presentation).karoubianEnvelopeUniversality := by
  change Nonempty (StableCompletionConstructionTarget.karoubiCompletion
      (concreteStableCompletionPackage presentation)) ∧
    (concreteStableCompletionPackage presentation).idempotentSplitting ∧
      (concreteStableCompletionPackage presentation).karoubiUniversalProperty
  exact ⟨KaroubiEnvelopeExistenceTarget.ofInfrastructure_holds
      (concreteStableCompletionPackage presentation).karoubiEnvelope,
    (concreteStableCompletionPackageData presentation).idempotentSplittingWitness,
    (concreteStableCompletionPackageData presentation).karoubiUniversalPropertyWitness⟩

theorem monoidalLiftThroughCompletion_holds (presentation : Type u)
  [PresentationQuiver presentation]
    [MonoidalPresentation presentation] :
    (concreteMonoidalLiftTarget presentation).monoidalLiftThroughCompletion := by
  let monoidalTransport :=
    StableCompletionConstructionTarget.monoidalTransport presentation
  exact ⟨monoidalTransport.throughDGEnvelope_holds,
    monoidalTransport.throughPretriangulatedHull_holds,
    monoidalTransport.throughH0_holds,
    monoidalTransport.throughKaroubiEnvelope_holds,
    StableCompletionConstructionData.monoidalCoherenceWitness presentation
      (concreteStableCompletionPackageData presentation)⟩

theorem exactnessTransportThroughCompletion_holds (presentation : Type u)
  [PresentationQuiver presentation]
    [MonoidalPresentation presentation] :
    (concreteExactnessTransportTarget presentation).exactnessTransportThroughCompletion := by
  exact ⟨(concreteStableCompletionPackageData presentation).exactnessTransportData.laws.exactnessForDGEnvelope,
    (concreteStableCompletionPackageData presentation).exactnessTransportData.laws.exactnessForPretriangulatedHull,
    ⟨(concreteStableCompletionPackage presentation).exactnessTransport.exactnessForH0⟩,
    (concreteStableCompletionPackage presentation).exactnessTransport.exactnessForKaroubiCompletion,
    ⟨(concreteStableCompletionPackage presentation).exactnessTransport.distinguishedTriangleTransport⟩⟩

structure ConcreteStepTheorems
    {setup : RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {internal : InternalManuscriptSpineTarget P comparison C}
    (presentation : Type u)
    [PresentationQuiver presentation]
    [MonoidalPresentation presentation] where
  dgEnvelope :
    (concreteFreeDGEnvelopeTarget presentation).dgEnvelopeUniversality
  pretriangulatedHull :
    (concretePretriangulatedHullTarget presentation).pretriangulatedHullUniversality
  hZeroPassage :
    (concreteH0TriangulatedTarget presentation).hZeroTriangulatedPassage
  karoubiEnvelope :
    (concreteKaroubiEnvelopeTarget presentation).karoubianEnvelopeUniversality
  monoidalLift :
    (concreteMonoidalLiftTarget presentation).monoidalLiftThroughCompletion
  exactnessTransport :
    (concreteExactnessTransportTarget presentation).exactnessTransportThroughCompletion

namespace ConcreteStepTheorems

def ofPresentation
    {setup : RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {internal : InternalManuscriptSpineTarget P comparison C}
    (presentation : Type u)
    [PresentationQuiver presentation]
    [MonoidalPresentation presentation] :
    ConcreteStepTheorems (internal := internal) presentation where
  dgEnvelope := freeDGEnvelope_universal_holds presentation
  pretriangulatedHull := pretriangulatedHull_universal_holds presentation
  hZeroPassage := hZeroTriangulated_passage_holds presentation
  karoubiEnvelope := karoubiEnvelope_universal_holds presentation
  monoidalLift := monoidalLiftThroughCompletion_holds presentation
  exactnessTransport := exactnessTransportThroughCompletion_holds presentation

end ConcreteStepTheorems

structure ConcreteStableCompletionBridgePackage
    {setup : RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    (internal : InternalManuscriptSpineTarget P comparison C)
    (presentation : Type u)
    [PresentationQuiver presentation]
    [MonoidalPresentation presentation] where
  bridge : StableCompletionFromLayerBTargets internal
  dgEnvelope_eq :
    bridge.dgEnvelope = concreteFreeDGEnvelopeTarget presentation
  pretriangulatedHull_eq :
    bridge.pretriangulatedHull = concretePretriangulatedHullTarget presentation
  hZeroPassage_eq :
    bridge.hZeroPassage = concreteH0TriangulatedTarget presentation
  karoubiEnvelope_eq :
    bridge.karoubiEnvelope = concreteKaroubiEnvelopeTarget presentation
  monoidalLift_eq :
    bridge.monoidalLift = concreteMonoidalLiftTarget presentation
  exactnessTransport_eq :
    bridge.exactnessTransport = concreteExactnessTransportTarget presentation

namespace ConcreteStableCompletionBridgePackage

def ofBridge
    {setup : RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {internal : InternalManuscriptSpineTarget P comparison C}
    {presentation : Type u}
    [PresentationQuiver presentation]
    [MonoidalPresentation presentation]
    (bridge : StableCompletionFromLayerBTargets internal)
    (dgEnvelope_eq :
      bridge.dgEnvelope = concreteFreeDGEnvelopeTarget presentation)
    (pretriangulatedHull_eq :
      bridge.pretriangulatedHull = concretePretriangulatedHullTarget presentation)
    (hZeroPassage_eq :
      bridge.hZeroPassage = concreteH0TriangulatedTarget presentation)
    (karoubiEnvelope_eq :
      bridge.karoubiEnvelope = concreteKaroubiEnvelopeTarget presentation)
    (monoidalLift_eq :
      bridge.monoidalLift = concreteMonoidalLiftTarget presentation)
    (exactnessTransport_eq :
      bridge.exactnessTransport = concreteExactnessTransportTarget presentation) :
    ConcreteStableCompletionBridgePackage internal presentation where
  bridge := bridge
  dgEnvelope_eq := dgEnvelope_eq
  pretriangulatedHull_eq := pretriangulatedHull_eq
  hZeroPassage_eq := hZeroPassage_eq
  karoubiEnvelope_eq := karoubiEnvelope_eq
  monoidalLift_eq := monoidalLift_eq
  exactnessTransport_eq := exactnessTransport_eq

def theoremPackage
    {setup : RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {internal : InternalManuscriptSpineTarget P comparison C}
    {presentation : Type u}
    [PresentationQuiver presentation]
    [MonoidalPresentation presentation]
    (package : ConcreteStableCompletionBridgePackage internal presentation) :
    package.bridge.TheoremPackage :=
  StableCompletionFromLayerBTargets.TheoremPackage.ofStepFields package.bridge
    (by
      rw [package.dgEnvelope_eq]
      exact freeDGEnvelope_universal_holds presentation)
    (by
      rw [package.pretriangulatedHull_eq]
      exact pretriangulatedHull_universal_holds presentation)
    (by
      rw [package.hZeroPassage_eq]
      exact hZeroTriangulated_passage_holds presentation)
    (by
      rw [package.karoubiEnvelope_eq]
      exact karoubiEnvelope_universal_holds presentation)
    (by
      rw [package.monoidalLift_eq]
      exact monoidalLiftThroughCompletion_holds presentation)
    (by
      rw [package.exactnessTransport_eq]
      exact exactnessTransportThroughCompletion_holds presentation)

def toStableAdditiveKaroubiCompletionTarget
    {setup : RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {internal : InternalManuscriptSpineTarget P comparison C}
    {presentation : Type u}
    [PresentationQuiver presentation]
    [MonoidalPresentation presentation]
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (package : ConcreteStableCompletionBridgePackage internal presentation) :
    StableAdditiveKaroubiCompletionTarget spine internal :=
  StableCompletionFromLayerBTargets.toStableAdditiveKaroubiCompletionTarget
    spine internal package.bridge package.theoremPackage

def toTraceStableCompletionConstructionTarget
    {setup : RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {internal : InternalManuscriptSpineTarget P comparison C}
    {presentation : Type u}
    [PresentationQuiver presentation]
    [MonoidalPresentation presentation]
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (package : ConcreteStableCompletionBridgePackage internal presentation)
    (stableCompletion : StableAdditiveKaroubiCompletionTarget spine internal) :
    TraceStableCompletionConstructionTarget spine internal stableCompletion :=
  StableCompletionFromLayerBTargets.toTraceStableCompletionConstructionTarget
    spine internal package.bridge package.theoremPackage stableCompletion

def toTraceCompletionUniversalPropertyTarget
    {setup : RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {internal : InternalManuscriptSpineTarget P comparison C}
    {presentation : Type u}
    [PresentationQuiver presentation]
    [MonoidalPresentation presentation]
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (package : ConcreteStableCompletionBridgePackage internal presentation)
    (stableCompletion : StableAdditiveKaroubiCompletionTarget spine internal)
    (construction : TraceStableCompletionConstructionTarget spine internal stableCompletion) :
    TraceCompletionUniversalPropertyTarget spine internal stableCompletion construction :=
  StableCompletionFromLayerBTargets.toTraceCompletionUniversalPropertyTarget
    spine internal package.bridge package.theoremPackage stableCompletion
    construction

end ConcreteStableCompletionBridgePackage

structure ConcreteStableCompletionData
    {setup : RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    (internal : InternalManuscriptSpineTarget P comparison C)
    (presentation : Type u)
    [PresentationQuiver presentation]
    [MonoidalPresentation presentation] where
  stableAdditiveCompletionTarget : Prop
  karoubiClosureTarget : Prop
  completionAgreesWithRecognitionTarget : Prop
  additiveConstructionTarget : Prop
  triangulatedConstructionTarget : Prop
  karoubiConstructionTarget : Prop
  structuralPackageCompatibilityTarget : Prop
  completionExtensionTarget : Prop
  exactSymmetricMonoidalExtensionTarget : Prop
  uniquenessTarget : Prop
  minimumCompletion :
    internal.minimumCompletion.completedTraceCategoryExists ∧
      internal.minimumCompletion.completionExtensionProperty ∧
      internal.minimumCompletion.stableCompletionModel
  stableCompletion :
    stableAdditiveCompletionTarget ∧
      karoubiClosureTarget ∧
      completionAgreesWithRecognitionTarget
  construction :
    additiveConstructionTarget ∧
      triangulatedConstructionTarget ∧
      karoubiConstructionTarget ∧
      structuralPackageCompatibilityTarget
  universalProperty :
    completionExtensionTarget ∧
      exactSymmetricMonoidalExtensionTarget ∧
      uniquenessTarget

namespace ConcreteStableCompletionData

def fieldTargets
    {setup : RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {internal : InternalManuscriptSpineTarget P comparison C}
    {presentation : Type u}
    [PresentationQuiver presentation]
    [MonoidalPresentation presentation]
    (_data : ConcreteStableCompletionData internal presentation) :
    StableCompletionFieldTargets :=
  concreteStableCompletionFieldTargets presentation

def stepTheorems
    {setup : RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {internal : InternalManuscriptSpineTarget P comparison C}
    {presentation : Type u}
    [PresentationQuiver presentation]
    [MonoidalPresentation presentation]
    (_data : ConcreteStableCompletionData internal presentation) :
    ConcreteStepTheorems (internal := internal) presentation :=
  ConcreteStepTheorems.ofPresentation (internal := internal) presentation

def minimumCompletionConsequencesTarget
    {setup : RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {internal : InternalManuscriptSpineTarget P comparison C}
    {presentation : Type u}
    [PresentationQuiver presentation]
    [MonoidalPresentation presentation]
    (data : ConcreteStableCompletionData internal presentation) :
    MinimumCompletionConsequencesTarget :=
  MinimumCompletionConsequencesTarget.ofMinimumCompletionTarget
    { completedTraceCategoryExists := data.minimumCompletion.1
      completionExtensionProperty := data.minimumCompletion.2.1
      stableCompletionModel := data.minimumCompletion.2.2 }

def minimumCompletionConstructionTarget
    {setup : RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {internal : InternalManuscriptSpineTarget P comparison C}
    {presentation : Type u}
    [PresentationQuiver presentation]
    [MonoidalPresentation presentation]
    (data : ConcreteStableCompletionData internal presentation) :
    MinimumCompletionConstructionTarget :=
  MinimumCompletionConstructionTarget.ofStableCompletionFieldTargets
    data.fieldTargets
    (fun _ _ _ _ _ _ => data.minimumCompletionConsequencesTarget)

def minimumCompletionTarget
    {setup : RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {internal : InternalManuscriptSpineTarget P comparison C}
    {presentation : Type u}
    [PresentationQuiver presentation]
    [MonoidalPresentation presentation]
    (data : ConcreteStableCompletionData internal presentation) :
    MinimumCompletionTarget :=
  let steps := data.stepTheorems
  data.minimumCompletionConstructionTarget.toMinimumCompletionTarget
    ⟨steps.dgEnvelope,
      ⟨steps.pretriangulatedHull,
        ⟨steps.hZeroPassage,
          ⟨steps.karoubiEnvelope,
            ⟨steps.monoidalLift,
              steps.exactnessTransport⟩⟩⟩⟩⟩

def bridgePackage
    {setup : RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {internal : InternalManuscriptSpineTarget P comparison C}
    {presentation : Type u}
    [PresentationQuiver presentation]
    [MonoidalPresentation presentation]
    (data : ConcreteStableCompletionData internal presentation) :
    ConcreteStableCompletionBridgePackage internal presentation :=
  let bridge : StableCompletionFromLayerBTargets internal := {
    dgEnvelope := concreteFreeDGEnvelopeTarget presentation
    pretriangulatedHull := concretePretriangulatedHullTarget presentation
    hZeroPassage := concreteH0TriangulatedTarget presentation
    karoubiEnvelope := concreteKaroubiEnvelopeTarget presentation
    monoidalLift := concreteMonoidalLiftTarget presentation
    exactnessTransport := concreteExactnessTransportTarget presentation
    stableAdditiveCompletionTarget := data.stableAdditiveCompletionTarget
    karoubiClosureTarget := data.karoubiClosureTarget
    completionAgreesWithRecognitionTarget := data.completionAgreesWithRecognitionTarget
    additiveConstructionTarget := data.additiveConstructionTarget
    triangulatedConstructionTarget := data.triangulatedConstructionTarget
    karoubiConstructionTarget := data.karoubiConstructionTarget
    structuralPackageCompatibilityTarget := data.structuralPackageCompatibilityTarget
    completionExtensionTarget := data.completionExtensionTarget
    exactSymmetricMonoidalExtensionTarget :=
      data.exactSymmetricMonoidalExtensionTarget
    uniquenessTarget := data.uniquenessTarget
    stepFieldsFeedMinimumCompletion := fun _ _ _ _ _ _ => data.minimumCompletion
    stepFieldsFeedStableCompletion := fun _ _ _ _ _ _ => data.stableCompletion
    stepFieldsFeedStableConstruction := fun _ _ _ _ _ _ => data.construction
    stepFieldsFeedCompletionUniversalProperty :=
      fun _ _ _ _ _ _ => data.universalProperty }
  ConcreteStableCompletionBridgePackage.ofBridge bridge rfl rfl rfl rfl rfl rfl

def toStableAdditiveKaroubiCompletionTarget
    {setup : RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {internal : InternalManuscriptSpineTarget P comparison C}
    {presentation : Type u}
    [PresentationQuiver presentation]
    [MonoidalPresentation presentation]
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (data : ConcreteStableCompletionData internal presentation) :
    StableAdditiveKaroubiCompletionTarget spine internal :=
  let package := data.bridgePackage
  package.toStableAdditiveKaroubiCompletionTarget spine

def toTraceStableCompletionConstructionTarget
    {setup : RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {internal : InternalManuscriptSpineTarget P comparison C}
    {presentation : Type u}
    [PresentationQuiver presentation]
    [MonoidalPresentation presentation]
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (data : ConcreteStableCompletionData internal presentation) :
    TraceStableCompletionConstructionTarget spine internal
      (data.toStableAdditiveKaroubiCompletionTarget spine) :=
  let package := data.bridgePackage
  package.toTraceStableCompletionConstructionTarget spine
    (data.toStableAdditiveKaroubiCompletionTarget spine)

def toTraceCompletionUniversalPropertyTarget
    {setup : RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {internal : InternalManuscriptSpineTarget P comparison C}
    {presentation : Type u}
    [PresentationQuiver presentation]
    [MonoidalPresentation presentation]
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (data : ConcreteStableCompletionData internal presentation) :
    TraceCompletionUniversalPropertyTarget spine internal
      (data.toStableAdditiveKaroubiCompletionTarget spine)
      (data.toTraceStableCompletionConstructionTarget spine) :=
  let package := data.bridgePackage
  package.toTraceCompletionUniversalPropertyTarget spine
    (data.toStableAdditiveKaroubiCompletionTarget spine)
    (data.toTraceStableCompletionConstructionTarget spine)

end ConcreteStableCompletionData

def concreteStableCompletionData
    {setup : RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    (internal : InternalManuscriptSpineTarget P comparison C)
    (presentation : Type u)
    [PresentationQuiver presentation]
    [MonoidalPresentation presentation]
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
    ConcreteStableCompletionData internal presentation where
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
  minimumCompletion := hMinimum
    (freeDGEnvelope_universal_holds presentation)
    (pretriangulatedHull_universal_holds presentation)
    (hZeroTriangulated_passage_holds presentation)
    (karoubiEnvelope_universal_holds presentation)
    (monoidalLiftThroughCompletion_holds presentation)
    (exactnessTransportThroughCompletion_holds presentation)
  stableCompletion := hStable
    (freeDGEnvelope_universal_holds presentation)
    (pretriangulatedHull_universal_holds presentation)
    (hZeroTriangulated_passage_holds presentation)
    (karoubiEnvelope_universal_holds presentation)
    (monoidalLiftThroughCompletion_holds presentation)
    (exactnessTransportThroughCompletion_holds presentation)
  construction := hConstruction
    (freeDGEnvelope_universal_holds presentation)
    (pretriangulatedHull_universal_holds presentation)
    (hZeroTriangulated_passage_holds presentation)
    (karoubiEnvelope_universal_holds presentation)
    (monoidalLiftThroughCompletion_holds presentation)
    (exactnessTransportThroughCompletion_holds presentation)
  universalProperty := hUniversal
    (freeDGEnvelope_universal_holds presentation)
    (pretriangulatedHull_universal_holds presentation)
    (hZeroTriangulated_passage_holds presentation)
    (karoubiEnvelope_universal_holds presentation)
    (monoidalLiftThroughCompletion_holds presentation)
    (exactnessTransportThroughCompletion_holds presentation)

def concreteStableCompletionBridgePackage
    {setup : RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    (internal : InternalManuscriptSpineTarget P comparison C)
    (presentation : Type u)
    [PresentationQuiver presentation]
    [MonoidalPresentation presentation]
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
    ConcreteStableCompletionBridgePackage internal presentation :=
  (concreteStableCompletionData internal presentation
    stableAdditiveCompletionTarget karoubiClosureTarget
    completionAgreesWithRecognitionTarget additiveConstructionTarget
    triangulatedConstructionTarget karoubiConstructionTarget
    structuralPackageCompatibilityTarget completionExtensionTarget
    exactSymmetricMonoidalExtensionTarget uniquenessTarget hMinimum hStable
    hConstruction hUniversal).bridgePackage

def concreteStableAdditiveKaroubiCompletionTarget
    {setup : RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (internal : InternalManuscriptSpineTarget P comparison C)
    (presentation : Type u)
    [PresentationQuiver presentation]
    [MonoidalPresentation presentation]
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
    StableAdditiveKaroubiCompletionTarget spine internal :=
  let package :=
    concreteStableCompletionBridgePackage internal presentation
      stableAdditiveCompletionTarget karoubiClosureTarget
      completionAgreesWithRecognitionTarget additiveConstructionTarget
      triangulatedConstructionTarget karoubiConstructionTarget
      structuralPackageCompatibilityTarget completionExtensionTarget
      exactSymmetricMonoidalExtensionTarget uniquenessTarget hMinimum hStable
      hConstruction hUniversal
  package.toStableAdditiveKaroubiCompletionTarget spine

def concreteTraceStableCompletionConstructionTarget
    {setup : RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (internal : InternalManuscriptSpineTarget P comparison C)
    (presentation : Type u)
    [PresentationQuiver presentation]
    [MonoidalPresentation presentation]
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
    TraceStableCompletionConstructionTarget spine internal
      (concreteStableAdditiveKaroubiCompletionTarget spine internal presentation
        stableAdditiveCompletionTarget karoubiClosureTarget
        completionAgreesWithRecognitionTarget additiveConstructionTarget
        triangulatedConstructionTarget karoubiConstructionTarget
        structuralPackageCompatibilityTarget completionExtensionTarget
        exactSymmetricMonoidalExtensionTarget uniquenessTarget hMinimum hStable
        hConstruction hUniversal) :=
  let package :=
    concreteStableCompletionBridgePackage internal presentation
      stableAdditiveCompletionTarget karoubiClosureTarget
      completionAgreesWithRecognitionTarget additiveConstructionTarget
      triangulatedConstructionTarget karoubiConstructionTarget
      structuralPackageCompatibilityTarget completionExtensionTarget
      exactSymmetricMonoidalExtensionTarget uniquenessTarget hMinimum hStable
      hConstruction hUniversal
  package.toTraceStableCompletionConstructionTarget spine
    (concreteStableAdditiveKaroubiCompletionTarget spine internal presentation
      stableAdditiveCompletionTarget karoubiClosureTarget
      completionAgreesWithRecognitionTarget additiveConstructionTarget
      triangulatedConstructionTarget karoubiConstructionTarget
      structuralPackageCompatibilityTarget completionExtensionTarget
      exactSymmetricMonoidalExtensionTarget uniquenessTarget hMinimum hStable
      hConstruction hUniversal)

def concreteTraceCompletionUniversalPropertyTarget
    {setup : RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (internal : InternalManuscriptSpineTarget P comparison C)
    (presentation : Type u)
    [PresentationQuiver presentation]
    [MonoidalPresentation presentation]
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
    TraceCompletionUniversalPropertyTarget spine internal
      (concreteStableAdditiveKaroubiCompletionTarget spine internal presentation
        stableAdditiveCompletionTarget karoubiClosureTarget
        completionAgreesWithRecognitionTarget additiveConstructionTarget
        triangulatedConstructionTarget karoubiConstructionTarget
        structuralPackageCompatibilityTarget completionExtensionTarget
        exactSymmetricMonoidalExtensionTarget uniquenessTarget hMinimum hStable
        hConstruction hUniversal)
      (concreteTraceStableCompletionConstructionTarget spine internal presentation
        stableAdditiveCompletionTarget karoubiClosureTarget
        completionAgreesWithRecognitionTarget additiveConstructionTarget
        triangulatedConstructionTarget karoubiConstructionTarget
        structuralPackageCompatibilityTarget completionExtensionTarget
        exactSymmetricMonoidalExtensionTarget uniquenessTarget hMinimum hStable
        hConstruction hUniversal) :=
  let package :=
    concreteStableCompletionBridgePackage internal presentation
      stableAdditiveCompletionTarget karoubiClosureTarget
      completionAgreesWithRecognitionTarget additiveConstructionTarget
      triangulatedConstructionTarget karoubiConstructionTarget
      structuralPackageCompatibilityTarget completionExtensionTarget
      exactSymmetricMonoidalExtensionTarget uniquenessTarget hMinimum hStable
      hConstruction hUniversal
  package.toTraceCompletionUniversalPropertyTarget spine
    (concreteStableAdditiveKaroubiCompletionTarget spine internal presentation
      stableAdditiveCompletionTarget karoubiClosureTarget
      completionAgreesWithRecognitionTarget additiveConstructionTarget
      triangulatedConstructionTarget karoubiConstructionTarget
      structuralPackageCompatibilityTarget completionExtensionTarget
      exactSymmetricMonoidalExtensionTarget uniquenessTarget hMinimum hStable
      hConstruction hUniversal)
    (concreteTraceStableCompletionConstructionTarget spine internal presentation
      stableAdditiveCompletionTarget karoubiClosureTarget
      completionAgreesWithRecognitionTarget additiveConstructionTarget
      triangulatedConstructionTarget karoubiConstructionTarget
      structuralPackageCompatibilityTarget completionExtensionTarget
      exactSymmetricMonoidalExtensionTarget uniquenessTarget hMinimum hStable
      hConstruction hUniversal)

end MotivicRecognition
end TraceCalc

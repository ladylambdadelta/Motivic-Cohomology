import TraceCalc.LayerALegacy.Extensions.SyntacticTraceDMgmEquivalence
import TraceCalc.LayerE.MotivicRecognition.InfinityPiZeroProofs
import TraceCalc.LayerD.MotivicRecognition.AdmissibleLocalizationAssembly
import TraceCalc.LayerD.DMgmQInterface

universe u v w x y z

namespace TraceCalc
namespace MotivicRecognition

open CategoryInfra.SyntacticTraceDMgm
open CategoryInfra.SyntacticInfinity

def concreteTraceToDMgmComparisonTarget (syntacticPresentation : Type u) :
    TraceToDMgmComparisonTarget syntacticPresentation :=
  TraceToDMgmComparisonTarget.syntactic syntacticPresentation

def concreteTraceToDMgmComparisonData (syntacticPresentation : Type u) :
    TraceToDMgmComparisonData
      (concreteTraceToDMgmComparisonTarget syntacticPresentation) :=
  TraceToDMgmComparisonData.syntactic syntacticPresentation

private theorem classicalPiZeroRecognitionWitness
    (iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}) :
    LayerD.DMgmQPiZeroInterface.piZeroRecognitionStatement iface :=
  LayerD.DMgmQPiZeroInterface.piZeroRecognition_holds iface

private theorem classicalInfinityRecognitionWitness
    (iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}) :
    LayerD.DMgmQPiZeroInterface.infinityRecognitionStatement iface :=
  LayerD.DMgmQPiZeroInterface.infinityRecognition_holds iface

private theorem classicalUniversalPropertyRecognitionWitness
    (iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}) :
    LayerD.DMgmQPiZeroInterface.universalPropertyRecognitionStatement iface :=
  LayerD.DMgmQPiZeroInterface.universalPropertyRecognition_holds iface

private theorem classicalRealizationStructureRecognitionWitness
    (iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}) :
    LayerD.DMgmQPiZeroInterface.realizationStructureRecognitionStatement iface :=
  ⟨⟨iface.target.baseFieldIsQTarget⟩,
    ⟨iface.target.coefficientFieldIsQTarget⟩⟩

/-- The classical structural part needed by the stable-completion bridge.

This is deliberately narrower than the full syntactic-to-classical
stable-completion preservation field: it proves that the existing classical
interface has the exact triangulated, symmetric monoidal, and idempotent
closure witnesses required to receive the Package 4 stable-completion
operations.  The remaining work is the comparison theorem identifying the
syntactic shifts/cones/Karoubi splittings/tensor with these classical
structures under an interpretation functor. -/
def syntacticDMgm_classicalStableCompletionStructuralStatement
    (iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}) : Prop :=
  Nonempty (TraceTriangulatedCoherenceData.{u, v, w, x, y, z}
    iface.trace iface.presentation) ∧
  Nonempty (TraceSymmetricMonoidalCoherenceData.{u, v, w, x, y, z}
    iface.trace iface.presentation) ∧
  (iface.presentation.motivicCategory.idempotentCompleteTarget ∧
    iface.presentation.admissibleLocalizationAxioms.Env.exactnessTarget)

private theorem classicalStableCompletionStructuralWitness
    (iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}) :
    syntacticDMgm_classicalStableCompletionStructuralStatement iface :=
  ⟨iface.certified.exactTriangulated_holds,
    iface.certified.symmetricMonoidal_holds,
    iface.certified.idempotentEnvelopeClosure_holds⟩

/-- Proof-relevant classical receiving side needed by presentation
preservation.  These five fields are data-bearing target structures, so the
bridge keeps them as data instead of erasing them into a proposition. -/
structure SyntacticDMgmClassicalPresentationReceivingData
    (iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}) where
  finiteCorrespondenceTransfers :
    CorrFunctorialityTarget iface.trace iface.presentation.motivicCategory
  localizationTriangles :
    OpenClosedLocalizationTarget iface.trace iface.presentation.motivicCategory
  nisnevichDescent :
    NisnevichDescentTarget iface.trace iface.presentation.motivicCategory
  a1Invariance :
    A1InvarianceTarget iface.trace iface.presentation.motivicCategory
  envelopeExactness :
    EnvelopeExactnessTarget iface.trace iface.presentation.motivicCategory

/-- The existing classical target supplies the Corr/Loc/Nis/A1/Env receiving
data needed by presentation preservation.  This does not claim that syntactic
generators and relations have already been interpreted into those surfaces;
that comparison still depends on the P3B classical boundary. -/
def syntacticDMgm_classicalPresentationReceiving_data
    (iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}) :
    SyntacticDMgmClassicalPresentationReceivingData iface where
  finiteCorrespondenceTransfers := iface.target.finiteCorrespondenceTransfers
  localizationTriangles := iface.target.localizationTriangles
  nisnevichDescent := iface.target.nisnevichDescent
  a1Invariance := iface.target.a1Invariance
  envelopeExactness := iface.target.envelopeExactness

/-- The classical receiving side for the final recognition/full-faithfulness
bridge.  It packages the proof-bearing structural witnesses already present in
the certified classical `DM_gm(Q)_Q` target. -/
def syntacticDMgm_classicalRecognitionReceivingStatement
    (iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}) : Prop :=
  Nonempty (TraceCompactGenerationData.{u, v, w, x, y, z}
    iface.trace iface.presentation) ∧
  Nonempty (TraceTriangulatedCoherenceData.{u, v, w, x, y, z}
    iface.trace iface.presentation) ∧
  Nonempty (TraceSymmetricMonoidalCoherenceData.{u, v, w, x, y, z}
    iface.trace iface.presentation) ∧
  (iface.presentation.motivicCategory.idempotentCompleteTarget ∧
    iface.presentation.admissibleLocalizationAxioms.Env.exactnessTarget) ∧
  iface.presentation.motivicCategory.qLinearTarget

private theorem classicalRecognitionReceivingWitness
    (iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}) :
    syntacticDMgm_classicalRecognitionReceivingStatement iface :=
  ⟨iface.certified.compactGeometricGeneration_holds,
    iface.certified.exactTriangulated_holds,
    iface.certified.symmetricMonoidal_holds,
    iface.certified.idempotentEnvelopeClosure_holds,
    iface.certified.qLinearCompatibility_holds⟩

/-- P6B integration point for the sealed Package 5 syntactic ∞→π₀
comparison.  This supplies the syntactic side of the π₀ bridge; the remaining
P6B comparison to the classical homotopy-category interface still requires
`interpretObj`/`interpretHom` and the classical boundary comparison. -/
def syntacticDMgm_p5InfinityToPiZeroComparison
    (presentation : Type u) :
    TraceInfinityToPiZeroShadowComparisonOverQ :=
  syntacticInfinityToPi0Comparison presentation

private theorem p5InfinityToPiZeroTriangulatedWitness
    (presentation : Type u) :
    (syntacticDMgm_p5InfinityToPiZeroComparison presentation).triangulatedStructureCompatibility :=
  let comparison := syntacticDMgm_p5InfinityToPiZeroComparison presentation
  comparison.triangulatedStructureCompatibility_holds

private theorem p5InfinityToPiZeroRealizationWitness
    (presentation : Type u) :
    (syntacticDMgm_p5InfinityToPiZeroComparison presentation).realizationCompatibility :=
  let comparison := syntacticDMgm_p5InfinityToPiZeroComparison presentation
  comparison.realizationCompatibility_holds

private theorem p5InfinityToPiZeroCompletedPresentationWitness
    (presentation : Type u) :
    (syntacticDMgm_p5InfinityToPiZeroComparison presentation).comparisonToCompletedPresentation :=
  let comparison := syntacticDMgm_p5InfinityToPiZeroComparison presentation
  comparison.comparisonToCompletedPresentation_holds

/-- Classical-side operations used to interpret the syntactic stable and
∞/π₀ generators.  They live over the existing `DMgmQPiZeroInterface`
motivic category; no syntactic replacement target is introduced. -/
structure SyntacticDMgmClassicalInterpretationData
    (syntacticPresentation : Type u)
    (iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}) where
  interpretObj :
    DMgmObj syntacticPresentation → iface.presentation.motivicCategory.Object
  interpretHom :
    ∀ {X Y : DMgmObj syntacticPresentation},
      DMgmHom X Y →
        iface.presentation.motivicCategory.Hom (interpretObj X) (interpretObj Y)
  interpretPi0 :
    ∀ {X Y : TraceObj syntacticPresentation},
      TraceHom X Y →
        iface.presentation.motivicCategory.Hom
          (interpretObj ((concreteTraceToDMgmComparisonTarget syntacticPresentation).objectComparison X))
          (interpretObj ((concreteTraceToDMgmComparisonTarget syntacticPresentation).objectComparison Y))
  classicalShiftObj :
    iface.presentation.motivicCategory.Object → iface.presentation.motivicCategory.Object
  classicalShiftMap :
    ∀ {X Y : iface.presentation.motivicCategory.Object},
      iface.presentation.motivicCategory.Hom X Y →
        iface.presentation.motivicCategory.Hom (classicalShiftObj X) (classicalShiftObj Y)
  classicalTensorObj :
    iface.presentation.motivicCategory.Object → iface.presentation.motivicCategory.Object →
      iface.presentation.motivicCategory.Object
  classicalTensorMap :
    ∀ {A B C D : iface.presentation.motivicCategory.Object},
      iface.presentation.motivicCategory.Hom A B →
        iface.presentation.motivicCategory.Hom C D →
          iface.presentation.motivicCategory.Hom (classicalTensorObj A C)
            (classicalTensorObj B D)
  classicalCofiberObj :
    iface.presentation.motivicCategory.Object → iface.presentation.motivicCategory.Object →
      iface.presentation.motivicCategory.Object
  classicalDualObj :
    iface.presentation.motivicCategory.Object → iface.presentation.motivicCategory.Object
  identityPreservation :
    ∀ X : DMgmObj syntacticPresentation,
      interpretHom (DMgmHom.id X) =
        iface.presentation.motivicCategory.id (interpretObj X)
  compositionPreservation :
    ∀ {X Y Z : DMgmObj syntacticPresentation}
      (f : DMgmHom X Y) (g : DMgmHom Y Z),
      interpretHom (DMgmHom.comp f g) =
        iface.presentation.motivicCategory.comp (interpretHom g) (interpretHom f)
  imagePi0Preservation :
    ∀ {X Y : TraceObj syntacticPresentation} (f : TraceHom X Y),
      interpretHom ((concreteTraceToDMgmComparisonTarget syntacticPresentation).homComparison f) =
        interpretPi0 f
  shiftObjPreservation :
    ∀ X : DMgmObj syntacticPresentation,
      interpretObj (DMgmObj.shift X) = classicalShiftObj (interpretObj X)
  shiftHomPreservation :
    ∀ {X Y : DMgmObj syntacticPresentation} (f : DMgmHom X Y),
      HEq (interpretHom (DMgmHom.shiftMap f))
        (classicalShiftMap (interpretHom f))
  cofiberObjPreservation :
    ∀ X Y : DMgmObj syntacticPresentation,
      interpretObj (DMgmObj.cofiber X Y) =
        classicalCofiberObj (interpretObj X) (interpretObj Y)
  tensorObjPreservation :
    ∀ X Y : DMgmObj syntacticPresentation,
      interpretObj (DMgmObj.tensor X Y) =
        classicalTensorObj (interpretObj X) (interpretObj Y)
  tensorHomPreservation :
    ∀ {A B C D : DMgmObj syntacticPresentation}
      (f : DMgmHom A B) (g : DMgmHom C D),
      HEq (interpretHom (DMgmHom.tensorMap f g))
        (classicalTensorMap (interpretHom f) (interpretHom g))
  dualObjPreservation :
    ∀ X : DMgmObj syntacticPresentation,
      interpretObj (DMgmObj.dual X) = classicalDualObj (interpretObj X)
  p3bAssignmentTable :
    ClassicalPeriods.GeneratorRealizationAssignmentTable iface.presentation.classicalContext
  p3bAdmissibilityComparison :
    iface.presentation.admissibleLocalizationAxioms =
      Package3B6.admissibleLocalizationAxioms_of_sealed_boundaries
        iface.presentation.motivicCategory p3bAssignmentTable

def syntacticDMgm_objectInterpretationStatement
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (interp : SyntacticDMgmClassicalInterpretationData syntacticPresentation iface) : Prop :=
  (∀ X : DMgmObj syntacticPresentation,
    interp.interpretHom (DMgmHom.id X) =
      iface.presentation.motivicCategory.id (interp.interpretObj X)) ∧
  ∀ X : DMgmObj syntacticPresentation,
    interp.interpretObj (DMgmObj.shift X) =
      interp.classicalShiftObj (interp.interpretObj X)

theorem objectInterpretationTargetWitnessFromInterpretation
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (interp : SyntacticDMgmClassicalInterpretationData syntacticPresentation iface) :
    syntacticDMgm_objectInterpretationStatement interp :=
  ⟨interp.identityPreservation, interp.shiftObjPreservation⟩

def syntacticDMgm_morphismInterpretationStatement
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (interp : SyntacticDMgmClassicalInterpretationData syntacticPresentation iface) : Prop :=
  (∀ {X Y Z : DMgmObj syntacticPresentation}
      (f : DMgmHom X Y) (g : DMgmHom Y Z),
      interp.interpretHom (DMgmHom.comp f g) =
        iface.presentation.motivicCategory.comp (interp.interpretHom g) (interp.interpretHom f)) ∧
  (∀ {X Y : DMgmObj syntacticPresentation} (f : DMgmHom X Y),
      HEq (interp.interpretHom (DMgmHom.shiftMap f))
        (interp.classicalShiftMap (interp.interpretHom f))) ∧
  ∀ {A B C D : DMgmObj syntacticPresentation}
      (f : DMgmHom A B) (g : DMgmHom C D),
      HEq (interp.interpretHom (DMgmHom.tensorMap f g))
        (interp.classicalTensorMap (interp.interpretHom f) (interp.interpretHom g))

theorem morphismInterpretationTargetWitnessFromInterpretation
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (interp : SyntacticDMgmClassicalInterpretationData syntacticPresentation iface) :
    syntacticDMgm_morphismInterpretationStatement interp :=
  ⟨interp.compositionPreservation,
    interp.shiftHomPreservation,
    interp.tensorHomPreservation⟩

def syntacticDMgm_presentationPreservationStatement
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (interp : SyntacticDMgmClassicalInterpretationData syntacticPresentation iface) : Prop :=
  ClassicalDMgmQPresentationTheorems iface.presentation ∧
    (concreteTraceToDMgmComparisonTarget syntacticPresentation).objectCompatibility ∧
    (concreteTraceToDMgmComparisonTarget syntacticPresentation).homCompatibility ∧
    ∀ {X Y : TraceObj syntacticPresentation} (f : TraceHom X Y),
      interp.interpretHom ((concreteTraceToDMgmComparisonTarget syntacticPresentation).homComparison f) =
        interp.interpretPi0 f

theorem presentationPreservationTargetWitnessFromInterpretation
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (interp : SyntacticDMgmClassicalInterpretationData syntacticPresentation iface) :
    syntacticDMgm_presentationPreservationStatement interp :=
  ⟨Package3B6.classicalDMgmQPresentationTheorems_of_sealed_boundaries
      interp.p3bAssignmentTable interp.p3bAdmissibilityComparison,
    (concreteTraceToDMgmComparisonData syntacticPresentation).objectCompatibilityWitness,
    (concreteTraceToDMgmComparisonData syntacticPresentation).homCompatibilityWitness,
    interp.imagePi0Preservation⟩

def syntacticDMgm_stableCompletionPreservationStatement
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (interp : SyntacticDMgmClassicalInterpretationData syntacticPresentation iface) : Prop :=
  syntacticDMgm_classicalStableCompletionStructuralStatement iface ∧
    (concreteTraceToDMgmComparisonTarget syntacticPresentation).exactMonoidalCompatibility ∧
    (∀ X : DMgmObj syntacticPresentation,
      interp.interpretObj (DMgmObj.shift X) =
        interp.classicalShiftObj (interp.interpretObj X)) ∧
    (∀ X Y : DMgmObj syntacticPresentation,
      interp.interpretObj (DMgmObj.cofiber X Y) =
        interp.classicalCofiberObj (interp.interpretObj X) (interp.interpretObj Y)) ∧
    (∀ X Y : DMgmObj syntacticPresentation,
      interp.interpretObj (DMgmObj.tensor X Y) =
        interp.classicalTensorObj (interp.interpretObj X) (interp.interpretObj Y)) ∧
    (∀ X : DMgmObj syntacticPresentation,
      interp.interpretObj (DMgmObj.dual X) = interp.classicalDualObj (interp.interpretObj X)) ∧
    (iface.presentation.motivicCategory.idempotentCompleteTarget ∧
      iface.presentation.admissibleLocalizationAxioms.Env.exactnessTarget)

theorem stableCompletionPreservationTargetWitnessFromInterpretation
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (interp : SyntacticDMgmClassicalInterpretationData syntacticPresentation iface) :
    syntacticDMgm_stableCompletionPreservationStatement interp :=
  ⟨classicalStableCompletionStructuralWitness iface,
    (concreteTraceToDMgmComparisonData syntacticPresentation).exactMonoidalCompatibilityWitness,
    interp.shiftObjPreservation,
    interp.cofiberObjPreservation,
    interp.tensorObjPreservation,
    interp.dualObjPreservation,
    iface.certified.idempotentEnvelopeClosure_holds⟩

def syntacticDMgm_piZeroCompatibilityStatement
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (interp : SyntacticDMgmClassicalInterpretationData syntacticPresentation iface) : Prop :=
  (syntacticDMgm_p5InfinityToPiZeroComparison syntacticPresentation).triangulatedStructureCompatibility ∧
    (concreteTraceToDMgmComparisonTarget syntacticPresentation).homotopyCategoryCompatibility ∧
    LayerD.DMgmQPiZeroInterface.piZeroRecognitionStatement iface ∧
    ∀ {X Y : TraceObj syntacticPresentation} (f : InfMap X Y),
      interp.interpretHom
          ((concreteTraceToDMgmComparisonTarget syntacticPresentation).homComparison
            ((concreteTraceToDMgmComparisonTarget syntacticPresentation).enhancement.category.pi0Class f)) =
        interp.interpretPi0
          ((concreteTraceToDMgmComparisonTarget syntacticPresentation).enhancement.category.pi0Class f)

theorem piZeroCompatibilityTargetWitnessFromInterpretation
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (interp : SyntacticDMgmClassicalInterpretationData syntacticPresentation iface) :
    syntacticDMgm_piZeroCompatibilityStatement interp :=
  ⟨p5InfinityToPiZeroTriangulatedWitness syntacticPresentation,
    (concreteTraceToDMgmComparisonData syntacticPresentation).homotopyCategoryCompatibilityWitness,
    LayerD.DMgmQPiZeroInterface.piZeroRecognition_holds iface,
    fun f =>
      interp.imagePi0Preservation
        ((concreteTraceToDMgmComparisonTarget syntacticPresentation).enhancement.category.pi0Class f)⟩

def syntacticDMgm_fullFaithfulnessRecognitionStatement
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (interp : SyntacticDMgmClassicalInterpretationData syntacticPresentation iface) : Prop :=
  syntacticDMgm_presentationPreservationStatement interp ∧
    syntacticDMgm_stableCompletionPreservationStatement interp ∧
    syntacticDMgm_piZeroCompatibilityStatement interp ∧
    (concreteTraceToDMgmComparisonTarget syntacticPresentation).fullyFaithful ∧
    syntacticDMgm_classicalRecognitionReceivingStatement iface

theorem fullFaithfulnessRecognitionTargetWitnessFromInterpretation
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (interp : SyntacticDMgmClassicalInterpretationData syntacticPresentation iface) :
    syntacticDMgm_fullFaithfulnessRecognitionStatement interp :=
  ⟨presentationPreservationTargetWitnessFromInterpretation interp,
    stableCompletionPreservationTargetWitnessFromInterpretation interp,
    piZeroCompatibilityTargetWitnessFromInterpretation interp,
    (concreteTraceToDMgmComparisonData syntacticPresentation).fullyFaithfulWitness,
    classicalRecognitionReceivingWitness iface⟩

/-- Compatibility name for the syntactic-to-classical bridge owner.

The proof-relevant owner is the interpretation data already present in this
file; the old bridge structure only repackaged exact statements as local
`Prop` fields plus witnesses. Keep the bridge name for downstream code, but
route it directly through `SyntacticDMgmClassicalInterpretationData`. -/
abbrev SyntacticDMgmToClassicalDMgmBridgeData
    (syntacticPresentation : Type u)
    (iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}) :=
  SyntacticDMgmClassicalInterpretationData syntacticPresentation iface

namespace SyntacticDMgmToClassicalDMgmBridgeData

def objectInterpretationTarget
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (bridge : SyntacticDMgmToClassicalDMgmBridgeData syntacticPresentation iface) : Prop :=
  syntacticDMgm_objectInterpretationStatement bridge

theorem objectInterpretationWitness
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (bridge : SyntacticDMgmToClassicalDMgmBridgeData syntacticPresentation iface) :
    bridge.objectInterpretationTarget :=
  objectInterpretationTargetWitnessFromInterpretation bridge

def morphismInterpretationTarget
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (bridge : SyntacticDMgmToClassicalDMgmBridgeData syntacticPresentation iface) : Prop :=
  syntacticDMgm_morphismInterpretationStatement bridge

theorem morphismInterpretationWitness
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (bridge : SyntacticDMgmToClassicalDMgmBridgeData syntacticPresentation iface) :
    bridge.morphismInterpretationTarget :=
  morphismInterpretationTargetWitnessFromInterpretation bridge

def presentationPreservationTarget
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (bridge : SyntacticDMgmToClassicalDMgmBridgeData syntacticPresentation iface) : Prop :=
  syntacticDMgm_presentationPreservationStatement bridge

theorem presentationPreservationWitness
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (bridge : SyntacticDMgmToClassicalDMgmBridgeData syntacticPresentation iface) :
    bridge.presentationPreservationTarget :=
  presentationPreservationTargetWitnessFromInterpretation bridge

def stableCompletionPreservationTarget
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (bridge : SyntacticDMgmToClassicalDMgmBridgeData syntacticPresentation iface) : Prop :=
  syntacticDMgm_stableCompletionPreservationStatement bridge

theorem stableCompletionPreservationWitness
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (bridge : SyntacticDMgmToClassicalDMgmBridgeData syntacticPresentation iface) :
    bridge.stableCompletionPreservationTarget :=
  stableCompletionPreservationTargetWitnessFromInterpretation bridge

def piZeroCompatibilityTarget
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (bridge : SyntacticDMgmToClassicalDMgmBridgeData syntacticPresentation iface) : Prop :=
  syntacticDMgm_piZeroCompatibilityStatement bridge

theorem piZeroCompatibilityWitness
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (bridge : SyntacticDMgmToClassicalDMgmBridgeData syntacticPresentation iface) :
    bridge.piZeroCompatibilityTarget :=
  piZeroCompatibilityTargetWitnessFromInterpretation bridge

def fullFaithfulnessRecognitionTarget
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (bridge : SyntacticDMgmToClassicalDMgmBridgeData syntacticPresentation iface) : Prop :=
  syntacticDMgm_fullFaithfulnessRecognitionStatement bridge

theorem fullFaithfulnessRecognitionWitness
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (bridge : SyntacticDMgmToClassicalDMgmBridgeData syntacticPresentation iface) :
    bridge.fullFaithfulnessRecognitionTarget :=
  fullFaithfulnessRecognitionTargetWitnessFromInterpretation bridge

abbrev ofInterpretationData
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (interp : SyntacticDMgmClassicalInterpretationData syntacticPresentation iface) :
    SyntacticDMgmToClassicalDMgmBridgeData syntacticPresentation iface :=
  interp

end SyntacticDMgmToClassicalDMgmBridgeData

/-- Compatibility alias for the syntactic-to-classical bridge theorem package. -/
abbrev SyntacticDMgmToClassicalDMgmBridgeTheoremPackage
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (bridge : SyntacticDMgmToClassicalDMgmBridgeData syntacticPresentation iface) :=
  SyntacticDMgmToClassicalDMgmBridgeData syntacticPresentation iface

namespace SyntacticDMgmToClassicalDMgmBridgeTheoremPackage

def objectInterpretation
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    {bridge : SyntacticDMgmToClassicalDMgmBridgeData syntacticPresentation iface}
    (package : SyntacticDMgmToClassicalDMgmBridgeTheoremPackage bridge) :
    bridge.objectInterpretationTarget :=
  package.objectInterpretationWitness

def morphismInterpretation
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    {bridge : SyntacticDMgmToClassicalDMgmBridgeData syntacticPresentation iface}
    (package : SyntacticDMgmToClassicalDMgmBridgeTheoremPackage bridge) :
    bridge.morphismInterpretationTarget :=
  package.morphismInterpretationWitness

def presentationPreservation
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    {bridge : SyntacticDMgmToClassicalDMgmBridgeData syntacticPresentation iface}
    (package : SyntacticDMgmToClassicalDMgmBridgeTheoremPackage bridge) :
    bridge.presentationPreservationTarget :=
  package.presentationPreservationWitness

def stableCompletionPreservation
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    {bridge : SyntacticDMgmToClassicalDMgmBridgeData syntacticPresentation iface}
    (package : SyntacticDMgmToClassicalDMgmBridgeTheoremPackage bridge) :
    bridge.stableCompletionPreservationTarget :=
  package.stableCompletionPreservationWitness

def piZeroCompatibility
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    {bridge : SyntacticDMgmToClassicalDMgmBridgeData syntacticPresentation iface}
    (package : SyntacticDMgmToClassicalDMgmBridgeTheoremPackage bridge) :
    bridge.piZeroCompatibilityTarget :=
  package.piZeroCompatibilityWitness

def fullFaithfulnessRecognition
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    {bridge : SyntacticDMgmToClassicalDMgmBridgeData syntacticPresentation iface}
    (package : SyntacticDMgmToClassicalDMgmBridgeTheoremPackage bridge) :
    bridge.fullFaithfulnessRecognitionTarget :=
  package.fullFaithfulnessRecognitionWitness

def classicalPiZeroRecognition
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    {bridge : SyntacticDMgmToClassicalDMgmBridgeData syntacticPresentation iface}
    (_package : SyntacticDMgmToClassicalDMgmBridgeTheoremPackage bridge) :
    LayerD.DMgmQPiZeroInterface.piZeroRecognitionStatement iface :=
  LayerD.DMgmQPiZeroInterface.piZeroRecognition_holds iface

def classicalInfinityRecognition
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    {bridge : SyntacticDMgmToClassicalDMgmBridgeData syntacticPresentation iface}
    (_package : SyntacticDMgmToClassicalDMgmBridgeTheoremPackage bridge) :
    LayerD.DMgmQPiZeroInterface.infinityRecognitionStatement iface :=
  LayerD.DMgmQPiZeroInterface.infinityRecognition_holds iface

def classicalUniversalPropertyRecognition
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    {bridge : SyntacticDMgmToClassicalDMgmBridgeData syntacticPresentation iface}
    (_package : SyntacticDMgmToClassicalDMgmBridgeTheoremPackage bridge) :
    LayerD.DMgmQPiZeroInterface.universalPropertyRecognitionStatement iface :=
  LayerD.DMgmQPiZeroInterface.universalPropertyRecognition_holds iface

def classicalRealizationStructureRecognition
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    {bridge : SyntacticDMgmToClassicalDMgmBridgeData syntacticPresentation iface}
    (_package : SyntacticDMgmToClassicalDMgmBridgeTheoremPackage bridge) :
    LayerD.DMgmQPiZeroInterface.realizationStructureRecognitionStatement iface :=
  ⟨⟨iface.target.baseFieldIsQTarget⟩,
    ⟨iface.target.coefficientFieldIsQTarget⟩⟩

def ofBridgeData
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (bridge : SyntacticDMgmToClassicalDMgmBridgeData syntacticPresentation iface) :
    SyntacticDMgmToClassicalDMgmBridgeTheoremPackage bridge :=
  bridge

end SyntacticDMgmToClassicalDMgmBridgeTheoremPackage

/-- Recognition target obtained only when syntactic bridge owner data has been
connected to the existing classical `DM_gm(Q)_Q` interface. -/
structure SyntacticDMgmClassicalRecognitionTarget
    (syntacticPresentation : Type u)
    (iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}) where
  bridge : SyntacticDMgmToClassicalDMgmBridgeData syntacticPresentation iface
  theoremPackage : SyntacticDMgmToClassicalDMgmBridgeTheoremPackage bridge
  classicalTarget : ClassicalDMgmQTarget iface.trace iface.presentation
  certifiedClassicalTarget :
    CertifiedClassicalDMgmQTarget iface.trace iface.presentation classicalTarget
  targetIsInterfaceTarget : classicalTarget = iface.target
  piZeroRecognitionWitness :
    LayerD.DMgmQPiZeroInterface.piZeroRecognitionStatement iface
  bridgeRecognitionWitness :
    bridge.objectInterpretationTarget ∧
      bridge.morphismInterpretationTarget ∧
      bridge.presentationPreservationTarget ∧
      bridge.stableCompletionPreservationTarget ∧
      bridge.piZeroCompatibilityTarget ∧
      bridge.fullFaithfulnessRecognitionTarget

namespace SyntacticDMgmClassicalRecognitionTarget

def ofBridgeData
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (bridge : SyntacticDMgmToClassicalDMgmBridgeData syntacticPresentation iface) :
    SyntacticDMgmClassicalRecognitionTarget syntacticPresentation iface :=
  let theoremPackage :=
    SyntacticDMgmToClassicalDMgmBridgeTheoremPackage.ofBridgeData bridge
  { bridge := bridge
    theoremPackage := theoremPackage
    classicalTarget := iface.target
    certifiedClassicalTarget := iface.certified
    targetIsInterfaceTarget := rfl
    piZeroRecognitionWitness := theoremPackage.classicalPiZeroRecognition
    bridgeRecognitionWitness :=
      ⟨theoremPackage.objectInterpretation,
        ⟨theoremPackage.morphismInterpretation,
          ⟨theoremPackage.presentationPreservation,
            ⟨theoremPackage.stableCompletionPreservation,
              ⟨theoremPackage.piZeroCompatibility,
                theoremPackage.fullFaithfulnessRecognition⟩⟩⟩⟩⟩ }

def ofInterpretationData
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (interp : SyntacticDMgmClassicalInterpretationData syntacticPresentation iface) :
    SyntacticDMgmClassicalRecognitionTarget syntacticPresentation iface :=
  SyntacticDMgmClassicalRecognitionTarget.ofBridgeData
    (SyntacticDMgmToClassicalDMgmBridgeData.ofInterpretationData interp)

end SyntacticDMgmClassicalRecognitionTarget

/-- Full proof-relevant syntactic-to-classical interface required for the
unconditional Package 6 identification.

This is the missing interface surface: it bundles the existing certified
classical `DM_gm(Q)_Q` interface together with the actual syntactic presentation
and interpretation semantics.  It does not synthesize morphisms from the bare
`MotivicCategoryCandidate`; those morphism interpretations are carried here as
real data with preservation laws by `SyntacticDMgmClassicalInterpretationData`. -/
structure SyntacticDMgmClassicalIdentificationInterface where
  syntacticPresentation : Type u
  classicalInterface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}
  interpretation :
    SyntacticDMgmClassicalInterpretationData syntacticPresentation classicalInterface

namespace SyntacticDMgmClassicalIdentificationInterface

def bridgeData
    (iface : SyntacticDMgmClassicalIdentificationInterface.{u, v, w, x, y, z}) :
    SyntacticDMgmToClassicalDMgmBridgeData
      iface.syntacticPresentation iface.classicalInterface :=
  SyntacticDMgmToClassicalDMgmBridgeData.ofInterpretationData iface.interpretation

def recognitionTarget
    (iface : SyntacticDMgmClassicalIdentificationInterface.{u, v, w, x, y, z}) :
    SyntacticDMgmClassicalRecognitionTarget
      iface.syntacticPresentation iface.classicalInterface :=
  SyntacticDMgmClassicalRecognitionTarget.ofInterpretationData iface.interpretation

theorem recognitionTarget_reaches_existing_classical_target
    (iface : SyntacticDMgmClassicalIdentificationInterface.{u, v, w, x, y, z}) :
    (recognitionTarget iface).classicalTarget = iface.classicalInterface.target :=
  rfl

theorem recognitionTargetBridgeFieldsWitness
    (iface : SyntacticDMgmClassicalIdentificationInterface.{u, v, w, x, y, z}) :
    (recognitionTarget iface).bridge.objectInterpretationTarget ∧
      (recognitionTarget iface).bridge.morphismInterpretationTarget ∧
      (recognitionTarget iface).bridge.presentationPreservationTarget ∧
      (recognitionTarget iface).bridge.stableCompletionPreservationTarget ∧
      (recognitionTarget iface).bridge.piZeroCompatibilityTarget ∧
      (recognitionTarget iface).bridge.fullFaithfulnessRecognitionTarget :=
  (recognitionTarget iface).bridgeRecognitionWitness

end SyntacticDMgmClassicalIdentificationInterface

/-- Final P6B package obtained from concrete syntactic-to-classical
interpretation semantics.  The target is the existing `DMgmQPiZeroInterface`;
the result records `classicalTarget = iface.target` rather than introducing a
parallel syntactic `DM_gm`. -/
def finalPackage6ClassicalSeal_from_interpretation
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (interp : SyntacticDMgmClassicalInterpretationData syntacticPresentation iface) :
    SyntacticDMgmClassicalRecognitionTarget syntacticPresentation iface :=
  SyntacticDMgmClassicalRecognitionTarget.ofInterpretationData interp

theorem finalPackage6ClassicalSeal_reaches_existing_classical_target
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (interp : SyntacticDMgmClassicalInterpretationData syntacticPresentation iface) :
    (finalPackage6ClassicalSeal_from_interpretation interp).classicalTarget = iface.target :=
  rfl

theorem finalPackage6ClassicalSealBridgeFieldsWitness
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (interp : SyntacticDMgmClassicalInterpretationData syntacticPresentation iface) :
    (finalPackage6ClassicalSeal_from_interpretation interp).bridge.objectInterpretationTarget ∧
      (finalPackage6ClassicalSeal_from_interpretation interp).bridge.morphismInterpretationTarget ∧
      (finalPackage6ClassicalSeal_from_interpretation interp).bridge.presentationPreservationTarget ∧
      (finalPackage6ClassicalSeal_from_interpretation interp).bridge.stableCompletionPreservationTarget ∧
      (finalPackage6ClassicalSeal_from_interpretation interp).bridge.piZeroCompatibilityTarget ∧
      (finalPackage6ClassicalSeal_from_interpretation interp).bridge.fullFaithfulnessRecognitionTarget :=
  (finalPackage6ClassicalSeal_from_interpretation interp).bridgeRecognitionWitness

/-- Final Package 6 seal from the full proof-relevant identification interface.

This is the non-anonymous version of the interpretation bridge: all required
object, morphism, presentation, stable-completion, π₀, and recognition
comparisons are fields of `SyntacticDMgmClassicalIdentificationInterface`. -/
def finalPackage6ClassicalSeal_from_identificationInterface
    (iface : SyntacticDMgmClassicalIdentificationInterface.{u, v, w, x, y, z}) :
    SyntacticDMgmClassicalRecognitionTarget
      iface.syntacticPresentation iface.classicalInterface :=
  SyntacticDMgmClassicalIdentificationInterface.recognitionTarget iface

theorem finalPackage6ClassicalSeal_interface_reaches_existing_classical_target
    (iface : SyntacticDMgmClassicalIdentificationInterface.{u, v, w, x, y, z}) :
    (finalPackage6ClassicalSeal_from_identificationInterface iface).classicalTarget =
      iface.classicalInterface.target :=
  rfl

theorem finalPackage6ClassicalSealInterfaceBridgeFieldsWitness
    (iface : SyntacticDMgmClassicalIdentificationInterface.{u, v, w, x, y, z}) :
    (finalPackage6ClassicalSeal_from_identificationInterface iface).bridge.objectInterpretationTarget ∧
      (finalPackage6ClassicalSeal_from_identificationInterface iface).bridge.morphismInterpretationTarget ∧
      (finalPackage6ClassicalSeal_from_identificationInterface iface).bridge.presentationPreservationTarget ∧
      (finalPackage6ClassicalSeal_from_identificationInterface iface).bridge.stableCompletionPreservationTarget ∧
      (finalPackage6ClassicalSeal_from_identificationInterface iface).bridge.piZeroCompatibilityTarget ∧
      (finalPackage6ClassicalSeal_from_identificationInterface iface).bridge.fullFaithfulnessRecognitionTarget :=
  (finalPackage6ClassicalSeal_from_identificationInterface iface).bridgeRecognitionWitness

-- ============================================================
-- P6A Syntactic Provider and ofSealedPackages
-- ============================================================

/-- Bundled provider of concrete classical operations needed to construct
`SyntacticDMgmClassicalInterpretationData` from sealed packages by recursion
on the syntactic `DMgmObj`/`DMgmHom` syntax.

This is the "P6A syntactic provider" surface: the sealed `DMgmQPiZeroInterface`
gives the certified classical target, while this structure supplies the
actual operation-level data (shift, tensor, cofiber, dual, base-image
interpretation) that are not stored as functions inside the sealed packages.

Fields:
- `interpretBase` / `interpretBaseHom` : classification of `TraceObj`/`TraceHom`
  (i.e. π₀ image objects and morphisms) into the classical motivic category;
- `classicalShiftObj` / `classicalShiftMap` : receiving shift functor;
- `classicalTensorObj` / `classicalTensorMap` : receiving tensor product;
- `classicalCofiberObj` : receiving cofiber/cone constructor;
- `classicalDualObj` : receiving dual;
- `p3bAssignmentTable` / `p3bAdmissibilityComparison` : sealed P3B boundary
  identification (same as the two P3B fields of
  `SyntacticDMgmClassicalInterpretationData`). -/
structure SealedClassicalOperationsProvider
    (syntacticPresentation : Type u)
    (iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}) where
  interpretBase :
    TraceObj syntacticPresentation → iface.presentation.motivicCategory.Object
  interpretBaseHom :
    ∀ {X Y : TraceObj syntacticPresentation},
      TraceHom X Y →
        iface.presentation.motivicCategory.Hom
          (interpretBase X) (interpretBase Y)
  classicalShiftObj :
    iface.presentation.motivicCategory.Object →
      iface.presentation.motivicCategory.Object
  classicalShiftMap :
    ∀ {X Y : iface.presentation.motivicCategory.Object},
      iface.presentation.motivicCategory.Hom X Y →
        iface.presentation.motivicCategory.Hom
          (classicalShiftObj X) (classicalShiftObj Y)
  classicalTensorObj :
    iface.presentation.motivicCategory.Object →
      iface.presentation.motivicCategory.Object →
        iface.presentation.motivicCategory.Object
  classicalTensorMap :
    ∀ {A B C D : iface.presentation.motivicCategory.Object},
      iface.presentation.motivicCategory.Hom A B →
        iface.presentation.motivicCategory.Hom C D →
          iface.presentation.motivicCategory.Hom
            (classicalTensorObj A C) (classicalTensorObj B D)
  classicalCofiberObj :
    iface.presentation.motivicCategory.Object →
      iface.presentation.motivicCategory.Object →
        iface.presentation.motivicCategory.Object
  classicalDualObj :
    iface.presentation.motivicCategory.Object →
      iface.presentation.motivicCategory.Object
  p3bAssignmentTable :
    ClassicalPeriods.GeneratorRealizationAssignmentTable
      iface.presentation.classicalContext
  p3bAdmissibilityComparison :
    iface.presentation.admissibleLocalizationAxioms =
      Package3B6.admissibleLocalizationAxioms_of_sealed_boundaries
        iface.presentation.motivicCategory p3bAssignmentTable

/-- Minimal proof-relevant operation-level data that the classical
`DM_gm(Q)_Q` interface must expose before Package 6 can be fully sealed.

The current certified classical target proves theorem-level structure exists,
but it does not expose these concrete functions.  This record is therefore the
next interface surface to inhabit from non-surrogate classical data. -/
structure ClassicalDMgmQOperationsData
    (syntacticPresentation : Type u)
    (iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}) where
  interpretBase :
    TraceObj syntacticPresentation → iface.presentation.motivicCategory.Object
  interpretBaseHom :
    ∀ {X Y : TraceObj syntacticPresentation},
      TraceHom X Y →
        iface.presentation.motivicCategory.Hom
          (interpretBase X) (interpretBase Y)
  classicalShiftObj :
    iface.presentation.motivicCategory.Object →
      iface.presentation.motivicCategory.Object
  classicalShiftMap :
    ∀ {X Y : iface.presentation.motivicCategory.Object},
      iface.presentation.motivicCategory.Hom X Y →
        iface.presentation.motivicCategory.Hom
          (classicalShiftObj X) (classicalShiftObj Y)
  classicalTensorObj :
    iface.presentation.motivicCategory.Object →
      iface.presentation.motivicCategory.Object →
        iface.presentation.motivicCategory.Object
  classicalTensorMap :
    ∀ {A B C D : iface.presentation.motivicCategory.Object},
      iface.presentation.motivicCategory.Hom A B →
        iface.presentation.motivicCategory.Hom C D →
          iface.presentation.motivicCategory.Hom
            (classicalTensorObj A C) (classicalTensorObj B D)
  classicalCofiberObj :
    iface.presentation.motivicCategory.Object →
      iface.presentation.motivicCategory.Object →
        iface.presentation.motivicCategory.Object
  classicalDualObj :
    iface.presentation.motivicCategory.Object →
      iface.presentation.motivicCategory.Object
  p3bAssignmentTable :
    ClassicalPeriods.GeneratorRealizationAssignmentTable
      iface.presentation.classicalContext
  p3bAdmissibilityComparison :
    iface.presentation.admissibleLocalizationAxioms =
      Package3B6.admissibleLocalizationAxioms_of_sealed_boundaries
        iface.presentation.motivicCategory p3bAssignmentTable

namespace ClassicalDMgmQOperationsData

/-- Operation-level classical data projected from the strengthened
`DMgmQPiZeroInterface`.

This is the non-surrogate source for the P6B interpretation machinery: the
object and morphism interpretations, classical shift/tensor/cofiber/duality
operations, and sealed P3B admissibility comparison are all fields of the
existing classical interface. -/
def ofSealedSources
    (syntacticPresentation : Type u)
    (iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}) :
    ClassicalDMgmQOperationsData syntacticPresentation iface where
  interpretBase := iface.interpretBase syntacticPresentation
  interpretBaseHom := iface.interpretBaseHom
  classicalShiftObj := iface.classicalShiftObj
  classicalShiftMap := iface.classicalShiftMap
  classicalTensorObj := iface.classicalTensorObj
  classicalTensorMap := iface.classicalTensorMap
  classicalCofiberObj := iface.classicalCofiberObj
  classicalDualObj := iface.classicalDualObj
  p3bAssignmentTable := iface.p3bAssignmentTable
  p3bAdmissibilityComparison := iface.p3bAdmissibilityComparison

def toSealedClassicalOperationsProvider
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (data : ClassicalDMgmQOperationsData syntacticPresentation iface) :
    SealedClassicalOperationsProvider syntacticPresentation iface where
  interpretBase := data.interpretBase
  interpretBaseHom := data.interpretBaseHom
  classicalShiftObj := data.classicalShiftObj
  classicalShiftMap := data.classicalShiftMap
  classicalTensorObj := data.classicalTensorObj
  classicalTensorMap := data.classicalTensorMap
  classicalCofiberObj := data.classicalCofiberObj
  classicalDualObj := data.classicalDualObj
  p3bAssignmentTable := data.p3bAssignmentTable
  p3bAdmissibilityComparison := data.p3bAdmissibilityComparison

end ClassicalDMgmQOperationsData

namespace SealedClassicalOperationsProvider

def ofSealedSources
    (syntacticPresentation : Type u)
    (iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}) :
    SealedClassicalOperationsProvider syntacticPresentation iface :=
  (ClassicalDMgmQOperationsData.ofSealedSources syntacticPresentation iface)
    |>.toSealedClassicalOperationsProvider

def ofClassicalOperationsData
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (data : ClassicalDMgmQOperationsData syntacticPresentation iface) :
    SealedClassicalOperationsProvider syntacticPresentation iface :=
  data.toSealedClassicalOperationsProvider

theorem interpretBase_from_classicalOperationsData
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (data : ClassicalDMgmQOperationsData syntacticPresentation iface)
    (X : TraceObj syntacticPresentation) :
    (ofClassicalOperationsData data).interpretBase X = data.interpretBase X :=
  rfl

theorem interpretBaseHom_from_classicalOperationsData
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (data : ClassicalDMgmQOperationsData syntacticPresentation iface)
    {X Y : TraceObj syntacticPresentation} (f : TraceHom X Y) :
    (ofClassicalOperationsData data).interpretBaseHom f = data.interpretBaseHom f :=
  rfl

theorem classicalShiftObj_from_classicalOperationsData
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (data : ClassicalDMgmQOperationsData syntacticPresentation iface)
    (X : iface.presentation.motivicCategory.Object) :
    (ofClassicalOperationsData data).classicalShiftObj X = data.classicalShiftObj X :=
  rfl

theorem classicalShiftMap_from_classicalOperationsData
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (data : ClassicalDMgmQOperationsData syntacticPresentation iface)
    {X Y : iface.presentation.motivicCategory.Object}
    (f : iface.presentation.motivicCategory.Hom X Y) :
    (ofClassicalOperationsData data).classicalShiftMap f = data.classicalShiftMap f :=
  rfl

theorem classicalTensorObj_from_classicalOperationsData
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (data : ClassicalDMgmQOperationsData syntacticPresentation iface)
    (X Y : iface.presentation.motivicCategory.Object) :
    (ofClassicalOperationsData data).classicalTensorObj X Y =
      data.classicalTensorObj X Y :=
  rfl

theorem classicalTensorMap_from_classicalOperationsData
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (data : ClassicalDMgmQOperationsData syntacticPresentation iface)
    {A B C D : iface.presentation.motivicCategory.Object}
    (f : iface.presentation.motivicCategory.Hom A B)
    (g : iface.presentation.motivicCategory.Hom C D) :
    (ofClassicalOperationsData data).classicalTensorMap f g =
      data.classicalTensorMap f g :=
  rfl

theorem classicalCofiberObj_from_classicalOperationsData
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (data : ClassicalDMgmQOperationsData syntacticPresentation iface)
    (X Y : iface.presentation.motivicCategory.Object) :
    (ofClassicalOperationsData data).classicalCofiberObj X Y =
      data.classicalCofiberObj X Y :=
  rfl

theorem classicalDualObj_from_classicalOperationsData
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (data : ClassicalDMgmQOperationsData syntacticPresentation iface)
    (X : iface.presentation.motivicCategory.Object) :
    (ofClassicalOperationsData data).classicalDualObj X = data.classicalDualObj X :=
  rfl

theorem p3bAssignmentTable_from_classicalOperationsData
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (data : ClassicalDMgmQOperationsData syntacticPresentation iface) :
    (ofClassicalOperationsData data).p3bAssignmentTable = data.p3bAssignmentTable :=
  rfl

theorem p3bAdmissibilityComparison_from_classicalOperationsData
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (data : ClassicalDMgmQOperationsData syntacticPresentation iface) :
    HEq (ofClassicalOperationsData data).p3bAdmissibilityComparison
      data.p3bAdmissibilityComparison :=
  HEq.rfl

theorem interpretBase_from_sealedSources
    (syntacticPresentation : Type u)
    (iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z})
    (X : TraceObj syntacticPresentation) :
    (ofSealedSources syntacticPresentation iface).interpretBase X =
      iface.interpretBase syntacticPresentation X :=
  rfl

theorem interpretBaseHom_from_sealedSources
    (syntacticPresentation : Type u)
    (iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z})
    {X Y : TraceObj syntacticPresentation} (f : TraceHom X Y) :
    (ofSealedSources syntacticPresentation iface).interpretBaseHom f =
      iface.interpretBaseHom f :=
  rfl

theorem classicalShiftObj_from_sealedSources
    (syntacticPresentation : Type u)
    (iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z})
    (X : iface.presentation.motivicCategory.Object) :
    (ofSealedSources syntacticPresentation iface).classicalShiftObj X =
      iface.classicalShiftObj X :=
  rfl

theorem classicalTensorObj_from_sealedSources
    (syntacticPresentation : Type u)
    (iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z})
    (X Y : iface.presentation.motivicCategory.Object) :
    (ofSealedSources syntacticPresentation iface).classicalTensorObj X Y =
      iface.classicalTensorObj X Y :=
  rfl

theorem p3bAdmissibilityComparison_from_sealedSources
    (syntacticPresentation : Type u)
    (iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}) :
    HEq (ofSealedSources syntacticPresentation iface).p3bAdmissibilityComparison
      iface.p3bAdmissibilityComparison :=
  HEq.rfl

end SealedClassicalOperationsProvider

-- ── Object interpretation by structural recursion ─────────────────────────

private def interpretObjFromProvider
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (provider : SealedClassicalOperationsProvider syntacticPresentation iface) :
    DMgmObj syntacticPresentation → iface.presentation.motivicCategory.Object
  | .image X     => provider.interpretBase X
  | .shift X     => provider.classicalShiftObj (interpretObjFromProvider provider X)
  | .cofiber X Y => provider.classicalCofiberObj
      (interpretObjFromProvider provider X) (interpretObjFromProvider provider Y)
  | .tensor X Y  => provider.classicalTensorObj
      (interpretObjFromProvider provider X) (interpretObjFromProvider provider Y)
  | .dual X      => provider.classicalDualObj (interpretObjFromProvider provider X)

-- ── Morphism interpretation by structural recursion ───────────────────────

private def interpretHomFromProvider
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (provider : SealedClassicalOperationsProvider syntacticPresentation iface) :
    ∀ {X Y : DMgmObj syntacticPresentation},
      DMgmHom X Y →
        iface.presentation.motivicCategory.Hom
          (interpretObjFromProvider provider X)
          (interpretObjFromProvider provider Y)
  | _, _,   .image f     => provider.interpretBaseHom f
  | _, _,   .id X        => iface.presentation.motivicCategory.id
                              (interpretObjFromProvider provider X)
  | _, _,   .comp f g    => iface.presentation.motivicCategory.comp
                              (interpretHomFromProvider provider g)
                              (interpretHomFromProvider provider f)
  | _, _,   .shiftMap f  => provider.classicalShiftMap
                              (interpretHomFromProvider provider f)
  | _, _,   .tensorMap f g => provider.classicalTensorMap
                              (interpretHomFromProvider provider f)
                              (interpretHomFromProvider provider g)

-- ── Preservation theorems ─────────────────────────────────────────────────

/-- Identity preservation: holds by definitional reduction. -/
theorem interpret_id_from_provider
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (provider : SealedClassicalOperationsProvider syntacticPresentation iface)
    (X : DMgmObj syntacticPresentation) :
    interpretHomFromProvider provider (DMgmHom.id X) =
      iface.presentation.motivicCategory.id (interpretObjFromProvider provider X) :=
  rfl

/-- Composition preservation: holds by definitional reduction. -/
theorem interpret_comp_from_provider
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (provider : SealedClassicalOperationsProvider syntacticPresentation iface)
    {X Y Z : DMgmObj syntacticPresentation}
    (f : DMgmHom X Y) (g : DMgmHom Y Z) :
    interpretHomFromProvider provider (DMgmHom.comp f g) =
      iface.presentation.motivicCategory.comp
        (interpretHomFromProvider provider g)
        (interpretHomFromProvider provider f) :=
  rfl

/-- Image/π₀ preservation for the canonical trace-to-DMgm comparison package. -/
theorem interpret_pi0_class_from_provider
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (provider : SealedClassicalOperationsProvider syntacticPresentation iface)
    {X Y : TraceObj syntacticPresentation} (f : TraceHom X Y) :
  interpretHomFromProvider provider
    ((concreteTraceToDMgmComparisonTarget syntacticPresentation).homComparison f) =
      provider.interpretBaseHom f :=
  rfl

/-- Shift object preservation: holds by definitional reduction. -/
theorem interpret_shift_obj_from_provider
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (provider : SealedClassicalOperationsProvider syntacticPresentation iface)
    (X : DMgmObj syntacticPresentation) :
    interpretObjFromProvider provider (DMgmObj.shift X) =
      provider.classicalShiftObj (interpretObjFromProvider provider X) :=
  rfl

/-- Shift morphism preservation (heterogeneous): holds by HEq.rfl since the
LHS and RHS are definitionally equal after unfolding. -/
theorem interpret_shift_hom_from_provider
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (provider : SealedClassicalOperationsProvider syntacticPresentation iface)
    {X Y : DMgmObj syntacticPresentation} (f : DMgmHom X Y) :
    HEq (interpretHomFromProvider provider (DMgmHom.shiftMap f))
      (provider.classicalShiftMap (interpretHomFromProvider provider f)) :=
  HEq.rfl

/-- Cofiber object preservation: holds by definitional reduction. -/
theorem interpret_cofiber_from_provider
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (provider : SealedClassicalOperationsProvider syntacticPresentation iface)
    (X Y : DMgmObj syntacticPresentation) :
    interpretObjFromProvider provider (DMgmObj.cofiber X Y) =
      provider.classicalCofiberObj
        (interpretObjFromProvider provider X)
        (interpretObjFromProvider provider Y) :=
  rfl

/-- Tensor object preservation: holds by definitional reduction. -/
theorem interpret_tensor_obj_from_provider
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (provider : SealedClassicalOperationsProvider syntacticPresentation iface)
    (X Y : DMgmObj syntacticPresentation) :
    interpretObjFromProvider provider (DMgmObj.tensor X Y) =
      provider.classicalTensorObj
        (interpretObjFromProvider provider X)
        (interpretObjFromProvider provider Y) :=
  rfl

/-- Tensor morphism preservation (heterogeneous): holds by HEq.rfl. -/
theorem interpret_tensor_hom_from_provider
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (provider : SealedClassicalOperationsProvider syntacticPresentation iface)
    {A B C D : DMgmObj syntacticPresentation}
    (f : DMgmHom A B) (g : DMgmHom C D) :
    HEq (interpretHomFromProvider provider (DMgmHom.tensorMap f g))
      (provider.classicalTensorMap
        (interpretHomFromProvider provider f)
        (interpretHomFromProvider provider g)) :=
  HEq.rfl

/-- Dual object preservation: holds by definitional reduction. -/
theorem interpret_dual_from_provider
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (provider : SealedClassicalOperationsProvider syntacticPresentation iface)
    (X : DMgmObj syntacticPresentation) :
    interpretObjFromProvider provider (DMgmObj.dual X) =
      provider.classicalDualObj (interpretObjFromProvider provider X) :=
  rfl

theorem interpret_id_from_classicalOperationsData
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (data : ClassicalDMgmQOperationsData syntacticPresentation iface)
    (X : DMgmObj syntacticPresentation) :
    interpretHomFromProvider
        (SealedClassicalOperationsProvider.ofClassicalOperationsData data)
        (DMgmHom.id X) =
      iface.presentation.motivicCategory.id
        (interpretObjFromProvider
          (SealedClassicalOperationsProvider.ofClassicalOperationsData data) X) := by
  simpa using
    interpret_id_from_provider
      (SealedClassicalOperationsProvider.ofClassicalOperationsData data) X

theorem interpret_comp_from_classicalOperationsData
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (data : ClassicalDMgmQOperationsData syntacticPresentation iface)
    {X Y Z : DMgmObj syntacticPresentation}
    (f : DMgmHom X Y) (g : DMgmHom Y Z) :
    interpretHomFromProvider
        (SealedClassicalOperationsProvider.ofClassicalOperationsData data)
        (DMgmHom.comp f g) =
      iface.presentation.motivicCategory.comp
        (interpretHomFromProvider
          (SealedClassicalOperationsProvider.ofClassicalOperationsData data) g)
        (interpretHomFromProvider
          (SealedClassicalOperationsProvider.ofClassicalOperationsData data) f) := by
  simpa using
    interpret_comp_from_provider
      (SealedClassicalOperationsProvider.ofClassicalOperationsData data) f g

theorem interpret_pi0_class_from_classicalOperationsData
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (data : ClassicalDMgmQOperationsData syntacticPresentation iface)
    {X Y : TraceObj syntacticPresentation} (f : TraceHom X Y) :
    interpretHomFromProvider
        (SealedClassicalOperationsProvider.ofClassicalOperationsData data)
        ((concreteTraceToDMgmComparisonTarget syntacticPresentation).homComparison f) =
      data.interpretBaseHom f := by
  simpa using
    interpret_pi0_class_from_provider
      (SealedClassicalOperationsProvider.ofClassicalOperationsData data) f

theorem interpret_shift_obj_from_classicalOperationsData
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (data : ClassicalDMgmQOperationsData syntacticPresentation iface)
    (X : DMgmObj syntacticPresentation) :
    interpretObjFromProvider
        (SealedClassicalOperationsProvider.ofClassicalOperationsData data)
        (DMgmObj.shift X) =
      data.classicalShiftObj
        (interpretObjFromProvider
          (SealedClassicalOperationsProvider.ofClassicalOperationsData data) X) := by
  simpa using
    interpret_shift_obj_from_provider
      (SealedClassicalOperationsProvider.ofClassicalOperationsData data) X

theorem interpret_shift_hom_from_classicalOperationsData
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (data : ClassicalDMgmQOperationsData syntacticPresentation iface)
    {X Y : DMgmObj syntacticPresentation} (f : DMgmHom X Y) :
    HEq
      (interpretHomFromProvider
        (SealedClassicalOperationsProvider.ofClassicalOperationsData data)
        (DMgmHom.shiftMap f))
      (data.classicalShiftMap
        (interpretHomFromProvider
          (SealedClassicalOperationsProvider.ofClassicalOperationsData data) f)) := by
  simpa using
    interpret_shift_hom_from_provider
      (SealedClassicalOperationsProvider.ofClassicalOperationsData data) f

theorem interpret_cofiber_from_classicalOperationsData
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (data : ClassicalDMgmQOperationsData syntacticPresentation iface)
    (X Y : DMgmObj syntacticPresentation) :
    interpretObjFromProvider
        (SealedClassicalOperationsProvider.ofClassicalOperationsData data)
        (DMgmObj.cofiber X Y) =
      data.classicalCofiberObj
        (interpretObjFromProvider
          (SealedClassicalOperationsProvider.ofClassicalOperationsData data) X)
        (interpretObjFromProvider
          (SealedClassicalOperationsProvider.ofClassicalOperationsData data) Y) := by
  simpa using
    interpret_cofiber_from_provider
      (SealedClassicalOperationsProvider.ofClassicalOperationsData data) X Y

theorem interpret_tensor_obj_from_classicalOperationsData
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (data : ClassicalDMgmQOperationsData syntacticPresentation iface)
    (X Y : DMgmObj syntacticPresentation) :
    interpretObjFromProvider
        (SealedClassicalOperationsProvider.ofClassicalOperationsData data)
        (DMgmObj.tensor X Y) =
      data.classicalTensorObj
        (interpretObjFromProvider
          (SealedClassicalOperationsProvider.ofClassicalOperationsData data) X)
        (interpretObjFromProvider
          (SealedClassicalOperationsProvider.ofClassicalOperationsData data) Y) := by
  simpa using
    interpret_tensor_obj_from_provider
      (SealedClassicalOperationsProvider.ofClassicalOperationsData data) X Y

theorem interpret_tensor_hom_from_classicalOperationsData
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (data : ClassicalDMgmQOperationsData syntacticPresentation iface)
    {A B C D : DMgmObj syntacticPresentation}
    (f : DMgmHom A B) (g : DMgmHom C D) :
    HEq
      (interpretHomFromProvider
        (SealedClassicalOperationsProvider.ofClassicalOperationsData data)
        (DMgmHom.tensorMap f g))
      (data.classicalTensorMap
        (interpretHomFromProvider
          (SealedClassicalOperationsProvider.ofClassicalOperationsData data) f)
        (interpretHomFromProvider
          (SealedClassicalOperationsProvider.ofClassicalOperationsData data) g)) := by
  simpa using
    interpret_tensor_hom_from_provider
      (SealedClassicalOperationsProvider.ofClassicalOperationsData data) f g

theorem interpret_dual_from_classicalOperationsData
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (data : ClassicalDMgmQOperationsData syntacticPresentation iface)
    (X : DMgmObj syntacticPresentation) :
    interpretObjFromProvider
        (SealedClassicalOperationsProvider.ofClassicalOperationsData data)
        (DMgmObj.dual X) =
      data.classicalDualObj
        (interpretObjFromProvider
          (SealedClassicalOperationsProvider.ofClassicalOperationsData data) X) := by
  simpa using
    interpret_dual_from_provider
      (SealedClassicalOperationsProvider.ofClassicalOperationsData data) X

-- ── ofSealedPackages ──────────────────────────────────────────────────────

namespace SyntacticDMgmClassicalInterpretationData

/-- Canonical Package 6 interpretation constructor from operation-level
classical data.

The structural recursion still runs through the internal provider helper, but
the public P6B route now starts from concrete operation data rather than from
an extra provider-level wrapper. -/
def ofClassicalOperationsData
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (data : ClassicalDMgmQOperationsData syntacticPresentation iface) :
    SyntacticDMgmClassicalInterpretationData syntacticPresentation iface where
  interpretObj :=
    interpretObjFromProvider
      (SealedClassicalOperationsProvider.ofClassicalOperationsData data)
  interpretHom :=
    interpretHomFromProvider
      (SealedClassicalOperationsProvider.ofClassicalOperationsData data)
  interpretPi0 := fun f => data.interpretBaseHom f
  classicalShiftObj := data.classicalShiftObj
  classicalShiftMap := data.classicalShiftMap
  classicalTensorObj := data.classicalTensorObj
  classicalTensorMap := data.classicalTensorMap
  classicalCofiberObj := data.classicalCofiberObj
  classicalDualObj := data.classicalDualObj
  identityPreservation := interpret_id_from_classicalOperationsData data
  compositionPreservation := interpret_comp_from_classicalOperationsData data
  imagePi0Preservation := interpret_pi0_class_from_classicalOperationsData data
  shiftObjPreservation := interpret_shift_obj_from_classicalOperationsData data
  shiftHomPreservation := interpret_shift_hom_from_classicalOperationsData data
  cofiberObjPreservation := interpret_cofiber_from_classicalOperationsData data
  tensorObjPreservation := interpret_tensor_obj_from_classicalOperationsData data
  tensorHomPreservation := interpret_tensor_hom_from_classicalOperationsData data
  dualObjPreservation := interpret_dual_from_classicalOperationsData data
  p3bAssignmentTable := data.p3bAssignmentTable
  p3bAdmissibilityComparison := data.p3bAdmissibilityComparison

/-- Direct Package 6 interpretation constructor from the existing operational
`DMgmQPiZeroInterface`. -/
def ofSealedSources
    (syntacticPresentation : Type u)
    (iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}) :
    SyntacticDMgmClassicalInterpretationData syntacticPresentation iface :=
  ofClassicalOperationsData
    (ClassicalDMgmQOperationsData.ofSealedSources syntacticPresentation iface)

end SyntacticDMgmClassicalInterpretationData

-- ── Final Package 6 constructor from sealed operations ───────────────────

/-- Canonical Package 6 constructor directly from operation-level classical
data. -/
def finalPackage6ClassicalSeal_from_classicalOperationsData
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (data : ClassicalDMgmQOperationsData syntacticPresentation iface) :
    SyntacticDMgmClassicalRecognitionTarget syntacticPresentation iface :=
  SyntacticDMgmClassicalRecognitionTarget.ofInterpretationData
    (SyntacticDMgmClassicalInterpretationData.ofClassicalOperationsData data)

theorem finalPackage6ClassicalSeal_from_classicalOperationsData_reaches_target
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (data : ClassicalDMgmQOperationsData syntacticPresentation iface) :
    (finalPackage6ClassicalSeal_from_classicalOperationsData data).classicalTarget =
      iface.target :=
  rfl

theorem finalPackage6ClassicalSealFromClassicalOperationsDataBridgeWitness
    {syntacticPresentation : Type u}
    {iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (data : ClassicalDMgmQOperationsData syntacticPresentation iface) :
    (finalPackage6ClassicalSeal_from_classicalOperationsData data).bridge.objectInterpretationTarget ∧
      (finalPackage6ClassicalSeal_from_classicalOperationsData data).bridge.morphismInterpretationTarget ∧
      (finalPackage6ClassicalSeal_from_classicalOperationsData data).bridge.presentationPreservationTarget ∧
      (finalPackage6ClassicalSeal_from_classicalOperationsData data).bridge.stableCompletionPreservationTarget ∧
      (finalPackage6ClassicalSeal_from_classicalOperationsData data).bridge.piZeroCompatibilityTarget ∧
      (finalPackage6ClassicalSeal_from_classicalOperationsData data).bridge.fullFaithfulnessRecognitionTarget :=
  (finalPackage6ClassicalSeal_from_classicalOperationsData data).bridgeRecognitionWitness

/-- Canonical internal Package 6 constructor from the existing operational
`DMgmQPiZeroInterface`.

This is the sealed P6B route used by downstream packages: all operation-level
classical data are projected from the existing interface, so no extra provider
parameter remains at the final constructor surface. -/
def finalPackage6ClassicalSeal_from_sealedSources
    (syntacticPresentation : Type u)
    (iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}) :
    SyntacticDMgmClassicalRecognitionTarget syntacticPresentation iface :=
  finalPackage6ClassicalSeal_from_classicalOperationsData
    (ClassicalDMgmQOperationsData.ofSealedSources syntacticPresentation iface)

theorem finalPackage6ClassicalSeal_from_sealedSources_reaches_target
    (syntacticPresentation : Type u)
    (iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}) :
    (finalPackage6ClassicalSeal_from_sealedSources syntacticPresentation iface).classicalTarget =
      iface.target :=
  rfl

theorem finalPackage6ClassicalSealFromSealedSourcesBridgeWitness
    (syntacticPresentation : Type u)
    (iface : LayerD.DMgmQPiZeroInterface.{u, v, w, x, y, z}) :
    (finalPackage6ClassicalSeal_from_sealedSources syntacticPresentation iface).bridge.objectInterpretationTarget ∧
      (finalPackage6ClassicalSeal_from_sealedSources syntacticPresentation iface).bridge.morphismInterpretationTarget ∧
      (finalPackage6ClassicalSeal_from_sealedSources syntacticPresentation iface).bridge.presentationPreservationTarget ∧
      (finalPackage6ClassicalSeal_from_sealedSources syntacticPresentation iface).bridge.stableCompletionPreservationTarget ∧
      (finalPackage6ClassicalSeal_from_sealedSources syntacticPresentation iface).bridge.piZeroCompatibilityTarget ∧
      (finalPackage6ClassicalSeal_from_sealedSources syntacticPresentation iface).bridge.fullFaithfulnessRecognitionTarget :=
  (finalPackage6ClassicalSeal_from_sealedSources syntacticPresentation iface)
    |>.bridgeRecognitionWitness

end MotivicRecognition
end TraceCalc

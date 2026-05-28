import TraceCalc.LayerD.MotivicRecognition.LocalizationAxioms
import TraceCalc.ClassicalPeriods.Package3BGeneratorSoundness
import TraceCalc.ClassicalPeriods.Package3B1CorrespondenceFunctoriality
import TraceCalc.ClassicalPeriods.Package3B2Localization
import TraceCalc.ClassicalPeriods.Package3B3Nisnevich
import TraceCalc.ClassicalPeriods.Package3B4A1
import TraceCalc.ClassicalPeriods.Package3B5Envelope

universe u v w x y z

namespace TraceCalc
namespace MotivicRecognition

/-!
LayerD canonical location for the sealed admissible-localization proof package.

The top-level `TraceCalc.MotivicRecognition.Package3BProofs` module is now a
compatibility wrapper.
-/

/-! ## Package 3B.1: Corr Functoriality - Proof Wrapper and Field Proofs -/

/-- Specification target: wire abstract target to classical generator data.

This defines what the Prop fields should be, without providing proofs yet.
-/
def CorrFunctorialityTarget.ofClassicalGeneratorRealization
    {trace : TracePresentation.{u, v, w, x, y}}
    {motivic : MotivicCategoryCandidate trace.base}
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx)
    : CorrFunctorialityTarget trace motivic where
  Corr := assignmentTable.corrAssignment.family.GeneratorIndex
  correspondenceIdentityTarget :=
    ∀ {X Y : ClassicalPeriods.GeometricPeriodObject.{u, v, w} ctx}
      (α : ClassicalPeriods.Package3B0.FiniteCorrespondence.{u, v, w} X Y),
      ClassicalPeriods.Package3B0.FiniteCorrespondence.composeCorrespondence
        (ClassicalPeriods.Package3B0.FiniteCorrespondence.identityCorrespondence X) α = α
  correspondenceCompositionTarget :=
    ∀ {W X Y Z : ClassicalPeriods.GeometricPeriodObject.{u, v, w} ctx}
      (α : ClassicalPeriods.Package3B0.FiniteCorrespondence.{u, v, w} W X)
      (β : ClassicalPeriods.Package3B0.FiniteCorrespondence.{u, v, w} X Y)
      (γ : ClassicalPeriods.Package3B0.FiniteCorrespondence.{u, v, w} Y Z),
      ClassicalPeriods.Package3B0.FiniteCorrespondence.composeCorrespondence
        (ClassicalPeriods.Package3B0.FiniteCorrespondence.composeCorrespondence α β) γ =
      ClassicalPeriods.Package3B0.FiniteCorrespondence.composeCorrespondence α
        (ClassicalPeriods.Package3B0.FiniteCorrespondence.composeCorrespondence β γ)
  theoremTarget :=
    ClassicalPeriods.CorrPacketSoundnessFromGeneratorRealizationTarget assignmentTable

/-- Certified wrapper: CorrFunctorialityTarget with internal proofs of all three fields.

The proof fields correspond exactly to the Prop-valued fields in the target.
-/
structure CertifiedCorrFunctorialityTarget
    {trace : TracePresentation.{u, v, w, x, y}}
    {motivic : MotivicCategoryCandidate trace.base}
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx) where
  target : CorrFunctorialityTarget trace motivic :=
    CorrFunctorialityTarget.ofClassicalGeneratorRealization assignmentTable
  /-- Internal proof: identity law holds for all generators. -/
  correspondenceIdentity_holds :
    target.correspondenceIdentityTarget
  /-- Internal proof: composition law holds for all generator pairs. -/
  correspondenceComposition_holds :
    target.correspondenceCompositionTarget
  /-- Internal proof: packet is sound under realization. -/
  theorem_holds :
    target.theoremTarget

/-- Proof 1: Identity law from generator correspondence structure.

Each generator's correspondence structure has an identityTarget field.
We extract these for all generators to prove the universal statement.
-/
theorem corr_identity_holds
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx)
    : ∀ {X Y : ClassicalPeriods.GeometricPeriodObject.{u, v, w} ctx}
        (α : ClassicalPeriods.Package3B0.FiniteCorrespondence.{u, v, w, w} X Y),
        ClassicalPeriods.Package3B0.FiniteCorrespondence.composeCorrespondence
          (ClassicalPeriods.Package3B0.FiniteCorrespondence.identityCorrespondence X) α = α :=
  fun α =>
    ClassicalPeriods.Package3B1.corr_identity_holds_from_finite_correspondences α

/-- Proof 2: Composition law from generator correspondence structure.

Each generator's correspondence structure has a compositionTarget field.
We extract these for all generator pairs to prove the universal statement.
-/
theorem corr_composition_holds
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx)
    : ∀ {W X Y Z : ClassicalPeriods.GeometricPeriodObject.{u, v, w} ctx}
        (α : ClassicalPeriods.Package3B0.FiniteCorrespondence.{u, v, w, w} W X)
        (β : ClassicalPeriods.Package3B0.FiniteCorrespondence.{u, v, w, w} X Y)
        (γ : ClassicalPeriods.Package3B0.FiniteCorrespondence.{u, v, w, w} Y Z),
        ClassicalPeriods.Package3B0.FiniteCorrespondence.composeCorrespondence
          (ClassicalPeriods.Package3B0.FiniteCorrespondence.composeCorrespondence α β) γ =
        ClassicalPeriods.Package3B0.FiniteCorrespondence.composeCorrespondence α
          (ClassicalPeriods.Package3B0.FiniteCorrespondence.composeCorrespondence β γ) :=
  fun α β γ =>
    ClassicalPeriods.Package3B1.corr_composition_holds_from_finite_correspondences α β γ

/-- Proof 3: Theorem target from classical packet soundness.

The complete correspondence functoriality (identity + composition + comparison targets).
This is exactly what the classical proof witnesses.
-/
theorem corr_theorem_holds
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx)
    : ClassicalPeriods.CorrPacketSoundnessFromGeneratorRealizationTarget assignmentTable :=
  ClassicalPeriods.corrPacketSoundnessFromGeneratorRealization assignmentTable

/-- Constructor: CertifiedCorrFunctorialityTarget from classical realization.

Assembles the three proofs into the certified wrapper using the specification target.
-/
def CertifiedCorrFunctorialityTarget.ofClassicalGeneratorRealization
    {trace : TracePresentation.{u, v, w, x, y}}
    {motivic : MotivicCategoryCandidate trace.base}
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx)
    : CertifiedCorrFunctorialityTarget (trace := trace) (motivic := motivic) assignmentTable where
  target := CorrFunctorialityTarget.ofClassicalGeneratorRealization assignmentTable
  correspondenceIdentity_holds := corr_identity_holds assignmentTable
  correspondenceComposition_holds := corr_composition_holds assignmentTable
  theorem_holds := corr_theorem_holds assignmentTable

/-! ## Package 3B.2: Open/Closed Localization - Proof Wrapper and Field Proofs -/

def OpenClosedLocalizationTarget.ofClassicalGeneratorRealization
    {trace : TracePresentation.{u, v, w, x, y}}
    {motivic : MotivicCategoryCandidate trace.base}
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx) :
    OpenClosedLocalizationTarget trace motivic where
  OpenPiece := assignmentTable.locAssignment.family.GeneratorIndex
  ClosedPiece := assignmentTable.locAssignment.family.GeneratorIndex
  localizationTriangleTarget := assignmentTable.locAssignment.triangleCompatibilityTarget
  gluingCompatibilityTarget :=
    assignmentTable.locAssignment.coneNaturalityData.connectingMorphismCompatibilityTarget
  theoremTarget :=
    ClassicalPeriods.LocPacketPeriodCompatibilityFromGeneratorRealizationTarget assignmentTable ∧
      assignmentTable.locAssignment.triangleCompatibilityTarget

structure CertifiedOpenClosedLocalizationTarget
    {trace : TracePresentation.{u, v, w, x, y}}
    {motivic : MotivicCategoryCandidate trace.base}
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx) where
  target : OpenClosedLocalizationTarget trace motivic :=
    OpenClosedLocalizationTarget.ofClassicalGeneratorRealization assignmentTable
  localizationTriangle_holds : target.localizationTriangleTarget
  gluingCompatibility_holds : target.gluingCompatibilityTarget
  theorem_holds : target.theoremTarget

theorem loc_localizationTriangle_holds
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx) :
    assignmentTable.locAssignment.triangleCompatibilityTarget :=
  ClassicalPeriods.Package3B2.loc_localizationTriangle_holds assignmentTable

theorem loc_gluingCompatibility_holds
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx) :
    assignmentTable.locAssignment.coneNaturalityData.connectingMorphismCompatibilityTarget :=
  ClassicalPeriods.Package3B2.loc_gluingCompatibility_holds assignmentTable

theorem loc_theorem_holds
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx) :
    ClassicalPeriods.LocPacketPeriodCompatibilityFromGeneratorRealizationTarget assignmentTable ∧
      assignmentTable.locAssignment.triangleCompatibilityTarget :=
  ClassicalPeriods.Package3B2.loc_theoremTarget_holds assignmentTable

def CertifiedOpenClosedLocalizationTarget.ofClassicalGeneratorRealization
    {trace : TracePresentation.{u, v, w, x, y}}
    {motivic : MotivicCategoryCandidate trace.base}
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx) :
    CertifiedOpenClosedLocalizationTarget (trace := trace) (motivic := motivic) assignmentTable where
  target := OpenClosedLocalizationTarget.ofClassicalGeneratorRealization assignmentTable
  localizationTriangle_holds := loc_localizationTriangle_holds assignmentTable
  gluingCompatibility_holds := loc_gluingCompatibility_holds assignmentTable
  theorem_holds := loc_theorem_holds assignmentTable

/-! ## Package 3B.3: Nisnevich Descent - Proof Wrapper and Field Proofs -/

def NisnevichDescentTarget.ofClassicalGeneratorRealization
    {trace : TracePresentation.{u, v, w, x, y}}
    {motivic : MotivicCategoryCandidate trace.base}
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx) :
    NisnevichDescentTarget trace motivic where
  Nis := assignmentTable.nisAssignment.family.GeneratorIndex
  coverDescentTarget :=
    ClassicalPeriods.NisPacketComparisonFromGeneratorRealizationTarget assignmentTable
  hyperdescentTarget := assignmentTable.nisAssignment.descentSquareCompatibilityTarget
  theoremTarget :=
    ClassicalPeriods.NisPacketComparisonFromGeneratorRealizationTarget assignmentTable ∧
      assignmentTable.nisAssignment.descentSquareCompatibilityTarget

structure CertifiedNisnevichDescentTarget
    {trace : TracePresentation.{u, v, w, x, y}}
    {motivic : MotivicCategoryCandidate trace.base}
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx) where
  target : NisnevichDescentTarget trace motivic :=
    NisnevichDescentTarget.ofClassicalGeneratorRealization assignmentTable
  coverDescent_holds : target.coverDescentTarget
  hyperdescent_holds : target.hyperdescentTarget
  theorem_holds : target.theoremTarget

theorem nis_coverDescent_holds
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx) :
    ClassicalPeriods.NisPacketComparisonFromGeneratorRealizationTarget assignmentTable :=
  ClassicalPeriods.Package3B3.nis_coverDescent_holds assignmentTable

theorem nis_hyperdescent_holds
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx) :
    assignmentTable.nisAssignment.descentSquareCompatibilityTarget :=
  ClassicalPeriods.Package3B3.nis_hyperdescent_holds assignmentTable

theorem nis_theorem_holds
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx) :
    ClassicalPeriods.NisPacketComparisonFromGeneratorRealizationTarget assignmentTable ∧
      assignmentTable.nisAssignment.descentSquareCompatibilityTarget :=
  ClassicalPeriods.Package3B3.nis_theoremTarget_holds assignmentTable

def CertifiedNisnevichDescentTarget.ofClassicalGeneratorRealization
    {trace : TracePresentation.{u, v, w, x, y}}
    {motivic : MotivicCategoryCandidate trace.base}
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx) :
    CertifiedNisnevichDescentTarget (trace := trace) (motivic := motivic) assignmentTable where
  target := NisnevichDescentTarget.ofClassicalGeneratorRealization assignmentTable
  coverDescent_holds := nis_coverDescent_holds assignmentTable
  hyperdescent_holds := nis_hyperdescent_holds assignmentTable
  theorem_holds := nis_theorem_holds assignmentTable

/-! ## Package 3B.4: A¹ Invariance - Proof Wrapper and Field Proofs -/

def A1InvarianceTarget.ofClassicalGeneratorRealization
    {trace : TracePresentation.{u, v, w, x, y}}
    {motivic : MotivicCategoryCandidate trace.base}
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx) :
    A1InvarianceTarget trace motivic where
  A1 := assignmentTable.a1Assignment.family.GeneratorIndex
  intervalObjectTarget :=
    ClassicalPeriods.A1PacketComparisonFromGeneratorRealizationTarget assignmentTable
  homotopyInvarianceTarget := assignmentTable.a1Assignment.framedExtractionTarget
  theoremTarget :=
    ClassicalPeriods.A1PacketComparisonFromGeneratorRealizationTarget assignmentTable ∧
      assignmentTable.a1Assignment.framedExtractionTarget

structure CertifiedA1InvarianceTarget
    {trace : TracePresentation.{u, v, w, x, y}}
    {motivic : MotivicCategoryCandidate trace.base}
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx) where
  target : A1InvarianceTarget trace motivic :=
    A1InvarianceTarget.ofClassicalGeneratorRealization assignmentTable
  intervalObject_holds : target.intervalObjectTarget
  homotopyInvariance_holds : target.homotopyInvarianceTarget
  theorem_holds : target.theoremTarget

theorem a1_intervalObject_holds
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx) :
    ClassicalPeriods.A1PacketComparisonFromGeneratorRealizationTarget assignmentTable :=
  ClassicalPeriods.Package3B4.a1_intervalObject_holds assignmentTable

theorem a1_homotopyInvariance_holds
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx) :
    assignmentTable.a1Assignment.framedExtractionTarget :=
  ClassicalPeriods.Package3B4.a1_homotopyInvariance_holds assignmentTable

theorem a1_theorem_holds
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx) :
    ClassicalPeriods.A1PacketComparisonFromGeneratorRealizationTarget assignmentTable ∧
      assignmentTable.a1Assignment.framedExtractionTarget :=
  ClassicalPeriods.Package3B4.a1_theoremTarget_holds assignmentTable

def CertifiedA1InvarianceTarget.ofClassicalGeneratorRealization
    {trace : TracePresentation.{u, v, w, x, y}}
    {motivic : MotivicCategoryCandidate trace.base}
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx) :
    CertifiedA1InvarianceTarget (trace := trace) (motivic := motivic) assignmentTable where
  target := A1InvarianceTarget.ofClassicalGeneratorRealization assignmentTable
  intervalObject_holds := a1_intervalObject_holds assignmentTable
  homotopyInvariance_holds := a1_homotopyInvariance_holds assignmentTable
  theorem_holds := a1_theorem_holds assignmentTable

/-! ## Package 3B.5: Envelope Exactness - Proof Wrapper and Field Proofs -/

def EnvelopeExactnessTarget.ofClassicalGeneratorRealization
    {trace : TracePresentation.{u, v, w, x, y}}
    {motivic : MotivicCategoryCandidate trace.base}
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx) :
    EnvelopeExactnessTarget trace motivic where
  Env := assignmentTable.envAssignment.family.GeneratorIndex
  envelopeFunctorialityTarget :=
    ClassicalPeriods.EnvPacketComparisonFromGeneratorRealizationTarget assignmentTable
  exactnessTarget := assignmentTable.envAssignment.exactCompletionTarget
  theoremTarget :=
    ClassicalPeriods.EnvPacketComparisonFromGeneratorRealizationTarget assignmentTable ∧
      assignmentTable.envAssignment.exactCompletionTarget

structure CertifiedEnvelopeExactnessTarget
    {trace : TracePresentation.{u, v, w, x, y}}
    {motivic : MotivicCategoryCandidate trace.base}
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx) where
  target : EnvelopeExactnessTarget trace motivic :=
    EnvelopeExactnessTarget.ofClassicalGeneratorRealization assignmentTable
  envelopeFunctoriality_holds : target.envelopeFunctorialityTarget
  exactness_holds : target.exactnessTarget
  theorem_holds : target.theoremTarget

theorem env_envelopeFunctoriality_holds
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx) :
    ClassicalPeriods.EnvPacketComparisonFromGeneratorRealizationTarget assignmentTable :=
  ClassicalPeriods.Package3B5.env_envelopeFunctoriality_holds assignmentTable

theorem env_exactness_holds
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx) :
    assignmentTable.envAssignment.exactCompletionTarget :=
  ClassicalPeriods.Package3B5.env_exactness_holds assignmentTable

theorem env_theorem_holds
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx) :
    ClassicalPeriods.EnvPacketComparisonFromGeneratorRealizationTarget assignmentTable ∧
      assignmentTable.envAssignment.exactCompletionTarget :=
  ClassicalPeriods.Package3B5.env_theoremTarget_holds assignmentTable

def CertifiedEnvelopeExactnessTarget.ofClassicalGeneratorRealization
    {trace : TracePresentation.{u, v, w, x, y}}
    {motivic : MotivicCategoryCandidate trace.base}
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx) :
    CertifiedEnvelopeExactnessTarget (trace := trace) (motivic := motivic) assignmentTable where
  target := EnvelopeExactnessTarget.ofClassicalGeneratorRealization assignmentTable
  envelopeFunctoriality_holds := env_envelopeFunctoriality_holds assignmentTable
  exactness_holds := env_exactness_holds assignmentTable
  theorem_holds := env_theorem_holds assignmentTable

end MotivicRecognition
end TraceCalc

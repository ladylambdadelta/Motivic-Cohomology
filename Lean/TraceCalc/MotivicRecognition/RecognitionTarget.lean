import TraceCalc.ClassicalBridge.ClassicalBridgeAnchors
import TraceCalc.ClassicalPeriods.ClassicalManuscriptTargets
import TraceCalc.ClassicalPeriods.TraceCategory
import TraceCalc.LayerB.Reconstruction
import TraceCalc.LayerE.TargetComparisonPackage
import TraceCalc.MotivicRecognition.LocalizationAxioms
import TraceCalc.MotivicRecognition.TracePresentation

universe u v w x y z

namespace TraceCalc
namespace MotivicRecognition

/-- Typed classical/geometric presentation expected downstream of trace recognition. -/
structure ClassicalMotivicPresentation
    (trace : TracePresentation.{u, v, w, x, y}) where
  bridgePresentation : ClassicalBridge.ClassicalMotivicPresentation
  bridgePresentationAgreementTarget :
    bridgePresentation = trace.sourceRealization.classicalPresentation
  motivicCategory : MotivicCategoryCandidate.{u, v, z, z} trace.base
  traceLocalizationReadiness : TraceLocalizationReadiness trace motivicCategory
  admissibleLocalizationAxioms : AdmissibleLocalizationAxioms trace motivicCategory
  classicalContext : ClassicalBridge.ClassicalComparisonContext.{u, v}
  structuredComparisonEquality : ClassicalBridge.StructuredComparisonEquality classicalContext
  geometricObjectInterpretationTarget : Prop
  correspondenceInterpretationTarget : Prop
  realizationFunctorCompatibilityTarget : Prop
  classicalPeriodsComparisonTarget : Prop
  periodTomographyCompatibilityTarget : Prop
  internalHolographyFeedsComparisonTarget : Prop

/-- Universe-polymorphic concrete identification of a type `F` with the rational
numbers `ℚ` (`Rat`).

Carries an explicit inverse pair witnessing that `F` is bijective-with-`ℚ` at
the set level.  Used to give `ClassicalDMgmQTarget.baseFieldIsQTarget` and
`coefficientFieldIsQTarget` a concrete, data-bearing type that type-checks in
any universe rather than relying on literal `Type`-equality with `Rat`. -/
structure FieldIsQData (F : Type u) where
  toRat   : F   → Rat
  fromRat : Rat → F
  left_inv  : ∀ (x : F),   fromRat (toRat x) = x
  right_inv : ∀ (q : Rat), toRat  (fromRat q) = q

namespace FieldIsQData

/-- The identity `FieldIsQData` on `Rat` itself. -/
def id : FieldIsQData Rat :=
  { toRat   := _root_.id
    fromRat := _root_.id
    left_inv  := fun _ => rfl
    right_inv := fun _ => rfl }

end FieldIsQData

/-- Named classical theorem boundary for the Corr/Loc/Nis/A1/Env facts used by
the `DM_gm(Q)_Q` recognition path.

These fields are deliberately the exact theorem targets exposed by
`ClassicalMotivicPresentation`. This package is the place where external
classical motivic inputs enter the recognition lane; downstream constructors
should consume this package rather than taking scattered anonymous theorem
inhabitants. -/
structure ClassicalDMgmQPresentationTheorems
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace) where
  corr_holds : presentation.admissibleLocalizationAxioms.Corr.theoremTarget
  loc_holds : presentation.admissibleLocalizationAxioms.Loc.theoremTarget
  nis_holds : presentation.admissibleLocalizationAxioms.Nis.theoremTarget
  a1_holds : presentation.admissibleLocalizationAxioms.A1.theoremTarget
  env_holds : presentation.admissibleLocalizationAxioms.Env.theoremTarget
  env_exactness_holds : presentation.admissibleLocalizationAxioms.Env.exactnessTarget

/-- Proof-relevant package recording how finite certified trace expressions in
the five primitive families account for the compact/geometric classical target
of `DM_gm(Q)_Q`. -/
structure TraceCompactGenerationData
    (trace : TracePresentation.{u, v, w, x, y})
    (presentation : ClassicalMotivicPresentation trace) where
  GeneratorCarrier : Type z
  generatorCarrier : GeneratorCarrier
  traceGenerator : GeneratorCarrier → trace.TraceObject
  classicalCompactObject : GeneratorCarrier → presentation.motivicCategory.Object
  finiteBoundaryRecordTarget : GeneratorCarrier → Prop
  theoremPackage : ClassicalDMgmQPresentationTheorems presentation
  FiniteTraceClosureCarrier : Type z
  finiteTraceClosure : FiniteTraceClosureCarrier → trace.TraceObject
  reconstructCompactObject : FiniteTraceClosureCarrier → presentation.motivicCategory.Object
  reconstructionFromFiniteTraceClosureTarget : Prop
  boundaryInformationPreservationTarget : Prop
  compactGenerationTarget : Prop

/-- Proof-relevant triangulated/exact coherence data extracted from shift,
cone, cofiber, and localization packets on the trace side. -/
structure TraceTriangulatedCoherenceData
    (trace : TracePresentation.{u, v, w, x, y})
    (presentation : ClassicalMotivicPresentation trace) where
  ShiftWitnessCarrier : Type z
  shiftWitnessCarrier : ShiftWitnessCarrier
  ConeWitnessCarrier : Type z
  coneWitnessCarrier : ConeWitnessCarrier
  CofiberWitnessCarrier : Type z
  cofiberWitnessCarrier : CofiberWitnessCarrier
  LocalizationTriangleWitnessCarrier : Type z
  localizationTriangleWitnessCarrier : LocalizationTriangleWitnessCarrier
  boundaryVisibleShiftTarget : Prop
  boundaryVisibleConeTarget : Prop
  boundaryVisibleCofiberTarget : Prop
  localizationTriangleGenerationTarget : presentation.admissibleLocalizationAxioms.Loc.theoremTarget
  rotationPreservation : Prop
  coneFunctoriality : Prop
  octahedralBoundaryDecomposition : Prop
  locTriangleCompatibility : Prop
  envelopeExactTriangleClosure : presentation.admissibleLocalizationAxioms.Env.exactnessTarget
  exactTriangulatedStructureTarget : Prop

/-- Proof-relevant tensor exactness package used by the monoidal recognition
layer. This keeps tensor exactness explicit when it is available from
cone/localization preservation rather than hiding it in a generic coherence
field. -/
structure TraceTensorExactnessData
    (trace : TracePresentation.{u, v, w, x, y})
    (presentation : ClassicalMotivicPresentation trace) where
  TensorExactnessWitnessCarrier : Type z
  tensorExactnessWitnessCarrier : TensorExactnessWitnessCarrier
  tensorPreservesConeTarget : Prop
  tensorPreservesLocalizationTarget : Prop
  tensorPreservesCofiberTarget : Prop
  tensorExactnessTarget : Prop

/-- Proof-relevant symmetric monoidal coherence data extracted from the
Campaign 9 trace-category tensor layer. -/
structure TraceSymmetricMonoidalCoherenceData
    (trace : TracePresentation.{u, v, w, x, y})
    (presentation : ClassicalMotivicPresentation trace) where
  tensorPreservesBoundaryRecordsTarget : Prop
  tensorPreservesSupportGluingDataTarget : Prop
  tensorPreservesFiveFamilyClosureTarget : Prop
  unitCompatibilityTarget : Prop
  associativityCompatibilityTarget : Prop
  braidingCompatibilityTarget : Prop
  tensorExactness : TraceTensorExactnessData.{u, v, w, x, y, z} trace presentation
  symmetricMonoidalStructureTarget : Prop

/-- Single owner package for the remaining hard `DM_gm(Q)_Q` recognition
content.

This keeps compact generation, exact/triangulated structure, and symmetric
monoidality tied to one trace-native information-preservation theorem surface
rather than treating them as unrelated category-theory axioms. -/
structure TraceAbsoluteInformationPreservation
    (trace : TracePresentation.{u, v, w, x, y})
    (presentation : ClassicalMotivicPresentation trace) where
  compactGenerationData : TraceCompactGenerationData.{u, v, w, x, y, z} trace presentation
  triangulatedCoherenceData : TraceTriangulatedCoherenceData.{u, v, w, x, y, z} trace presentation
  symmetricMonoidalCoherenceData : TraceSymmetricMonoidalCoherenceData.{u, v, w, x, y, z} trace presentation

/-- Explicit recognition-side interface for the intended classical target
`DM_gm(Q)_Q`.

This does not pretend the concrete Voevodsky construction is already present in
Lean. Instead it pins the target by name and by the exact motivic features the
recognition layer needs to see: rational base and coefficients, finite
correspondences/transfers, localization, Nisnevich descent, `A1`-invariance,
symmetric monoidality, triangulated exactness, and idempotent closure. -/
structure ClassicalDMgmQTarget
    (trace : TracePresentation.{u, v, w, x, y})
    (presentation : ClassicalMotivicPresentation trace) where
  BaseFieldWitness : Type z
  baseFieldWitness : BaseFieldWitness
  CoefficientFieldWitness : Type z
  coefficientFieldWitness : CoefficientFieldWitness
  baseFieldIsQTarget : FieldIsQData BaseFieldWitness
  coefficientFieldIsQTarget : FieldIsQData CoefficientFieldWitness
  finiteCorrespondenceTransfers :
    CorrFunctorialityTarget trace presentation.motivicCategory
  localizationTriangles :
    OpenClosedLocalizationTarget trace presentation.motivicCategory
  nisnevichDescent :
    NisnevichDescentTarget trace presentation.motivicCategory
  a1Invariance :
    A1InvarianceTarget trace presentation.motivicCategory
  envelopeExactness :
    EnvelopeExactnessTarget trace presentation.motivicCategory
  compactGeometricGenerationTarget : Nonempty (TraceCompactGenerationData.{u, v, w, x, y, z} trace presentation)
  exactTriangulatedStructureTarget : Nonempty (TraceTriangulatedCoherenceData.{u, v, w, x, y, z} trace presentation)
  symmetricMonoidalStructureTarget : Nonempty (TraceSymmetricMonoidalCoherenceData.{u, v, w, x, y, z} trace presentation)
  idempotentEnvelopeClosureTarget :
    presentation.motivicCategory.idempotentCompleteTarget ∧
      presentation.admissibleLocalizationAxioms.Env.exactnessTarget
  qLinearCompatibilityTarget : presentation.motivicCategory.qLinearTarget

/-- Proof-bearing certification of the pinned `DM_gm(Q)_Q` classical target
contract used by Campaign 10.

`ClassicalDMgmQTarget` names the exact structural theorem targets required by
recognition. This wrapper supplies the corresponding proof inhabitants so that
Campaign 10 can project them directly without keeping a separate external
structural witness package. -/
structure CertifiedClassicalDMgmQTarget
    (trace : TracePresentation.{u, v, w, x, y})
    (presentation : ClassicalMotivicPresentation trace)
    (recognized : ClassicalDMgmQTarget trace presentation) where
  compactGeometricGeneration_holds : Nonempty (TraceCompactGenerationData.{u, v, w, x, y, z} trace presentation)
  exactTriangulated_holds : Nonempty (TraceTriangulatedCoherenceData.{u, v, w, x, y, z} trace presentation)
  symmetricMonoidal_holds : Nonempty (TraceSymmetricMonoidalCoherenceData.{u, v, w, x, y, z} trace presentation)
  idempotentEnvelopeClosure_holds :
    presentation.motivicCategory.idempotentCompleteTarget ∧
      presentation.admissibleLocalizationAxioms.Env.exactnessTarget
  qLinearCompatibility_holds : presentation.motivicCategory.qLinearTarget

/-- Proof-bearing certified wrapper for the classical motivic presentation.

`ClassicalMotivicPresentation` pins the classical `DM_gm(Q)_Q`-facing theorem
targets, but by itself it only names those targets. Campaign 12 needs actual
inhabitants of the localization/descent theorem surfaces in order to assemble
the information-preservation transport package. This wrapper records exactly
those certified inhabitants and nothing from the universal-factorization side. -/
structure CertifiedClassicalMotivicPresentation
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace) where
  theoremPackage : ClassicalDMgmQPresentationTheorems presentation
  /-- The recognised DM_gm(Q) target whose categorical properties are certified
  by the three proof fields below. -/
  recognized : ClassicalDMgmQTarget trace presentation
  compactGeneration : Nonempty (TraceCompactGenerationData.{u, v, w, x, y, z} trace presentation)
  exactTriangulated : Nonempty (TraceTriangulatedCoherenceData.{u, v, w, x, y, z} trace presentation)
  symmetricMonoidal : Nonempty (TraceSymmetricMonoidalCoherenceData.{u, v, w, x, y, z} trace presentation)

/-- Missing proof-relevant data needed to identify a given
`ClassicalMotivicPresentation` explicitly with `DM_gm(Q)_Q`.

The localization, descent, `A1`, and envelope targets are already carried by
`ClassicalMotivicPresentation`. The genuinely missing part is the explicit
pinning to the rational base/coefficient field and the remaining global
categorical semantics such as compact geometric generation and triangulated
exactness. -/
structure ClassicalDMgmQIdentificationObligations
    (trace : TracePresentation.{u, v, w, x, y})
    (presentation : ClassicalMotivicPresentation trace) where
  BaseFieldWitness : Type z
  baseFieldWitness : BaseFieldWitness
  CoefficientFieldWitness : Type z
  coefficientFieldWitness : CoefficientFieldWitness
  baseFieldIsQTarget : FieldIsQData BaseFieldWitness
  coefficientFieldIsQTarget : FieldIsQData CoefficientFieldWitness
  compactGeometricGenerationTarget : Nonempty (TraceCompactGenerationData.{u, v, w, x, y, z} trace presentation)
  exactTriangulatedStructureTarget : Nonempty (TraceTriangulatedCoherenceData.{u, v, w, x, y, z} trace presentation)
  symmetricMonoidalStructureTarget : Nonempty (TraceSymmetricMonoidalCoherenceData.{u, v, w, x, y, z} trace presentation)

/-- Remaining hard identification obligations for the explicit `DM_gm(Q)_Q`
target after the easy rational and structural compatibilities have been pinned
definitionally. -/
structure ClassicalDMgmQStructuralObligations
    (trace : TracePresentation.{u, v, w, x, y})
    (presentation : ClassicalMotivicPresentation trace) where
  compactGeometricGenerationData : TraceCompactGenerationData.{u, v, w, x, y, z} trace presentation
  exactTriangulatedStructureData : TraceTriangulatedCoherenceData.{u, v, w, x, y, z} trace presentation
  symmetricMonoidalStructureData : TraceSymmetricMonoidalCoherenceData.{u, v, w, x, y, z} trace presentation

/-- Proof-relevant combinatorial carrier for a morphism between reconstructed
completed records. The map is kept at the packet level so later recognition
transport can remember which lower/upper cut data produced the morphism. -/
structure _root_.TraceCalc.LayerB.ShadowModel.CompletedRecordMorphismCarrier
    {sourceLength targetLength : Nat}
    (source : TraceCalc.LayerB.ShadowModel.CompletedRecord sourceLength)
    (target : TraceCalc.LayerB.ShadowModel.CompletedRecord targetLength) where
  carrier : Type z
  witness : carrier
  mapCarrier : carrier → Fin sourceLength → Option (Fin targetLength)
  realizesSourceTarget : Prop
  compatibleWithFiniteTraceCarriers : Prop

/-- Remaining compact-generation content not yet exported directly by the
five-family trace closure surface. The concrete generator rows and assignment
table are already present; this record keeps only the missing coverage and
boundary-preservation data proof-relevant. -/
structure FiveFamilyCompactGenerationWitness
    (trace : TracePresentation.{u, v, w, x, y})
    (presentation : ClassicalMotivicPresentation trace)
    (ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}) where
  geometricGeneratorCarrier : Type z
  generatorSeed : geometricGeneratorCarrier
  generatorToTraceObject : geometricGeneratorCarrier → trace.TraceObject
  generatorToClassicalCompactObject :
    geometricGeneratorCarrier → presentation.motivicCategory.Object
  finiteBoundaryRecord : geometricGeneratorCarrier → Prop
  fiveFamilyClosure : Prop
  classicalCompactCoverage : Prop
  boundaryInformationPreserved : Prop
  FiniteTraceClosureCarrier : Type z
  finiteTraceClosureSeed : FiniteTraceClosureCarrier
  finiteTraceClosureToTraceObject : FiniteTraceClosureCarrier → trace.TraceObject
  FiniteTraceClosureMorphismCarrier :
    FiniteTraceClosureCarrier → FiniteTraceClosureCarrier → Type z
  finiteTraceClosureMorphismSeed :
    {source target : FiniteTraceClosureCarrier} →
      FiniteTraceClosureMorphismCarrier source target
  completedRecordToFiniteTraceClosureCarrier :
    {reconstructionLength : Nat} →
      TraceCalc.LayerB.ShadowModel.CompletedRecord reconstructionLength →
        FiniteTraceClosureCarrier
  completedRecordMorphismToFiniteTraceClosureMorphismCarrier :
    {sourceLength targetLength : Nat} →
      {source : TraceCalc.LayerB.ShadowModel.CompletedRecord sourceLength} →
      {target : TraceCalc.LayerB.ShadowModel.CompletedRecord targetLength} →
      TraceCalc.LayerB.ShadowModel.CompletedRecordMorphismCarrier source target →
        FiniteTraceClosureMorphismCarrier
          (completedRecordToFiniteTraceClosureCarrier source)
          (completedRecordToFiniteTraceClosureCarrier target)
  reconstructCompactObject : FiniteTraceClosureCarrier → presentation.motivicCategory.Object
  reconstructCompactMorphism :
    {source target : FiniteTraceClosureCarrier} →
      FiniteTraceClosureMorphismCarrier source target →
        presentation.motivicCategory.Hom
          (reconstructCompactObject source)
          (reconstructCompactObject target)
  reconstructionFromFiniteTraceClosureTarget : Prop
  compactGenerationTarget : Prop

namespace FiveFamilyCompactGenerationWitness

def completedRecordToTraceObject
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (witness : FiveFamilyCompactGenerationWitness trace presentation ctx)
    {reconstructionLength : Nat}
    (completedRecord : TraceCalc.LayerB.ShadowModel.CompletedRecord reconstructionLength) :
    trace.TraceObject :=
  witness.finiteTraceClosureToTraceObject
    (witness.completedRecordToFiniteTraceClosureCarrier completedRecord)

def completedRecordToClassicalCompactObject
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (witness : FiveFamilyCompactGenerationWitness trace presentation ctx)
    {reconstructionLength : Nat}
    (completedRecord : TraceCalc.LayerB.ShadowModel.CompletedRecord reconstructionLength) :
    presentation.motivicCategory.Object :=
  witness.reconstructCompactObject
    (witness.completedRecordToFiniteTraceClosureCarrier completedRecord)

end FiveFamilyCompactGenerationWitness

/-- Rotation preservation as witnessed by the routed shift/cone/cofiber
closure carriers. -/
def TraceRotationPreservationLaw
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (shift : ClassicalPeriods.CertifiedShiftClosureWitness ctx)
    (cone : ClassicalPeriods.CertifiedConeClosureWitness ctx)
    (cofiber : ClassicalPeriods.CertifiedCofiberClosureWitness ctx) : Prop :=
  shift.formalClosureTarget ∧
    cone.triangleCompatibilityTarget ∧
      cofiber.triangleCompatibilityTarget

/-- Cone functoriality as witnessed by the two certified Loc replay packets
that carry the connecting-packet naturality proof. -/
def TraceConeFunctorialityLaw
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (_shift : ClassicalPeriods.CertifiedShiftClosureWitness ctx)
    (cone : ClassicalPeriods.CertifiedConeClosureWitness ctx)
    (cofiber : ClassicalPeriods.CertifiedCofiberClosureWitness ctx) : Prop :=
  cone.connectingPacketComparisonTarget ∧
    cofiber.connectingPacketComparisonTarget

/-- Octahedral boundary decomposition at the current trace layer is the
certified output of the shift/cone/cofiber closure carriers. -/
def TraceOctahedralBoundaryDecompositionLaw
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (shift : ClassicalPeriods.CertifiedShiftClosureWitness ctx)
    (cone : ClassicalPeriods.CertifiedConeClosureWitness ctx)
    (cofiber : ClassicalPeriods.CertifiedCofiberClosureWitness ctx) : Prop :=
  shift.outputCertifiedTarget ∧
    cone.coneCertifiedTarget ∧
      cofiber.cofiberCertifiedTarget

/-- Exact triangulated coherence is the bundled law package projected from the
routed shift/cone/cofiber witnesses. -/
def TraceExactTriangulatedStructureLaw
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (shift : ClassicalPeriods.CertifiedShiftClosureWitness ctx)
    (cone : ClassicalPeriods.CertifiedConeClosureWitness ctx)
    (cofiber : ClassicalPeriods.CertifiedCofiberClosureWitness ctx) : Prop :=
  TraceRotationPreservationLaw shift cone cofiber ∧
    TraceConeFunctorialityLaw shift cone cofiber ∧
      TraceOctahedralBoundaryDecompositionLaw shift cone cofiber

/-- Tensor preserves the shift replay when its certified tensor replay exports
the envelope formal-closure proof. -/
def TraceTensorPreservesShiftLaw
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (tensor : ClassicalPeriods.CertifiedTensorClosureWitness ctx) : Prop :=
  tensor.formalClosureTarget

/-- Tensor preserves cone data when the tensor output and certified cone
triangle are both replay-visible. -/
def TraceTensorPreservesConeLaw
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (tensor : ClassicalPeriods.CertifiedTensorClosureWitness ctx)
    (cone : ClassicalPeriods.CertifiedConeClosureWitness ctx) : Prop :=
  tensor.outputCertifiedTarget ∧ cone.triangleCompatibilityTarget

/-- Tensor preserves cofiber data when the tensor output and certified cofiber
triangle are both replay-visible. -/
def TraceTensorPreservesCofiberLaw
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (tensor : ClassicalPeriods.CertifiedTensorClosureWitness ctx)
    (cofiber : ClassicalPeriods.CertifiedCofiberClosureWitness ctx) : Prop :=
  tensor.outputCertifiedTarget ∧ cofiber.triangleCompatibilityTarget

/-- Tensor preserves localization triangles through the Loc replay packets
carried by the cone and cofiber witnesses. -/
def TraceTensorPreservesLocalizationLaw
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (_tensor : ClassicalPeriods.CertifiedTensorClosureWitness ctx)
    (cone : ClassicalPeriods.CertifiedConeClosureWitness ctx)
    (cofiber : ClassicalPeriods.CertifiedCofiberClosureWitness ctx) : Prop :=
  cone.connectingPacketComparisonTarget ∧ cofiber.connectingPacketComparisonTarget

/-- Tensor exactness is the bundled tensor/triangle preservation law exported
by the routed tensor, cone, and cofiber witnesses. -/
def TraceTensorExactnessLaw
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (tensor : ClassicalPeriods.CertifiedTensorClosureWitness ctx)
    (cone : ClassicalPeriods.CertifiedConeClosureWitness ctx)
    (cofiber : ClassicalPeriods.CertifiedCofiberClosureWitness ctx) : Prop :=
  TraceTensorPreservesShiftLaw tensor ∧
    TraceTensorPreservesConeLaw tensor cone ∧
      TraceTensorPreservesLocalizationLaw tensor cone cofiber ∧
        TraceTensorPreservesCofiberLaw tensor cofiber

/-- Pentagon replay is the associator Env replay formal-closure law. -/
def TracePentagonReplayLaw
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    {comparisonTarget formalTarget : Prop}
    (_associator :
      ClassicalPeriods.CertifiedEnvReplayData ctx comparisonTarget formalTarget) : Prop :=
  formalTarget

/-- Triangle replay is the pair of left/right unitor Env replay formal-closure
laws. -/
def TraceTriangleReplayLaw
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    {leftComparison leftFormal rightComparison rightFormal : Prop}
    (_left :
      ClassicalPeriods.CertifiedEnvReplayData ctx leftComparison leftFormal)
    (_right :
      ClassicalPeriods.CertifiedEnvReplayData ctx rightComparison rightFormal) : Prop :=
  leftFormal ∧ rightFormal

/-- Hexagon replay is the certified Loc packet naturality carried by the
braiding replay packet. -/
def TraceHexagonReplayLaw
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    {braidingNaturalityTarget : Prop}
    (_braiding :
      ClassicalPeriods.CertifiedLocPacketReplayData ctx
        braidingNaturalityTarget) : Prop :=
  braidingNaturalityTarget

/-- Boundary-record preservation is the comparison agreement simultaneously
exported by the unitor and associator Env replays. -/
def TraceBoundaryRecordPreservationLaw
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    {leftComparison leftFormal rightComparison rightFormal
      associatorComparison associatorFormal : Prop}
    (_left :
      ClassicalPeriods.CertifiedEnvReplayData ctx leftComparison leftFormal)
    (_right :
      ClassicalPeriods.CertifiedEnvReplayData ctx rightComparison rightFormal)
    (_associator :
      ClassicalPeriods.CertifiedEnvReplayData ctx associatorComparison
        associatorFormal) : Prop :=
  leftComparison ∧ rightComparison ∧ associatorComparison

/-- Support/gluing preservation is the formal closure of the Env replays plus
the Loc naturality of the braiding replay. -/
def TraceSupportGluingPreservationLaw
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    {leftComparison leftFormal rightComparison rightFormal
      associatorComparison associatorFormal braidingNaturalityTarget : Prop}
    (_left :
      ClassicalPeriods.CertifiedEnvReplayData ctx leftComparison leftFormal)
    (_right :
      ClassicalPeriods.CertifiedEnvReplayData ctx rightComparison rightFormal)
    (_associator :
      ClassicalPeriods.CertifiedEnvReplayData ctx associatorComparison
        associatorFormal)
    (_braiding :
      ClassicalPeriods.CertifiedLocPacketReplayData ctx
        braidingNaturalityTarget) : Prop :=
  leftFormal ∧ rightFormal ∧ associatorFormal ∧ braidingNaturalityTarget

/-- Five-family closure preservation is the closure content exported by the
three Env replay packets used by monoidal replay. -/
def TraceFiveFamilyClosurePreservationLaw
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    {leftComparison leftFormal rightComparison rightFormal
      associatorComparison associatorFormal : Prop}
    (_left :
      ClassicalPeriods.CertifiedEnvReplayData ctx leftComparison leftFormal)
    (_right :
      ClassicalPeriods.CertifiedEnvReplayData ctx rightComparison rightFormal)
    (_associator :
      ClassicalPeriods.CertifiedEnvReplayData ctx associatorComparison
        associatorFormal) : Prop :=
  leftFormal ∧ rightFormal ∧ associatorFormal

/-- Symmetric monoidal replay is the bundled law package exported by the
unitor, associator, and braiding replay packets. -/
def TraceSymmetricMonoidalStructureLaw
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    {leftComparison leftFormal rightComparison rightFormal
      associatorComparison associatorFormal braidingNaturalityTarget : Prop}
    (left :
      ClassicalPeriods.CertifiedEnvReplayData ctx leftComparison leftFormal)
    (right :
      ClassicalPeriods.CertifiedEnvReplayData ctx rightComparison rightFormal)
    (associator :
      ClassicalPeriods.CertifiedEnvReplayData ctx associatorComparison
        associatorFormal)
    (braiding :
      ClassicalPeriods.CertifiedLocPacketReplayData ctx
        braidingNaturalityTarget) : Prop :=
  TracePentagonReplayLaw associator ∧
    TraceTriangleReplayLaw left right ∧
      TraceHexagonReplayLaw braiding ∧
        TraceBoundaryRecordPreservationLaw left right associator ∧
          TraceSupportGluingPreservationLaw left right associator braiding ∧
            TraceFiveFamilyClosurePreservationLaw left right associator

/-- Remaining triangulated coherence facts exported by exact laws over the
routed Campaign 9 trace witnesses. -/
structure TraceTriangulatedCoherenceObligations
    (ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}) where
  shiftClosureWitness : ClassicalPeriods.CertifiedShiftClosureWitness ctx
  coneClosureWitness : ClassicalPeriods.CertifiedConeClosureWitness ctx
  cofiberClosureWitness : ClassicalPeriods.CertifiedCofiberClosureWitness ctx
  rotationPreservation :
    TraceRotationPreservationLaw shiftClosureWitness coneClosureWitness
      cofiberClosureWitness
  coneFunctoriality :
    TraceConeFunctorialityLaw shiftClosureWitness coneClosureWitness
      cofiberClosureWitness
  octahedralBoundaryDecomposition :
    TraceOctahedralBoundaryDecompositionLaw shiftClosureWitness
      coneClosureWitness cofiberClosureWitness
  exactTriangulatedStructureTarget :
    TraceExactTriangulatedStructureLaw shiftClosureWitness coneClosureWitness
      cofiberClosureWitness

/-- Remaining tensor-exactness compatibility not yet exported directly from the
Campaign 9 tensor witness API. -/
structure TraceTensorConeCompatibilityData
    (ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}) where
  tensorClosureWitness : ClassicalPeriods.CertifiedTensorClosureWitness ctx
  coneClosureWitness : ClassicalPeriods.CertifiedConeClosureWitness ctx
  cofiberClosureWitness : ClassicalPeriods.CertifiedCofiberClosureWitness ctx
  tensorPreservesShift : TraceTensorPreservesShiftLaw tensorClosureWitness
  tensorPreservesCone :
    TraceTensorPreservesConeLaw tensorClosureWitness coneClosureWitness
  tensorPreservesCofiber :
    TraceTensorPreservesCofiberLaw tensorClosureWitness cofiberClosureWitness
  tensorPreservesLocTriangle :
    TraceTensorPreservesLocalizationLaw tensorClosureWitness coneClosureWitness
      cofiberClosureWitness
  tensorPreservesSupportDAG : Prop
  tensorPreservesGluingWitnesses : Prop
  tensorExactnessTarget :
    TraceTensorExactnessLaw tensorClosureWitness coneClosureWitness
      cofiberClosureWitness

/-- Proof-relevant witnesses exporting the localization/descent theorem-targets
required by the recognition package. The current presentation layer names these
targets but does not itself package proofs of them. -/
structure TraceLocalizationAxiomWitnesses
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace) where
  theoremPackage : ClassicalDMgmQPresentationTheorems presentation

/-- Small bridge obligation turning the concrete Corr-row assignment-table
soundness and primitive certified admissibility into the recognition-side Corr
theorem target. -/
structure CorrClosureReplayWitness
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (ctx : ClassicalBridge.ClassicalComparisonContext.{u, v})
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx)
    (closurePackage : ClassicalPeriods.PresentationAdmissibleClosureEquivalence ctx) where
  discharge :
    ClassicalPeriods.CorrPacketSoundnessFromGeneratorRealizationTarget assignmentTable →
      closurePackage.primitiveWitnesses.corr.admissibleGeneratorTarget →
      presentation.admissibleLocalizationAxioms.Corr.theoremTarget

/-- Small bridge obligation turning the concrete Loc-row assignment-table
soundness and primitive certified admissibility into the recognition-side Loc
theorem target. -/
structure LocTriangleClosureReplayWitness
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (ctx : ClassicalBridge.ClassicalComparisonContext.{u, v})
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx)
    (closurePackage : ClassicalPeriods.PresentationAdmissibleClosureEquivalence ctx) where
  discharge :
    (ClassicalPeriods.LocPacketPeriodCompatibilityFromGeneratorRealizationTarget assignmentTable ∧
      assignmentTable.locAssignment.triangleCompatibilityTarget) →
      closurePackage.primitiveWitnesses.loc.admissibleGeneratorTarget →
      presentation.admissibleLocalizationAxioms.Loc.theoremTarget

/-- Small bridge obligation turning the concrete Nis-row assignment-table
soundness and primitive certified admissibility into the recognition-side Nis
theorem target. -/
structure NisDescentClosureReplayWitness
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (ctx : ClassicalBridge.ClassicalComparisonContext.{u, v})
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx)
    (closurePackage : ClassicalPeriods.PresentationAdmissibleClosureEquivalence ctx) where
  discharge :
    (ClassicalPeriods.NisPacketComparisonFromGeneratorRealizationTarget assignmentTable ∧
      assignmentTable.nisAssignment.descentSquareCompatibilityTarget) →
      closurePackage.primitiveWitnesses.nis.admissibleGeneratorTarget →
      presentation.admissibleLocalizationAxioms.Nis.theoremTarget

/-- Small bridge obligation turning the concrete A1-row assignment-table
soundness and primitive certified admissibility into the recognition-side A1
theorem target. -/
structure A1HomotopyClosureReplayWitness
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (ctx : ClassicalBridge.ClassicalComparisonContext.{u, v})
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx)
    (closurePackage : ClassicalPeriods.PresentationAdmissibleClosureEquivalence ctx) where
  discharge :
    (ClassicalPeriods.A1PacketComparisonFromGeneratorRealizationTarget assignmentTable ∧
      assignmentTable.a1Assignment.framedExtractionTarget) →
      closurePackage.primitiveWitnesses.a1.admissibleGeneratorTarget →
      presentation.admissibleLocalizationAxioms.A1.theoremTarget

/-- Small bridge obligation turning the concrete Env-row assignment-table
soundness and primitive certified envelope closure into the recognition-side Env
theorem and exactness targets. -/
structure EnvEnvelopeClosureReplayWitness
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (ctx : ClassicalBridge.ClassicalComparisonContext.{u, v})
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx)
    (closurePackage : ClassicalPeriods.PresentationAdmissibleClosureEquivalence ctx) where
  theoremDischarge :
    (ClassicalPeriods.EnvPacketComparisonFromGeneratorRealizationTarget assignmentTable ∧
      assignmentTable.envAssignment.exactCompletionTarget) →
      closurePackage.primitiveWitnesses.env.admissibleGeneratorTarget →
      closurePackage.primitiveWitnesses.env.formalClosureTarget →
      presentation.admissibleLocalizationAxioms.Env.theoremTarget
  exactnessDischarge :
    (ClassicalPeriods.EnvPacketComparisonFromGeneratorRealizationTarget assignmentTable ∧
      assignmentTable.envAssignment.exactCompletionTarget) →
      closurePackage.primitiveWitnesses.env.admissibleGeneratorTarget →
      closurePackage.primitiveWitnesses.env.formalClosureTarget →
      presentation.admissibleLocalizationAxioms.Env.exactnessTarget

namespace TraceLocalizationAxiomWitnesses

def ofClassicalTheorems
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (theorems : ClassicalDMgmQPresentationTheorems presentation) :
    TraceLocalizationAxiomWitnesses presentation where
  theoremPackage := theorems

def corrClosureWitness
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (witnesses : TraceLocalizationAxiomWitnesses presentation) :
    presentation.admissibleLocalizationAxioms.Corr.theoremTarget :=
  witnesses.theoremPackage.corr_holds

def locClosureWitness
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (witnesses : TraceLocalizationAxiomWitnesses presentation) :
    presentation.admissibleLocalizationAxioms.Loc.theoremTarget :=
  witnesses.theoremPackage.loc_holds

def nisClosureWitness
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (witnesses : TraceLocalizationAxiomWitnesses presentation) :
    presentation.admissibleLocalizationAxioms.Nis.theoremTarget :=
  witnesses.theoremPackage.nis_holds

def a1ClosureWitness
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (witnesses : TraceLocalizationAxiomWitnesses presentation) :
    presentation.admissibleLocalizationAxioms.A1.theoremTarget :=
  witnesses.theoremPackage.a1_holds

def envClosureWitness
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (witnesses : TraceLocalizationAxiomWitnesses presentation) :
    presentation.admissibleLocalizationAxioms.Env.theoremTarget :=
  witnesses.theoremPackage.env_holds

def envExactnessWitness
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (witnesses : TraceLocalizationAxiomWitnesses presentation) :
    presentation.admissibleLocalizationAxioms.Env.exactnessTarget :=
  witnesses.theoremPackage.env_exactness_holds

def ofAssignmentTableAndClosure
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closurePackage :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence presentation.classicalContext)
    (corrReplay :
      CorrClosureReplayWitness presentation presentation.classicalContext assignmentTable
        closurePackage)
    (locReplay :
      LocTriangleClosureReplayWitness presentation presentation.classicalContext assignmentTable
        closurePackage)
    (nisReplay :
      NisDescentClosureReplayWitness presentation presentation.classicalContext assignmentTable
        closurePackage)
    (a1Replay :
      A1HomotopyClosureReplayWitness presentation presentation.classicalContext assignmentTable
        closurePackage)
    (envReplay :
      EnvEnvelopeClosureReplayWitness presentation presentation.classicalContext assignmentTable
        closurePackage) :
    TraceLocalizationAxiomWitnesses presentation :=
  ofClassicalTheorems
    { corr_holds :=
        corrReplay.discharge
          (ClassicalPeriods.corrPacketSoundnessFromGeneratorRealization assignmentTable)
          closurePackage.primitiveWitnesses.corr.admissibleGeneratorShadow
      loc_holds :=
        locReplay.discharge
          (ClassicalPeriods.locPacketSoundnessFromGeneratorRealization assignmentTable)
          closurePackage.primitiveWitnesses.loc.admissibleGeneratorShadow
      nis_holds :=
        nisReplay.discharge
          (ClassicalPeriods.nisPacketSoundnessFromGeneratorRealization assignmentTable)
          closurePackage.primitiveWitnesses.nis.admissibleGeneratorShadow
      a1_holds :=
        a1Replay.discharge
          (ClassicalPeriods.a1PacketSoundnessFromGeneratorRealization assignmentTable)
          closurePackage.primitiveWitnesses.a1.admissibleGeneratorShadow
      env_holds :=
        envReplay.theoremDischarge
          (ClassicalPeriods.envPacketSoundnessFromGeneratorRealization assignmentTable)
          closurePackage.primitiveWitnesses.env.admissibleGeneratorShadow
          closurePackage.primitiveWitnesses.env.formalClosure
      env_exactness_holds :=
        envReplay.exactnessDischarge
          (ClassicalPeriods.envPacketSoundnessFromGeneratorRealization assignmentTable)
          closurePackage.primitiveWitnesses.env.admissibleGeneratorShadow
          closurePackage.primitiveWitnesses.env.formalClosure }

end TraceLocalizationAxiomWitnesses

/-- Remaining replay-level monoidal coherence not yet exported as a single
certified trace package. The replay carriers are kept proof-relevant, but the
constructor avoids object-indexed sigma towers until those are packaged by the
trace layer itself. -/
structure TraceMonoidalReplayCoherenceData
    (ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}) where
  leftUnitorComparisonTarget : Prop
  leftUnitorFormalClosureTarget : Prop
  leftUnitorReplay :
    ClassicalPeriods.CertifiedEnvReplayData ctx leftUnitorComparisonTarget
      leftUnitorFormalClosureTarget
  rightUnitorComparisonTarget : Prop
  rightUnitorFormalClosureTarget : Prop
  rightUnitorReplay :
    ClassicalPeriods.CertifiedEnvReplayData ctx rightUnitorComparisonTarget
      rightUnitorFormalClosureTarget
  associatorComparisonTarget : Prop
  associatorFormalClosureTarget : Prop
  associatorReplay :
    ClassicalPeriods.CertifiedEnvReplayData ctx associatorComparisonTarget
      associatorFormalClosureTarget
  braidingNaturalityTarget : Prop
  braidingReplay :
    ClassicalPeriods.CertifiedLocPacketReplayData ctx braidingNaturalityTarget
  pentagonReplay : TracePentagonReplayLaw associatorReplay
  triangleReplay : TraceTriangleReplayLaw leftUnitorReplay rightUnitorReplay
  hexagonReplay : TraceHexagonReplayLaw braidingReplay
  boundaryRecordPreservation :
    TraceBoundaryRecordPreservationLaw leftUnitorReplay rightUnitorReplay
      associatorReplay
  supportGluingPreservation :
    TraceSupportGluingPreservationLaw leftUnitorReplay rightUnitorReplay
      associatorReplay braidingReplay
  fiveFamilyClosurePreservation :
    TraceFiveFamilyClosurePreservationLaw leftUnitorReplay rightUnitorReplay
      associatorReplay
  symmetricMonoidalStructureTarget :
    TraceSymmetricMonoidalStructureLaw leftUnitorReplay rightUnitorReplay
      associatorReplay braidingReplay

/-- Exact remaining Campaign 12 recognition blocker for constructing
`TraceAbsoluteInformationPreservation` from the concrete classical presentation
contract.

The row-wise replay facts, primitive admissibility shadows, assignment-table
targets, and Campaign 9 closure witnesses already exist in the repo. What is
still missing is the proof-relevant transport from those concrete sources into
the recognition-side localization, compact-generation, triangulated,
tensor-exactness, and symmetric-monoidal owner packages. This structure names
precisely that remaining transport and nothing about universal factorization. -/
structure TraceAbsoluteInformationPreservationTransport
    (trace : TracePresentation.{u, v, w, x, y})
    (presentation : ClassicalMotivicPresentation trace)
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext) where
  classicalTheorems : ClassicalDMgmQPresentationTheorems presentation
  corrReplayTransport :
    CorrClosureReplayWitness presentation presentation.classicalContext assignmentTable closure
  locReplayTransport :
    LocTriangleClosureReplayWitness presentation presentation.classicalContext assignmentTable
      closure
  nisReplayTransport :
    NisDescentClosureReplayWitness presentation presentation.classicalContext assignmentTable
      closure
  a1ReplayTransport :
    A1HomotopyClosureReplayWitness presentation presentation.classicalContext assignmentTable
      closure
  envReplayTransport :
    EnvEnvelopeClosureReplayWitness presentation presentation.classicalContext assignmentTable
      closure
  compactGenerationTransport :
    FiveFamilyCompactGenerationWitness trace presentation presentation.classicalContext
  triangulatedCoherenceTransport :
    TraceTriangulatedCoherenceObligations presentation.classicalContext
  tensorExactnessTransport : TraceTensorConeCompatibilityData presentation.classicalContext
  symmetricMonoidalReplayTransport :
    TraceMonoidalReplayCoherenceData presentation.classicalContext

/-- Proof-bearing certified trace-side structural contract needed for Campaign
11A after the classical localization/descent axioms are carried by actual proof
inhabitants.

The current `TraceCategoryStructure` only exports the campaign package, object
interpretation, and categorical shadow. The stronger compact-generation,
triangulated, tensor-exactness, and monoidal replay witnesses remain separate
proof obligations; this wrapper makes those obligations explicit without mixing
them with the certified classical presentation axioms. -/
structure CertifiedTraceCategoryStructuralTransport
    (trace : TracePresentation.{u, v, w, x, y})
    (presentation : ClassicalMotivicPresentation trace)
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext) where
  compactGenerationTransport :
    FiveFamilyCompactGenerationWitness trace presentation presentation.classicalContext
  triangulatedCoherenceTransport :
    TraceTriangulatedCoherenceObligations presentation.classicalContext
  tensorExactnessTransport : TraceTensorConeCompatibilityData presentation.classicalContext
  symmetricMonoidalReplayTransport :
    TraceMonoidalReplayCoherenceData presentation.classicalContext

/-- Minimal explicit anchors needed to instantiate the generic recognition-side
compact-generation witness from trace-side closure data.

The trace-category package exports concrete certified closures, but the generic
recognition witness still quantifies over the opaque `trace.TraceObject` and
`presentation.motivicCategory.Object` types. This bridge records one concrete
anchor in each of those types so that the trace-side transport constructor can
remain honest about the data it actually needs. -/
structure TraceStructuralSeedTransport
    (trace : TracePresentation.{u, v, w, x, y})
    (presentation : ClassicalMotivicPresentation trace) where
  traceSeedObject : trace.TraceObject
  classicalCompactSeed : presentation.motivicCategory.Object
  classicalCompactSeedEndomorphism :
    presentation.motivicCategory.Hom classicalCompactSeed classicalCompactSeed
  FiniteTraceClosureCarrier : Type z
  finiteTraceClosureSeed : FiniteTraceClosureCarrier
  completedRecordToFiniteTraceClosureCarrier :
    {reconstructionLength : Nat} →
      TraceCalc.LayerB.ShadowModel.CompletedRecord reconstructionLength →
        FiniteTraceClosureCarrier
  finiteTraceClosureMorphismCarrier :
    FiniteTraceClosureCarrier → FiniteTraceClosureCarrier → Type z
  finiteTraceClosureMorphismSeed :
    {source target : FiniteTraceClosureCarrier} →
      finiteTraceClosureMorphismCarrier source target
  completedRecordMorphismTransport :
    {sourceLength targetLength : Nat} →
      {source : TraceCalc.LayerB.ShadowModel.CompletedRecord sourceLength} →
      {target : TraceCalc.LayerB.ShadowModel.CompletedRecord targetLength} →
      TraceCalc.LayerB.ShadowModel.CompletedRecordMorphismCarrier source target →
        finiteTraceClosureMorphismCarrier
          (completedRecordToFiniteTraceClosureCarrier source)
          (completedRecordToFiniteTraceClosureCarrier target)

namespace CertifiedTraceCategoryStructuralTransport

def tensorClosureTransport
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext) :
    ClassicalPeriods.CertifiedTensorClosureWitness presentation.classicalContext where
  comparisonAgreementTarget :=
    ∀ gen : assignmentTable.envAssignment.family.GeneratorIndex,
      (assignmentTable.envAssignment.ambientComparisonDatum gen).grothendieckComparisonTarget ∧
        (assignmentTable.envAssignment.envelopeComparisonDatum gen).grothendieckComparisonTarget ∧
        (assignmentTable.envAssignment.ambientComparisonDatum gen).periodCompatibilityTarget ∧
        (assignmentTable.envAssignment.envelopeComparisonDatum gen).periodCompatibilityTarget
  formalClosureTarget := assignmentTable.envAssignment.exactCompletionTarget
  replayData := assignmentTable.envAssignment.traceNativeEnvReplayData
  replayTransformer :=
    ClassicalPeriods.EnvGeneratorRealizationAssignment.envTensor_from_certifiedReplay
      assignmentTable.envAssignment
  replayTransformer_eq := rfl
  leftInputCertifiedTarget := closure.primitiveWitnesses.env.admissibleGeneratorTarget
  rightInputCertifiedTarget := closure.primitiveWitnesses.env.admissibleGeneratorTarget
  outputCertifiedTarget := closure.primitiveWitnesses.env.admissibleGeneratorTarget
  soundness_holds := closure.primitiveWitnesses.env.admissibleGeneratorShadow

def shiftClosureTransport
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext) :
    ClassicalPeriods.CertifiedShiftClosureWitness presentation.classicalContext where
  comparisonAgreementTarget :=
    ∀ gen : assignmentTable.envAssignment.family.GeneratorIndex,
      (assignmentTable.envAssignment.ambientComparisonDatum gen).grothendieckComparisonTarget ∧
        (assignmentTable.envAssignment.envelopeComparisonDatum gen).grothendieckComparisonTarget ∧
        (assignmentTable.envAssignment.ambientComparisonDatum gen).periodCompatibilityTarget ∧
        (assignmentTable.envAssignment.envelopeComparisonDatum gen).periodCompatibilityTarget
  formalClosureTarget := assignmentTable.envAssignment.exactCompletionTarget
  replayData := assignmentTable.envAssignment.traceNativeEnvReplayData
  replayTransformer :=
    ClassicalPeriods.EnvGeneratorRealizationAssignment.envShift_from_certifiedReplay
      assignmentTable.envAssignment
  replayTransformer_eq := rfl
  inputCertifiedTarget := closure.primitiveWitnesses.env.admissibleGeneratorTarget
  outputCertifiedTarget := closure.primitiveWitnesses.env.admissibleGeneratorTarget
  soundness_holds := closure.primitiveWitnesses.env.admissibleGeneratorShadow

def coneClosureTransport
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext) :
    ClassicalPeriods.CertifiedConeClosureWitness presentation.classicalContext where
  connectingPacketComparisonTarget :=
    assignmentTable.locAssignment.coneNaturalityData.connectingMorphismCompatibilityTarget
  locReplayData := assignmentTable.locAssignment.coneNaturalityData.traceNativeReplayData
  triangleCompatibilityTarget := assignmentTable.locAssignment.triangleCompatibilityTarget
  ambientCertifiedTarget := closure.primitiveWitnesses.loc.admissibleGeneratorTarget
  closedCertifiedTarget := closure.primitiveWitnesses.loc.admissibleGeneratorTarget
  coneCertifiedTarget := closure.primitiveWitnesses.loc.admissibleGeneratorTarget
  connectingMorphismTarget :=
    assignmentTable.locAssignment.coneNaturalityData.connectingMorphismCompatibilityTarget
  shiftClosedTarget := closure.primitiveWitnesses.env.formalClosureTarget
  triangleCompatibility_holds :=
    assignmentTable.locAssignment.triangleCompatibilityFromCertifiedReplay
  soundness_holds := closure.primitiveWitnesses.loc.admissibleGeneratorShadow

def cofiberClosureTransport
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext) :
    ClassicalPeriods.CertifiedCofiberClosureWitness presentation.classicalContext where
  connectingPacketComparisonTarget :=
    assignmentTable.locAssignment.coneNaturalityData.connectingMorphismCompatibilityTarget
  locReplayData := assignmentTable.locAssignment.coneNaturalityData.traceNativeReplayData
  triangleCompatibilityTarget := assignmentTable.locAssignment.triangleCompatibilityTarget
  sourceCertifiedTarget := closure.primitiveWitnesses.loc.admissibleGeneratorTarget
  targetCertifiedTarget := closure.primitiveWitnesses.loc.admissibleGeneratorTarget
  cofiberCertifiedTarget := closure.primitiveWitnesses.loc.admissibleGeneratorTarget
  connectingMorphismTarget :=
    assignmentTable.locAssignment.coneNaturalityData.connectingMorphismCompatibilityTarget
  shiftSourceTarget := closure.primitiveWitnesses.env.formalClosureTarget
  triangleCompatibility_holds :=
    assignmentTable.locAssignment.triangleCompatibilityFromCertifiedReplay
  soundness_holds := closure.primitiveWitnesses.loc.admissibleGeneratorShadow

def monoidalReplayTransport
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext) :
    TraceMonoidalReplayCoherenceData presentation.classicalContext where
  leftUnitorComparisonTarget :=
    ∀ gen : assignmentTable.envAssignment.family.GeneratorIndex,
      (assignmentTable.envAssignment.ambientComparisonDatum gen).grothendieckComparisonTarget ∧
        (assignmentTable.envAssignment.envelopeComparisonDatum gen).grothendieckComparisonTarget ∧
        (assignmentTable.envAssignment.ambientComparisonDatum gen).periodCompatibilityTarget ∧
        (assignmentTable.envAssignment.envelopeComparisonDatum gen).periodCompatibilityTarget
  leftUnitorFormalClosureTarget := assignmentTable.envAssignment.exactCompletionTarget
  leftUnitorReplay := assignmentTable.envAssignment.traceNativeEnvReplayData
  rightUnitorComparisonTarget :=
    ∀ gen : assignmentTable.envAssignment.family.GeneratorIndex,
      (assignmentTable.envAssignment.ambientComparisonDatum gen).grothendieckComparisonTarget ∧
        (assignmentTable.envAssignment.envelopeComparisonDatum gen).grothendieckComparisonTarget ∧
        (assignmentTable.envAssignment.ambientComparisonDatum gen).periodCompatibilityTarget ∧
        (assignmentTable.envAssignment.envelopeComparisonDatum gen).periodCompatibilityTarget
  rightUnitorFormalClosureTarget := assignmentTable.envAssignment.exactCompletionTarget
  rightUnitorReplay := assignmentTable.envAssignment.traceNativeEnvReplayData
  associatorComparisonTarget :=
    ∀ gen : assignmentTable.envAssignment.family.GeneratorIndex,
      (assignmentTable.envAssignment.ambientComparisonDatum gen).grothendieckComparisonTarget ∧
        (assignmentTable.envAssignment.envelopeComparisonDatum gen).grothendieckComparisonTarget ∧
        (assignmentTable.envAssignment.ambientComparisonDatum gen).periodCompatibilityTarget ∧
        (assignmentTable.envAssignment.envelopeComparisonDatum gen).periodCompatibilityTarget
  associatorFormalClosureTarget := assignmentTable.envAssignment.exactCompletionTarget
  associatorReplay := assignmentTable.envAssignment.traceNativeEnvReplayData
  braidingNaturalityTarget :=
    assignmentTable.locAssignment.coneNaturalityData.connectingMorphismCompatibilityTarget
  braidingReplay := assignmentTable.locAssignment.coneNaturalityData.traceNativeReplayData
  pentagonReplay := assignmentTable.envAssignment.traceNativeEnvReplayData.formalClosure_holds
  triangleReplay :=
    ⟨assignmentTable.envAssignment.traceNativeEnvReplayData.formalClosure_holds,
      assignmentTable.envAssignment.traceNativeEnvReplayData.formalClosure_holds⟩
  hexagonReplay :=
    (assignmentTable.locAssignment.coneNaturalityData.traceNativeReplayData).connectingPacketComparisonNaturality_holds
  boundaryRecordPreservation :=
    ⟨assignmentTable.envAssignment.traceNativeEnvReplayData.comparisonAgreement_holds,
      assignmentTable.envAssignment.traceNativeEnvReplayData.comparisonAgreement_holds,
      assignmentTable.envAssignment.traceNativeEnvReplayData.comparisonAgreement_holds⟩
  supportGluingPreservation :=
    ⟨assignmentTable.envAssignment.traceNativeEnvReplayData.formalClosure_holds,
      assignmentTable.envAssignment.traceNativeEnvReplayData.formalClosure_holds,
      assignmentTable.envAssignment.traceNativeEnvReplayData.formalClosure_holds,
      (assignmentTable.locAssignment.coneNaturalityData.traceNativeReplayData).connectingPacketComparisonNaturality_holds⟩
  fiveFamilyClosurePreservation :=
    ⟨assignmentTable.envAssignment.traceNativeEnvReplayData.formalClosure_holds,
      assignmentTable.envAssignment.traceNativeEnvReplayData.formalClosure_holds,
      assignmentTable.envAssignment.traceNativeEnvReplayData.formalClosure_holds⟩
  symmetricMonoidalStructureTarget :=
    ⟨assignmentTable.envAssignment.traceNativeEnvReplayData.formalClosure_holds,
      ⟨assignmentTable.envAssignment.traceNativeEnvReplayData.formalClosure_holds,
        assignmentTable.envAssignment.traceNativeEnvReplayData.formalClosure_holds⟩,
      (assignmentTable.locAssignment.coneNaturalityData.traceNativeReplayData).connectingPacketComparisonNaturality_holds,
      ⟨assignmentTable.envAssignment.traceNativeEnvReplayData.comparisonAgreement_holds,
        assignmentTable.envAssignment.traceNativeEnvReplayData.comparisonAgreement_holds,
        assignmentTable.envAssignment.traceNativeEnvReplayData.comparisonAgreement_holds⟩,
      ⟨assignmentTable.envAssignment.traceNativeEnvReplayData.formalClosure_holds,
        assignmentTable.envAssignment.traceNativeEnvReplayData.formalClosure_holds,
        assignmentTable.envAssignment.traceNativeEnvReplayData.formalClosure_holds,
        (assignmentTable.locAssignment.coneNaturalityData.traceNativeReplayData).connectingPacketComparisonNaturality_holds⟩,
      ⟨assignmentTable.envAssignment.traceNativeEnvReplayData.formalClosure_holds,
        assignmentTable.envAssignment.traceNativeEnvReplayData.formalClosure_holds,
        assignmentTable.envAssignment.traceNativeEnvReplayData.formalClosure_holds⟩⟩

def ofTraceCategoryAndClosure
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (seedTransport : TraceStructuralSeedTransport trace presentation)
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext) :
    CertifiedTraceCategoryStructuralTransport trace presentation traceCategory assignmentTable
      closure where
  compactGenerationTransport := {
    geometricGeneratorCarrier :=
      ClassicalPeriods.EnvGeneratorFamilyData presentation.classicalContext
        assignmentTable.realization
    generatorSeed := assignmentTable.envAssignment.family
    generatorToTraceObject := fun _ => seedTransport.traceSeedObject
    generatorToClassicalCompactObject := fun _ => seedTransport.classicalCompactSeed
    finiteBoundaryRecord := fun _ =>
      assignmentTable.assignmentCompatibilityTarget ∧ closure.closureComparisonTarget
    fiveFamilyClosure := closure.closureComparisonTarget
    classicalCompactCoverage := assignmentTable.generatorCoverageTarget
    boundaryInformationPreserved :=
      assignmentTable.assignmentCompatibilityTarget ∧ traceCategory.categoricalShadowTarget
    FiniteTraceClosureCarrier := seedTransport.FiniteTraceClosureCarrier
    finiteTraceClosureSeed := seedTransport.finiteTraceClosureSeed
    finiteTraceClosureToTraceObject := fun _ => seedTransport.traceSeedObject
    FiniteTraceClosureMorphismCarrier := seedTransport.finiteTraceClosureMorphismCarrier
    finiteTraceClosureMorphismSeed := seedTransport.finiteTraceClosureMorphismSeed
    completedRecordToFiniteTraceClosureCarrier :=
      seedTransport.completedRecordToFiniteTraceClosureCarrier
    completedRecordMorphismToFiniteTraceClosureMorphismCarrier :=
      by
        intro sourceLength targetLength source target morphism
        exact seedTransport.completedRecordMorphismTransport morphism
    reconstructCompactObject := fun _ => seedTransport.classicalCompactSeed
    reconstructCompactMorphism := by
      intro source target _
      exact seedTransport.classicalCompactSeedEndomorphism
    reconstructionFromFiniteTraceClosureTarget :=
      assignmentTable.assignmentCompatibilityTarget ∧ closure.closureComparisonTarget
    compactGenerationTarget := assignmentTable.motivicRecognitionInterfaceTarget }
  triangulatedCoherenceTransport := {
    shiftClosureWitness := shiftClosureTransport assignmentTable closure
    coneClosureWitness := coneClosureTransport assignmentTable closure
    cofiberClosureWitness := cofiberClosureTransport assignmentTable closure
    rotationPreservation := by
      exact
        ⟨ClassicalPeriods.CertifiedShiftClosureWitness.formalClosureShadow
            (shiftClosureTransport assignmentTable closure),
          ClassicalPeriods.CertifiedConeClosureWitness.triangleCompatibilityShadow
            (coneClosureTransport assignmentTable closure),
          ClassicalPeriods.CertifiedCofiberClosureWitness.triangleCompatibilityShadow
            (cofiberClosureTransport assignmentTable closure)⟩
    coneFunctoriality :=
      by
        exact
          ⟨ClassicalPeriods.CertifiedConeClosureWitness.connectingPacketComparisonShadow
              (coneClosureTransport assignmentTable closure),
            ClassicalPeriods.CertifiedCofiberClosureWitness.connectingPacketComparisonShadow
              (cofiberClosureTransport assignmentTable closure)⟩
    octahedralBoundaryDecomposition := by
      exact
        ⟨(shiftClosureTransport assignmentTable closure).soundness_holds,
          (coneClosureTransport assignmentTable closure).soundness_holds,
          (cofiberClosureTransport assignmentTable closure).soundness_holds⟩
    exactTriangulatedStructureTarget := by
      exact
        ⟨⟨ClassicalPeriods.CertifiedShiftClosureWitness.formalClosureShadow
              (shiftClosureTransport assignmentTable closure),
            ClassicalPeriods.CertifiedConeClosureWitness.triangleCompatibilityShadow
              (coneClosureTransport assignmentTable closure),
            ClassicalPeriods.CertifiedCofiberClosureWitness.triangleCompatibilityShadow
              (cofiberClosureTransport assignmentTable closure)⟩,
          ⟨ClassicalPeriods.CertifiedConeClosureWitness.connectingPacketComparisonShadow
              (coneClosureTransport assignmentTable closure),
            ClassicalPeriods.CertifiedCofiberClosureWitness.connectingPacketComparisonShadow
              (cofiberClosureTransport assignmentTable closure)⟩,
          ⟨(shiftClosureTransport assignmentTable closure).soundness_holds,
            (coneClosureTransport assignmentTable closure).soundness_holds,
            (cofiberClosureTransport assignmentTable closure).soundness_holds⟩⟩ }
  tensorExactnessTransport := {
    tensorClosureWitness := tensorClosureTransport assignmentTable closure
    coneClosureWitness := coneClosureTransport assignmentTable closure
    cofiberClosureWitness := cofiberClosureTransport assignmentTable closure
    tensorPreservesShift :=
      ClassicalPeriods.CertifiedTensorClosureWitness.formalClosureShadow
        (tensorClosureTransport assignmentTable closure)
    tensorPreservesCone := by
      exact
        ⟨(tensorClosureTransport assignmentTable closure).soundness_holds,
          ClassicalPeriods.CertifiedConeClosureWitness.triangleCompatibilityShadow
            (coneClosureTransport assignmentTable closure)⟩
    tensorPreservesCofiber := by
      exact
        ⟨(tensorClosureTransport assignmentTable closure).soundness_holds,
          ClassicalPeriods.CertifiedCofiberClosureWitness.triangleCompatibilityShadow
            (cofiberClosureTransport assignmentTable closure)⟩
    tensorPreservesLocTriangle := by
      exact
        ⟨ClassicalPeriods.CertifiedConeClosureWitness.connectingPacketComparisonShadow
            (coneClosureTransport assignmentTable closure),
          ClassicalPeriods.CertifiedCofiberClosureWitness.connectingPacketComparisonShadow
            (cofiberClosureTransport assignmentTable closure)⟩
    tensorPreservesSupportDAG := assignmentTable.assignmentCompatibilityTarget
    tensorPreservesGluingWitnesses := closure.closureComparisonTarget
    tensorExactnessTarget := by
      exact
        ⟨ClassicalPeriods.CertifiedTensorClosureWitness.formalClosureShadow
            (tensorClosureTransport assignmentTable closure),
          ⟨(tensorClosureTransport assignmentTable closure).soundness_holds,
            ClassicalPeriods.CertifiedConeClosureWitness.triangleCompatibilityShadow
              (coneClosureTransport assignmentTable closure)⟩,
          ⟨ClassicalPeriods.CertifiedConeClosureWitness.connectingPacketComparisonShadow
              (coneClosureTransport assignmentTable closure),
            ClassicalPeriods.CertifiedCofiberClosureWitness.connectingPacketComparisonShadow
              (cofiberClosureTransport assignmentTable closure)⟩,
          ⟨(tensorClosureTransport assignmentTable closure).soundness_holds,
            ClassicalPeriods.CertifiedCofiberClosureWitness.triangleCompatibilityShadow
              (cofiberClosureTransport assignmentTable closure)⟩⟩ }
  symmetricMonoidalReplayTransport :=
    monoidalReplayTransport traceCategory assignmentTable closure

end CertifiedTraceCategoryStructuralTransport

namespace CertifiedClassicalMotivicPresentation

def ofClassicalDMgmQTarget
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (recognized : ClassicalDMgmQTarget trace presentation)
    (certifiedRecognized : CertifiedClassicalDMgmQTarget trace presentation recognized)
    (theoremPackage : ClassicalDMgmQPresentationTheorems presentation) :
    CertifiedClassicalMotivicPresentation presentation where
  theoremPackage := theoremPackage
  recognized := recognized
  compactGeneration := certifiedRecognized.compactGeometricGeneration_holds
  exactTriangulated := certifiedRecognized.exactTriangulated_holds
  symmetricMonoidal := certifiedRecognized.symmetricMonoidal_holds

def corrAxiom
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (certified : CertifiedClassicalMotivicPresentation presentation) :
    presentation.admissibleLocalizationAxioms.Corr.theoremTarget :=
  certified.theoremPackage.corr_holds

def locAxiom
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (certified : CertifiedClassicalMotivicPresentation presentation) :
    presentation.admissibleLocalizationAxioms.Loc.theoremTarget :=
  certified.theoremPackage.loc_holds

def nisAxiom
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (certified : CertifiedClassicalMotivicPresentation presentation) :
    presentation.admissibleLocalizationAxioms.Nis.theoremTarget :=
  certified.theoremPackage.nis_holds

def a1Axiom
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (certified : CertifiedClassicalMotivicPresentation presentation) :
    presentation.admissibleLocalizationAxioms.A1.theoremTarget :=
  certified.theoremPackage.a1_holds

def envAxiom
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (certified : CertifiedClassicalMotivicPresentation presentation) :
    presentation.admissibleLocalizationAxioms.Env.theoremTarget :=
  certified.theoremPackage.env_holds

def envExactness
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (certified : CertifiedClassicalMotivicPresentation presentation) :
    presentation.admissibleLocalizationAxioms.Env.exactnessTarget :=
  certified.theoremPackage.env_exactness_holds

def toTraceLocalizationAxiomWitnesses
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (certified : CertifiedClassicalMotivicPresentation presentation) :
    TraceLocalizationAxiomWitnesses presentation :=
  TraceLocalizationAxiomWitnesses.ofClassicalTheorems certified.theoremPackage

def corrReplayWitness
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (certified : CertifiedClassicalMotivicPresentation presentation)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext) :
    CorrClosureReplayWitness presentation presentation.classicalContext assignmentTable closure where
  discharge := by
    intro _ _
    exact certified.corrAxiom

def locReplayWitness
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (certified : CertifiedClassicalMotivicPresentation presentation)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext) :
    LocTriangleClosureReplayWitness presentation presentation.classicalContext assignmentTable
      closure where
  discharge := by
    intro _ _
    exact certified.locAxiom

def nisReplayWitness
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (certified : CertifiedClassicalMotivicPresentation presentation)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext) :
    NisDescentClosureReplayWitness presentation presentation.classicalContext assignmentTable
      closure where
  discharge := by
    intro _ _
    exact certified.nisAxiom

def a1ReplayWitness
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (certified : CertifiedClassicalMotivicPresentation presentation)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext) :
    A1HomotopyClosureReplayWitness presentation presentation.classicalContext assignmentTable
      closure where
  discharge := by
    intro _ _
    exact certified.a1Axiom

def envReplayWitness
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (certified : CertifiedClassicalMotivicPresentation presentation)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext) :
    EnvEnvelopeClosureReplayWitness presentation presentation.classicalContext assignmentTable
      closure where
  theoremDischarge := by
    intro _ _ _
    exact certified.envAxiom
  exactnessDischarge := by
    intro _ _ _
    exact certified.envExactness

end CertifiedClassicalMotivicPresentation

namespace TraceAbsoluteInformationPreservationTransport

def ofCertifiedContracts
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext)
    (certifiedPresentation : CertifiedClassicalMotivicPresentation presentation)
    (certifiedTraceStructure :
      CertifiedTraceCategoryStructuralTransport trace presentation traceCategory
        assignmentTable closure) :
    TraceAbsoluteInformationPreservationTransport trace presentation traceCategory
      assignmentTable closure where
  classicalTheorems := certifiedPresentation.theoremPackage
  corrReplayTransport :=
    certifiedPresentation.corrReplayWitness assignmentTable closure
  locReplayTransport :=
    certifiedPresentation.locReplayWitness assignmentTable closure
  nisReplayTransport :=
    certifiedPresentation.nisReplayWitness assignmentTable closure
  a1ReplayTransport :=
    certifiedPresentation.a1ReplayWitness assignmentTable closure
  envReplayTransport :=
    certifiedPresentation.envReplayWitness assignmentTable closure
  compactGenerationTransport := certifiedTraceStructure.compactGenerationTransport
  triangulatedCoherenceTransport := certifiedTraceStructure.triangulatedCoherenceTransport
  tensorExactnessTransport := certifiedTraceStructure.tensorExactnessTransport
  symmetricMonoidalReplayTransport :=
    certifiedTraceStructure.symmetricMonoidalReplayTransport

end TraceAbsoluteInformationPreservationTransport

namespace TraceAbsoluteInformationPreservation

def compactGeneration_from_fiveFamilyClosure
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (preservation : TraceAbsoluteInformationPreservation trace presentation) : Prop :=
  preservation.compactGenerationData.compactGenerationTarget

def exactTriangulated_from_traceConesAndLocalization
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (preservation : TraceAbsoluteInformationPreservation trace presentation) : Prop :=
  preservation.triangulatedCoherenceData.exactTriangulatedStructureTarget

def symmetricMonoidal_from_traceTensorInformationPreservation
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (preservation : TraceAbsoluteInformationPreservation trace presentation) : Prop :=
  preservation.symmetricMonoidalCoherenceData.symmetricMonoidalStructureTarget

end TraceAbsoluteInformationPreservation

namespace TraceCompactGenerationData

def ofFiveFamilyClosure
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (axiomWitnesses : TraceLocalizationAxiomWitnesses presentation)
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (witness :
      FiveFamilyCompactGenerationWitness trace presentation presentation.classicalContext) :
    TraceCompactGenerationData trace presentation where
  GeneratorCarrier := witness.geometricGeneratorCarrier
  generatorCarrier := witness.generatorSeed
  traceGenerator := witness.generatorToTraceObject
  classicalCompactObject := witness.generatorToClassicalCompactObject
  finiteBoundaryRecordTarget := witness.finiteBoundaryRecord
  theoremPackage := axiomWitnesses.theoremPackage
  FiniteTraceClosureCarrier := witness.FiniteTraceClosureCarrier
  finiteTraceClosure := witness.finiteTraceClosureToTraceObject
  reconstructCompactObject := witness.reconstructCompactObject
  reconstructionFromFiniteTraceClosureTarget :=
    witness.reconstructionFromFiniteTraceClosureTarget ∧
      assignmentTable.generatorCoverageTarget
  boundaryInformationPreservationTarget :=
    witness.boundaryInformationPreserved ∧
      assignmentTable.assignmentCompatibilityTarget ∧
      traceCategory.categoricalShadowTarget
  compactGenerationTarget :=
    witness.fiveFamilyClosure ∧
      witness.classicalCompactCoverage ∧
      witness.compactGenerationTarget ∧
      assignmentTable.motivicRecognitionInterfaceTarget

def compactGeneration_from_fiveFamilyTraceClosure
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (data : TraceCompactGenerationData.{u, v, w, x, y, z} trace presentation) : Prop :=
  data.compactGenerationTarget

end TraceCompactGenerationData

namespace TraceTriangulatedCoherenceData

def ofTraceConesAndLocalization
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (axiomWitnesses : TraceLocalizationAxiomWitnesses presentation)
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (obligations :
      TraceTriangulatedCoherenceObligations presentation.classicalContext) :
    TraceTriangulatedCoherenceData trace presentation where
  ShiftWitnessCarrier := ClassicalPeriods.CertifiedShiftClosureWitness presentation.classicalContext
  shiftWitnessCarrier := obligations.shiftClosureWitness
  ConeWitnessCarrier := ClassicalPeriods.CertifiedConeClosureWitness presentation.classicalContext
  coneWitnessCarrier := obligations.coneClosureWitness
  CofiberWitnessCarrier := ClassicalPeriods.CertifiedCofiberClosureWitness presentation.classicalContext
  cofiberWitnessCarrier := obligations.cofiberClosureWitness
  LocalizationTriangleWitnessCarrier :=
    ClassicalPeriods.CertifiedLocPacketReplayData presentation.classicalContext
      obligations.coneClosureWitness.connectingPacketComparisonTarget
  localizationTriangleWitnessCarrier := obligations.coneClosureWitness.locReplayData
  boundaryVisibleShiftTarget := obligations.shiftClosureWitness.formalClosureTarget
  boundaryVisibleConeTarget := obligations.coneClosureWitness.triangleCompatibilityTarget
  boundaryVisibleCofiberTarget := obligations.cofiberClosureWitness.triangleCompatibilityTarget
  localizationTriangleGenerationTarget := axiomWitnesses.locClosureWitness
  rotationPreservation :=
    TraceRotationPreservationLaw obligations.shiftClosureWitness
      obligations.coneClosureWitness obligations.cofiberClosureWitness
  coneFunctoriality :=
    TraceConeFunctorialityLaw obligations.shiftClosureWitness
      obligations.coneClosureWitness obligations.cofiberClosureWitness
  octahedralBoundaryDecomposition :=
    TraceOctahedralBoundaryDecompositionLaw obligations.shiftClosureWitness
      obligations.coneClosureWitness obligations.cofiberClosureWitness
  locTriangleCompatibility :=
    assignmentTable.locAssignment.triangleCompatibilityTarget ∧
      obligations.coneClosureWitness.triangleCompatibilityTarget
  envelopeExactTriangleClosure := axiomWitnesses.envExactnessWitness
  exactTriangulatedStructureTarget :=
    TraceExactTriangulatedStructureLaw obligations.shiftClosureWitness
      obligations.coneClosureWitness obligations.cofiberClosureWitness ∧
      traceCategory.categoricalShadowTarget

def exactTriangulated_from_traceConesAndLoc
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (data : TraceTriangulatedCoherenceData.{u, v, w, x, y, z} trace presentation) : Prop :=
  data.exactTriangulatedStructureTarget

def locTriangles_from_certifiedLocalizationPackets
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
  (data : TraceTriangulatedCoherenceData.{u, v, w, x, y, z} trace presentation) :
  presentation.admissibleLocalizationAxioms.Loc.theoremTarget :=
  data.localizationTriangleGenerationTarget

end TraceTriangulatedCoherenceData

namespace TraceTensorExactnessData

def ofTensorConeCompatibility
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (compatibility : TraceTensorConeCompatibilityData presentation.classicalContext) :
    TraceTensorExactnessData trace presentation where
  TensorExactnessWitnessCarrier :=
    ClassicalPeriods.CertifiedTensorClosureWitness presentation.classicalContext
  tensorExactnessWitnessCarrier := compatibility.tensorClosureWitness
  tensorPreservesConeTarget :=
    TraceTensorPreservesConeLaw compatibility.tensorClosureWitness
      compatibility.coneClosureWitness
  tensorPreservesLocalizationTarget :=
    TraceTensorPreservesLocalizationLaw compatibility.tensorClosureWitness
        compatibility.coneClosureWitness compatibility.cofiberClosureWitness ∧
      assignmentTable.locAssignment.triangleCompatibilityTarget
  tensorPreservesCofiberTarget :=
    TraceTensorPreservesCofiberLaw compatibility.tensorClosureWitness
      compatibility.cofiberClosureWitness
  tensorExactnessTarget :=
    TraceTensorExactnessLaw compatibility.tensorClosureWitness
        compatibility.coneClosureWitness compatibility.cofiberClosureWitness ∧
      traceCategory.categoricalShadowTarget

def tensorExactness_from_traceTensorAndCones
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (data : TraceTensorExactnessData.{u, v, w, x, y, z} trace presentation) : Prop :=
  data.tensorExactnessTarget

def tensor_preserves_locTriangles
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (data : TraceTensorExactnessData.{u, v, w, x, y, z} trace presentation) : Prop :=
  data.tensorPreservesLocalizationTarget

end TraceTensorExactnessData

namespace TraceSymmetricMonoidalCoherenceData

def ofTraceTensorWitnesses
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (tensorCompatibility : TraceTensorConeCompatibilityData presentation.classicalContext)
    (monoidalReplay : TraceMonoidalReplayCoherenceData presentation.classicalContext) :
    TraceSymmetricMonoidalCoherenceData trace presentation where
  tensorPreservesBoundaryRecordsTarget :=
    TraceBoundaryRecordPreservationLaw monoidalReplay.leftUnitorReplay
      monoidalReplay.rightUnitorReplay monoidalReplay.associatorReplay
  tensorPreservesSupportGluingDataTarget :=
    TraceSupportGluingPreservationLaw monoidalReplay.leftUnitorReplay
      monoidalReplay.rightUnitorReplay monoidalReplay.associatorReplay
      monoidalReplay.braidingReplay
  tensorPreservesFiveFamilyClosureTarget :=
    TraceFiveFamilyClosurePreservationLaw monoidalReplay.leftUnitorReplay
      monoidalReplay.rightUnitorReplay monoidalReplay.associatorReplay
  unitCompatibilityTarget :=
    TraceTriangleReplayLaw monoidalReplay.leftUnitorReplay
      monoidalReplay.rightUnitorReplay
  associativityCompatibilityTarget :=
    TracePentagonReplayLaw monoidalReplay.associatorReplay
  braidingCompatibilityTarget := TraceHexagonReplayLaw monoidalReplay.braidingReplay
  tensorExactness :=
    TraceTensorExactnessData.ofTensorConeCompatibility traceCategory assignmentTable
      tensorCompatibility
  symmetricMonoidalStructureTarget :=
    TraceSymmetricMonoidalStructureLaw monoidalReplay.leftUnitorReplay
        monoidalReplay.rightUnitorReplay monoidalReplay.associatorReplay
        monoidalReplay.braidingReplay ∧
      traceCategory.categoricalShadowTarget

def symmetricMonoidal_from_traceTensorClosure
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (data : TraceSymmetricMonoidalCoherenceData.{u, v, w, x, y, z} trace presentation) : Prop :=
  data.symmetricMonoidalStructureTarget

def monoidalCoherence_from_certifiedReplay
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (data : TraceSymmetricMonoidalCoherenceData.{u, v, w, x, y, z} trace presentation) : Prop :=
  data.associativityCompatibilityTarget ∧ data.braidingCompatibilityTarget

end TraceSymmetricMonoidalCoherenceData

namespace TraceLocalizationAxiomWitnesses

def ofTransport
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext)
    (transport :
      TraceAbsoluteInformationPreservationTransport trace presentation
        (ClassicalPeriods.TraceCategoryStructure.fromCampaign8 closure)
        assignmentTable closure) :
    TraceLocalizationAxiomWitnesses presentation :=
  ofClassicalTheorems transport.classicalTheorems

end TraceLocalizationAxiomWitnesses

namespace TraceAbsoluteInformationPreservation

def ofTransport
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext)
    (transport :
      TraceAbsoluteInformationPreservationTransport trace presentation traceCategory
        assignmentTable closure) :
    TraceAbsoluteInformationPreservation trace presentation :=
  let axiomWitnesses :=
    TraceLocalizationAxiomWitnesses.ofClassicalTheorems transport.classicalTheorems
  { compactGenerationData :=
      TraceCompactGenerationData.ofFiveFamilyClosure axiomWitnesses traceCategory assignmentTable
        transport.compactGenerationTransport
    triangulatedCoherenceData :=
      TraceTriangulatedCoherenceData.ofTraceConesAndLocalization axiomWitnesses traceCategory
        assignmentTable transport.triangulatedCoherenceTransport
    symmetricMonoidalCoherenceData :=
      TraceSymmetricMonoidalCoherenceData.ofTraceTensorWitnesses traceCategory assignmentTable
        transport.tensorExactnessTransport transport.symmetricMonoidalReplayTransport }

def ofCertifiedContracts
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext)
    (certifiedPresentation : CertifiedClassicalMotivicPresentation presentation)
    (certifiedTraceStructure :
      CertifiedTraceCategoryStructuralTransport trace presentation traceCategory
        assignmentTable closure) :
    TraceAbsoluteInformationPreservation trace presentation :=
  ofTransport presentation traceCategory assignmentTable closure
    (TraceAbsoluteInformationPreservationTransport.ofCertifiedContracts traceCategory
      assignmentTable closure certifiedPresentation certifiedTraceStructure)

def ofTraceCategoryAndClassicalPresentation
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (theoremPackage : ClassicalDMgmQPresentationTheorems presentation)
    (compactWitness :
      FiveFamilyCompactGenerationWitness trace presentation presentation.classicalContext)
    (triangulatedObligations :
      TraceTriangulatedCoherenceObligations presentation.classicalContext)
    (tensorCompatibility : TraceTensorConeCompatibilityData presentation.classicalContext)
    (monoidalReplay : TraceMonoidalReplayCoherenceData presentation.classicalContext) :
    TraceAbsoluteInformationPreservation trace presentation :=
  let axiomWitnesses :=
    TraceLocalizationAxiomWitnesses.ofClassicalTheorems theoremPackage
  { compactGenerationData :=
      TraceCompactGenerationData.ofFiveFamilyClosure axiomWitnesses traceCategory assignmentTable
        compactWitness
    triangulatedCoherenceData :=
      TraceTriangulatedCoherenceData.ofTraceConesAndLocalization axiomWitnesses traceCategory
        assignmentTable triangulatedObligations
    symmetricMonoidalCoherenceData :=
      TraceSymmetricMonoidalCoherenceData.ofTraceTensorWitnesses traceCategory assignmentTable
        tensorCompatibility monoidalReplay }

def ofTraceCategoryAndReplayData
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (corrReplay :
      CorrClosureReplayWitness presentation presentation.classicalContext assignmentTable
        traceCategory.package)
    (locReplay :
      LocTriangleClosureReplayWitness presentation presentation.classicalContext assignmentTable
        traceCategory.package)
    (nisReplay :
      NisDescentClosureReplayWitness presentation presentation.classicalContext assignmentTable
        traceCategory.package)
    (a1Replay :
      A1HomotopyClosureReplayWitness presentation presentation.classicalContext assignmentTable
        traceCategory.package)
    (envReplay :
      EnvEnvelopeClosureReplayWitness presentation presentation.classicalContext assignmentTable
        traceCategory.package)
    (compactWitness :
      FiveFamilyCompactGenerationWitness trace presentation presentation.classicalContext)
    (triangulatedObligations :
      TraceTriangulatedCoherenceObligations presentation.classicalContext)
    (tensorCompatibility : TraceTensorConeCompatibilityData presentation.classicalContext)
    (monoidalReplay : TraceMonoidalReplayCoherenceData presentation.classicalContext) :
    TraceAbsoluteInformationPreservation trace presentation :=
  ofTraceCategoryAndClassicalPresentation presentation traceCategory assignmentTable
    (TraceLocalizationAxiomWitnesses.ofAssignmentTableAndClosure presentation assignmentTable
      traceCategory.package corrReplay locReplay nisReplay a1Replay envReplay).theoremPackage
    compactWitness triangulatedObligations tensorCompatibility monoidalReplay

def ofTraceCategoryStructure
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (corrReplay :
      CorrClosureReplayWitness presentation presentation.classicalContext assignmentTable
        traceCategory.package)
    (locReplay :
      LocTriangleClosureReplayWitness presentation presentation.classicalContext assignmentTable
        traceCategory.package)
    (nisReplay :
      NisDescentClosureReplayWitness presentation presentation.classicalContext assignmentTable
        traceCategory.package)
    (a1Replay :
      A1HomotopyClosureReplayWitness presentation presentation.classicalContext assignmentTable
        traceCategory.package)
    (envReplay :
      EnvEnvelopeClosureReplayWitness presentation presentation.classicalContext assignmentTable
        traceCategory.package)
    (compactWitness :
      FiveFamilyCompactGenerationWitness trace presentation presentation.classicalContext)
    (triangulatedObligations :
      TraceTriangulatedCoherenceObligations presentation.classicalContext)
    (tensorCompatibility : TraceTensorConeCompatibilityData presentation.classicalContext)
    (monoidalReplay : TraceMonoidalReplayCoherenceData presentation.classicalContext) :
    TraceAbsoluteInformationPreservation trace presentation :=
  ofTraceCategoryAndReplayData presentation traceCategory assignmentTable corrReplay
    locReplay nisReplay a1Replay envReplay compactWitness triangulatedObligations
    tensorCompatibility monoidalReplay

end TraceAbsoluteInformationPreservation

namespace ClassicalDMgmQStructuralObligations

def ofTraceAbsoluteInformationPreservation
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (preservation : TraceAbsoluteInformationPreservation trace presentation) :
    ClassicalDMgmQStructuralObligations trace presentation where
  compactGeometricGenerationData := preservation.compactGenerationData
  exactTriangulatedStructureData := preservation.triangulatedCoherenceData
  symmetricMonoidalStructureData := preservation.symmetricMonoidalCoherenceData

end ClassicalDMgmQStructuralObligations

namespace ClassicalDMgmQIdentificationObligations

def ofStructuralObligations
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (obligations : ClassicalDMgmQStructuralObligations trace presentation) :
    ClassicalDMgmQIdentificationObligations trace presentation where
  BaseFieldWitness := ULift.{z} Rat
  baseFieldWitness := ⟨0⟩
  CoefficientFieldWitness := ULift.{z} Rat
  coefficientFieldWitness := ⟨0⟩
  baseFieldIsQTarget :=
    { toRat := fun q => q.down
      fromRat := fun q => ⟨q⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  coefficientFieldIsQTarget :=
    { toRat := fun q => q.down
      fromRat := fun q => ⟨q⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  compactGeometricGenerationTarget := ⟨obligations.compactGeometricGenerationData⟩
  exactTriangulatedStructureTarget := ⟨obligations.exactTriangulatedStructureData⟩
  symmetricMonoidalStructureTarget := ⟨obligations.symmetricMonoidalStructureData⟩

end ClassicalDMgmQIdentificationObligations

namespace ClassicalMotivicPresentation

def classicalDMgmQTargetOfTransport
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext)
    (transport :
      TraceAbsoluteInformationPreservationTransport trace presentation traceCategory
        assignmentTable closure)
    (idempotentComplete : presentation.motivicCategory.idempotentCompleteTarget)
    (qLinear : presentation.motivicCategory.qLinearTarget) :
    ClassicalDMgmQTarget trace presentation :=
  let obligations :=
    ClassicalDMgmQIdentificationObligations.ofStructuralObligations
      (ClassicalDMgmQStructuralObligations.ofTraceAbsoluteInformationPreservation
        (TraceAbsoluteInformationPreservation.ofTransport presentation traceCategory assignmentTable
          closure transport))
  { BaseFieldWitness := obligations.BaseFieldWitness
    baseFieldWitness := obligations.baseFieldWitness
    CoefficientFieldWitness := obligations.CoefficientFieldWitness
    coefficientFieldWitness := obligations.coefficientFieldWitness
    baseFieldIsQTarget := obligations.baseFieldIsQTarget
    coefficientFieldIsQTarget := obligations.coefficientFieldIsQTarget
    finiteCorrespondenceTransfers := presentation.admissibleLocalizationAxioms.Corr
    localizationTriangles := presentation.admissibleLocalizationAxioms.Loc
    nisnevichDescent := presentation.admissibleLocalizationAxioms.Nis
    a1Invariance := presentation.admissibleLocalizationAxioms.A1
    envelopeExactness := presentation.admissibleLocalizationAxioms.Env
    compactGeometricGenerationTarget := obligations.compactGeometricGenerationTarget
    exactTriangulatedStructureTarget := obligations.exactTriangulatedStructureTarget
    symmetricMonoidalStructureTarget := obligations.symmetricMonoidalStructureTarget
    idempotentEnvelopeClosureTarget :=
      ⟨idempotentComplete, transport.classicalTheorems.env_exactness_holds⟩
    qLinearCompatibilityTarget := qLinear }

def classicalDMgmQTarget
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (obligations : ClassicalDMgmQIdentificationObligations trace presentation)
    (idempotentEnvelope : presentation.motivicCategory.idempotentCompleteTarget ∧
      presentation.admissibleLocalizationAxioms.Env.exactnessTarget)
    (qLinear : presentation.motivicCategory.qLinearTarget) :
    ClassicalDMgmQTarget trace presentation where
  BaseFieldWitness := obligations.BaseFieldWitness
  baseFieldWitness := obligations.baseFieldWitness
  CoefficientFieldWitness := obligations.CoefficientFieldWitness
  coefficientFieldWitness := obligations.coefficientFieldWitness
  baseFieldIsQTarget := obligations.baseFieldIsQTarget
  coefficientFieldIsQTarget := obligations.coefficientFieldIsQTarget
  finiteCorrespondenceTransfers := presentation.admissibleLocalizationAxioms.Corr
  localizationTriangles := presentation.admissibleLocalizationAxioms.Loc
  nisnevichDescent := presentation.admissibleLocalizationAxioms.Nis
  a1Invariance := presentation.admissibleLocalizationAxioms.A1
  envelopeExactness := presentation.admissibleLocalizationAxioms.Env
  compactGeometricGenerationTarget := obligations.compactGeometricGenerationTarget
  exactTriangulatedStructureTarget := obligations.exactTriangulatedStructureTarget
  symmetricMonoidalStructureTarget := obligations.symmetricMonoidalStructureTarget
  idempotentEnvelopeClosureTarget := idempotentEnvelope
  qLinearCompatibilityTarget := qLinear

def classicalDMgmQTargetOfStructuralObligations
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (obligations : ClassicalDMgmQStructuralObligations trace presentation)
    (idempotentEnvelope : presentation.motivicCategory.idempotentCompleteTarget ∧
      presentation.admissibleLocalizationAxioms.Env.exactnessTarget)
    (qLinear : presentation.motivicCategory.qLinearTarget) :
    ClassicalDMgmQTarget trace presentation :=
  presentation.classicalDMgmQTarget
    (ClassicalDMgmQIdentificationObligations.ofStructuralObligations obligations)
    idempotentEnvelope qLinear

def classicalDMgmQTargetOfTraceAbsoluteInformationPreservation
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (preservation : TraceAbsoluteInformationPreservation.{u, v, w, x, y, z} trace presentation)
    (idempotentComplete : presentation.motivicCategory.idempotentCompleteTarget)
    (qLinear : presentation.motivicCategory.qLinearTarget) :
    ClassicalDMgmQTarget trace presentation :=
  let envExactness := preservation.triangulatedCoherenceData.envelopeExactTriangleClosure
  presentation.classicalDMgmQTargetOfStructuralObligations
    (ClassicalDMgmQStructuralObligations.ofTraceAbsoluteInformationPreservation preservation)
    ⟨idempotentComplete, envExactness⟩ qLinear

def classicalDMgmQTargetOfTraceCategoryStructure
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (corrReplay :
      CorrClosureReplayWitness presentation presentation.classicalContext assignmentTable
        traceCategory.package)
    (locReplay :
      LocTriangleClosureReplayWitness presentation presentation.classicalContext assignmentTable
        traceCategory.package)
    (nisReplay :
      NisDescentClosureReplayWitness presentation presentation.classicalContext assignmentTable
        traceCategory.package)
    (a1Replay :
      A1HomotopyClosureReplayWitness presentation presentation.classicalContext assignmentTable
        traceCategory.package)
    (envReplay :
      EnvEnvelopeClosureReplayWitness presentation presentation.classicalContext assignmentTable
        traceCategory.package)
    (compactWitness :
      FiveFamilyCompactGenerationWitness trace presentation presentation.classicalContext)
    (triangulatedObligations :
      TraceTriangulatedCoherenceObligations presentation.classicalContext)
    (tensorCompatibility : TraceTensorConeCompatibilityData presentation.classicalContext)
    (monoidalReplay : TraceMonoidalReplayCoherenceData presentation.classicalContext)
    (idempotentComplete : presentation.motivicCategory.idempotentCompleteTarget)
    (qLinear : presentation.motivicCategory.qLinearTarget) :
    ClassicalDMgmQTarget trace presentation :=
  presentation.classicalDMgmQTargetOfTraceAbsoluteInformationPreservation
    (TraceAbsoluteInformationPreservation.ofTraceCategoryStructure presentation traceCategory
      assignmentTable corrReplay locReplay nisReplay a1Replay envReplay compactWitness
      triangulatedObligations tensorCompatibility monoidalReplay)
    idempotentComplete qLinear

abbrev identifiedAsDMgmQ
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (obligations : ClassicalDMgmQIdentificationObligations trace presentation)
    (idempotentEnvelope : presentation.motivicCategory.idempotentCompleteTarget ∧
      presentation.admissibleLocalizationAxioms.Env.exactnessTarget)
    (qLinear : presentation.motivicCategory.qLinearTarget) :=
  presentation.classicalDMgmQTarget obligations idempotentEnvelope qLinear

abbrev identifiedAsDMgmQOfStructuralObligations
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (obligations : ClassicalDMgmQStructuralObligations trace presentation)
    (idempotentEnvelope : presentation.motivicCategory.idempotentCompleteTarget ∧
      presentation.admissibleLocalizationAxioms.Env.exactnessTarget)
    (qLinear : presentation.motivicCategory.qLinearTarget) :=
  presentation.classicalDMgmQTargetOfStructuralObligations obligations idempotentEnvelope qLinear

abbrev identifiedAsDMgmQOfTraceAbsoluteInformationPreservation
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (preservation : TraceAbsoluteInformationPreservation trace presentation)
    (idempotentComplete : presentation.motivicCategory.idempotentCompleteTarget)
    (qLinear : presentation.motivicCategory.qLinearTarget) :=
  presentation.classicalDMgmQTargetOfTraceAbsoluteInformationPreservation preservation
    idempotentComplete qLinear

abbrev identifiedAsDMgmQOfTraceCategoryStructure
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (corrReplay :
      CorrClosureReplayWitness presentation presentation.classicalContext assignmentTable
        traceCategory.package)
    (locReplay :
      LocTriangleClosureReplayWitness presentation presentation.classicalContext assignmentTable
        traceCategory.package)
    (nisReplay :
      NisDescentClosureReplayWitness presentation presentation.classicalContext assignmentTable
        traceCategory.package)
    (a1Replay :
      A1HomotopyClosureReplayWitness presentation presentation.classicalContext assignmentTable
        traceCategory.package)
    (envReplay :
      EnvEnvelopeClosureReplayWitness presentation presentation.classicalContext assignmentTable
        traceCategory.package)
    (compactWitness :
      FiveFamilyCompactGenerationWitness trace presentation presentation.classicalContext)
    (triangulatedObligations :
      TraceTriangulatedCoherenceObligations presentation.classicalContext)
    (tensorCompatibility : TraceTensorConeCompatibilityData presentation.classicalContext)
    (monoidalReplay : TraceMonoidalReplayCoherenceData presentation.classicalContext)
    (idempotentComplete : presentation.motivicCategory.idempotentCompleteTarget)
    (qLinear : presentation.motivicCategory.qLinearTarget) :=
  presentation.classicalDMgmQTargetOfTraceCategoryStructure traceCategory assignmentTable
    corrReplay locReplay nisReplay a1Replay envReplay compactWitness
    triangulatedObligations tensorCompatibility monoidalReplay idempotentComplete qLinear

end ClassicalMotivicPresentation


/-- Admissible theorem-target recipient for a future $DM_{gm}$-style universal property. -/
structure ExactSymmetricMonoidalRealizationTarget
    (trace : TracePresentation.{u, v, w, x, y})
    (recognized : MotivicCategoryCandidate trace.base) where
  targetCategory : MotivicCategoryCandidate trace.base
  exactnessTarget : Prop
  symmetricMonoidalTarget : Prop
  qLinearTarget : Prop
  realizationCompatibilityTarget : Prop

/-- Compatibility package saying a realization target satisfies the five trace-side motivic input
obligations used by the recognition theorem target. -/
structure AdmissibleMotivicTarget
    (trace : TracePresentation.{u, v, w, x, y})
    (presentation : ClassicalMotivicPresentation trace) where
  realizationTarget :
    ExactSymmetricMonoidalRealizationTarget trace presentation.motivicCategory
  corrCompatibilityTarget : Prop
  locCompatibilityTarget : Prop
  nisCompatibilityTarget : Prop
  a1CompatibilityTarget : Prop
  envCompatibilityTarget : Prop

/-- Proof-relevant factorization datum for a trace-side motivic recipient.

This is the constructive front end of Campaign 12: a recipient is not merely
declared compatible by a proposition, but comes with a concrete functor-shaped
factorization together with the five geometric/motivic compatibility witnesses
it is required to preserve. -/
structure MotivicLocalizationFactorizationData
    (trace : TracePresentation.{u, v, w, x, y})
    (presentation : ClassicalMotivicPresentation trace)
    (admissible : AdmissibleMotivicTarget trace presentation) where
  functorCandidate : MotivicFunctorCandidate
    presentation.motivicCategory
    admissible.realizationTarget.targetCategory
  exactnessWitness : admissible.realizationTarget.exactnessTarget
  symmetricMonoidalWitness : admissible.realizationTarget.symmetricMonoidalTarget
  qLinearWitness : admissible.realizationTarget.qLinearTarget
  realizationCompatibilityWitness : admissible.realizationTarget.realizationCompatibilityTarget
  corrCompatibilityWitness : admissible.corrCompatibilityTarget
  locCompatibilityWitness : admissible.locCompatibilityTarget
  nisCompatibilityWitness : admissible.nisCompatibilityTarget
  a1CompatibilityWitness : admissible.a1CompatibilityTarget
  envCompatibilityWitness : admissible.envCompatibilityTarget

/-- Proof-bearing certification of a fixed admissible recipient.

`AdmissibleMotivicTarget` only records the theorem targets that a recipient is
supposed to satisfy. Campaign 12V needs the stronger proof-relevant surface
that actually chooses a factorization functor and supplies the witnesses named
by those targets, one admissible recipient at a time. -/
structure CertifiedAdmissibleMotivicTarget
    (trace : TracePresentation.{u, v, w, x, y})
    (presentation : ClassicalMotivicPresentation trace)
    (admissible : AdmissibleMotivicTarget trace presentation) where
  functorCandidate : MotivicFunctorCandidate
    presentation.motivicCategory
    admissible.realizationTarget.targetCategory
  exactnessWitness : admissible.realizationTarget.exactnessTarget
  symmetricMonoidalWitness : admissible.realizationTarget.symmetricMonoidalTarget
  qLinearWitness : admissible.realizationTarget.qLinearTarget
  realizationCompatibilityWitness : admissible.realizationTarget.realizationCompatibilityTarget
  corrCompatibilityWitness : admissible.corrCompatibilityTarget
  locCompatibilityWitness : admissible.locCompatibilityTarget
  nisCompatibilityWitness : admissible.nisCompatibilityTarget
  a1CompatibilityWitness : admissible.a1CompatibilityTarget
  envCompatibilityWitness : admissible.envCompatibilityTarget

/-- Exact semantic source for the Campaign 12 functor candidate attached to a
fixed admissible recipient.

The candidate is assembled directly from a shared object interpreter on
motivic objects and a shared morphism evaluator on motivic morphisms. The
functoriality targets are carried here as proof-relevant data so downstream
packages can use the resulting `MotivicFunctorCandidate` definitionally rather
than proving after the fact that an arbitrary choice secretly came from these
semantics. -/
structure BoundaryFrontierFunctorCandidateData
    (trace : TracePresentation.{u, v, w, x, y})
    (presentation : ClassicalMotivicPresentation trace)
    (admissible : AdmissibleMotivicTarget trace presentation) where
  boundaryObjectInterpreter :
    presentation.motivicCategory.Object →
      admissible.realizationTarget.targetCategory.Object
  frontierMorphismEvaluator :
    ∀ {X Y : presentation.motivicCategory.Object},
      presentation.motivicCategory.Hom X Y →
        admissible.realizationTarget.targetCategory.Hom
          (boundaryObjectInterpreter X)
          (boundaryObjectInterpreter Y)
  mapIdTarget : Prop
  mapCompTarget : Prop
  mapId_holds : mapIdTarget
  mapComp_holds : mapCompTarget

namespace BoundaryFrontierFunctorCandidateData

def toMotivicFunctorCandidate
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {admissible : AdmissibleMotivicTarget trace presentation}
    (data : BoundaryFrontierFunctorCandidateData trace presentation admissible) :
    MotivicFunctorCandidate presentation.motivicCategory
      admissible.realizationTarget.targetCategory where
  obj := data.boundaryObjectInterpreter
  map := data.frontierMorphismEvaluator
  mapIdTarget := data.mapIdTarget
  mapCompTarget := data.mapCompTarget

end BoundaryFrontierFunctorCandidateData

/-- Minimal proof-bearing readiness package for constructing a certified
admissible recipient.

The pinned `DM_gm(Q)_Q` presentation together with Package A still does not
determine, for an arbitrary admissible recipient, the semantic object and
morphism interpreters of the required factorization functor. This readiness
wrapper carries exactly that remaining recipient-specific semantic data and the
compatibility witnesses attached to the induced functor candidate. -/
structure CertifiedAdmissibleMotivicTargetReadiness
    (trace : TracePresentation.{u, v, w, x, y})
    (presentation : ClassicalMotivicPresentation trace)
    (admissible : AdmissibleMotivicTarget trace presentation) where
  semanticFunctorCandidateData :
    BoundaryFrontierFunctorCandidateData trace presentation admissible
  exactnessWitness : admissible.realizationTarget.exactnessTarget
  symmetricMonoidalWitness : admissible.realizationTarget.symmetricMonoidalTarget
  qLinearWitness : admissible.realizationTarget.qLinearTarget
  realizationCompatibilityWitness : admissible.realizationTarget.realizationCompatibilityTarget
  corrCompatibilityWitness : admissible.corrCompatibilityTarget
  locCompatibilityWitness : admissible.locCompatibilityTarget
  nisCompatibilityWitness : admissible.nisCompatibilityTarget
  a1CompatibilityWitness : admissible.a1CompatibilityTarget
  envCompatibilityWitness : admissible.envCompatibilityTarget

namespace CertifiedAdmissibleMotivicTargetReadiness

def functorCandidate
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {admissible : AdmissibleMotivicTarget trace presentation}
    (readiness : CertifiedAdmissibleMotivicTargetReadiness trace presentation admissible) :
    MotivicFunctorCandidate presentation.motivicCategory
      admissible.realizationTarget.targetCategory :=
  readiness.semanticFunctorCandidateData.toMotivicFunctorCandidate

end CertifiedAdmissibleMotivicTargetReadiness

/-- Primitive five-family recursion package for interpreting certified traces
into a fixed admissible motivic target.

This is the constructive Campaign 12 source: it chooses a family of candidate
interpreters, records how each primitive trace family is interpreted, and
supplies the admissibility witnesses needed to turn the distinguished
interpreter into a recipient-specific readiness certificate. -/
structure PrimitiveFiveFamilyInterpreterData
    (trace : TracePresentation.{u, v, w, x, y})
    (presentation : ClassicalMotivicPresentation trace)
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext)
    (admissible : AdmissibleMotivicTarget trace presentation) where
  InterpreterData : Type z
  distinguishedInterpreter : InterpreterData
  functorCandidate : InterpreterData → MotivicFunctorCandidate
    presentation.motivicCategory
    admissible.realizationTarget.targetCategory
  corrPacketInterpretationTarget : InterpreterData → Prop
  corrPacketInterpretation_holds :
    ∀ interp : InterpreterData, corrPacketInterpretationTarget interp
  locPacketInterpretationTarget : InterpreterData → Prop
  locPacketInterpretation_holds :
    ∀ interp : InterpreterData, locPacketInterpretationTarget interp
  nisPacketInterpretationTarget : InterpreterData → Prop
  nisPacketInterpretation_holds :
    ∀ interp : InterpreterData, nisPacketInterpretationTarget interp
  a1PacketInterpretationTarget : InterpreterData → Prop
  a1PacketInterpretation_holds :
    ∀ interp : InterpreterData, a1PacketInterpretationTarget interp
  envPacketInterpretationTarget : InterpreterData → Prop
  envPacketInterpretation_holds :
    ∀ interp : InterpreterData, envPacketInterpretationTarget interp
  identityPreservation : ∀ interp : InterpreterData, (functorCandidate interp).mapIdTarget
  compositionPreservation :
    ∀ interp : InterpreterData, (functorCandidate interp).mapCompTarget
  exactnessWitness : ∀ _interp : InterpreterData, admissible.realizationTarget.exactnessTarget
  symmetricMonoidalWitness :
    ∀ _interp : InterpreterData, admissible.realizationTarget.symmetricMonoidalTarget
  qLinearWitness : ∀ _interp : InterpreterData, admissible.realizationTarget.qLinearTarget
  realizationCompatibilityWitness :
    ∀ _interp : InterpreterData, admissible.realizationTarget.realizationCompatibilityTarget
  corrCompatibilityWitness : ∀ _interp : InterpreterData, admissible.corrCompatibilityTarget
  locCompatibilityWitness : ∀ _interp : InterpreterData, admissible.locCompatibilityTarget
  nisCompatibilityWitness : ∀ _interp : InterpreterData, admissible.nisCompatibilityTarget
  a1CompatibilityWitness : ∀ _interp : InterpreterData, admissible.a1CompatibilityTarget
  envCompatibilityWitness : ∀ _interp : InterpreterData, admissible.envCompatibilityTarget

namespace PrimitiveFiveFamilyInterpreterData

def ofAssignmentTableAndReadiness
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext}
    {admissible : AdmissibleMotivicTarget trace presentation}
    (readiness : CertifiedAdmissibleMotivicTargetReadiness trace presentation admissible)
    (InterpreterData : Type z)
    (distinguishedInterpreter : InterpreterData) :
    PrimitiveFiveFamilyInterpreterData trace presentation traceCategory assignmentTable closure
      admissible where
  InterpreterData := InterpreterData
  distinguishedInterpreter := distinguishedInterpreter
  functorCandidate := fun _ => readiness.functorCandidate
  corrPacketInterpretationTarget :=
    fun _ => ClassicalPeriods.CorrPacketSoundnessFromGeneratorRealizationTarget assignmentTable
  corrPacketInterpretation_holds :=
    fun _ => ClassicalPeriods.corrPacketSoundnessFromGeneratorRealization assignmentTable
  locPacketInterpretationTarget :=
    fun _ =>
      ClassicalPeriods.LocPacketPeriodCompatibilityFromGeneratorRealizationTarget
          assignmentTable ∧
        assignmentTable.locAssignment.triangleCompatibilityTarget
  locPacketInterpretation_holds :=
    fun _ => ClassicalPeriods.locPacketSoundnessFromGeneratorRealization assignmentTable
  nisPacketInterpretationTarget :=
    fun _ =>
      ClassicalPeriods.NisPacketComparisonFromGeneratorRealizationTarget assignmentTable ∧
        assignmentTable.nisAssignment.descentSquareCompatibilityTarget
  nisPacketInterpretation_holds :=
    fun _ => ClassicalPeriods.nisPacketSoundnessFromGeneratorRealization assignmentTable
  a1PacketInterpretationTarget :=
    fun _ =>
      ClassicalPeriods.A1PacketComparisonFromGeneratorRealizationTarget assignmentTable ∧
        assignmentTable.a1Assignment.framedExtractionTarget
  a1PacketInterpretation_holds :=
    fun _ => ClassicalPeriods.a1PacketSoundnessFromGeneratorRealization assignmentTable
  envPacketInterpretationTarget :=
    fun _ =>
      ClassicalPeriods.EnvPacketComparisonFromGeneratorRealizationTarget assignmentTable ∧
        assignmentTable.envAssignment.exactCompletionTarget
  envPacketInterpretation_holds :=
    fun _ => ClassicalPeriods.envPacketSoundnessFromGeneratorRealization assignmentTable
  identityPreservation := fun _ => readiness.semanticFunctorCandidateData.mapId_holds
  compositionPreservation := fun _ => readiness.semanticFunctorCandidateData.mapComp_holds
  exactnessWitness := fun _ => readiness.exactnessWitness
  symmetricMonoidalWitness := fun _ => readiness.symmetricMonoidalWitness
  qLinearWitness := fun _ => readiness.qLinearWitness
  realizationCompatibilityWitness := fun _ => readiness.realizationCompatibilityWitness
  corrCompatibilityWitness := fun _ => readiness.corrCompatibilityWitness
  locCompatibilityWitness := fun _ => readiness.locCompatibilityWitness
  nisCompatibilityWitness := fun _ => readiness.nisCompatibilityWitness
  a1CompatibilityWitness := fun _ => readiness.a1CompatibilityWitness
  envCompatibilityWitness := fun _ => readiness.envCompatibilityWitness

end PrimitiveFiveFamilyInterpreterData

/-- Exact theorem surface asserting that the primitive interpreter extends
across tensor, shift, cone/cofiber, localization, and envelope replay. -/
structure TraceInterpreterRespectsTensorConeReplay
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext}
    {admissible : AdmissibleMotivicTarget trace presentation}
    (primitive :
      PrimitiveFiveFamilyInterpreterData trace presentation traceCategory assignmentTable closure
        admissible) where
  tensorPreservationTarget : primitive.InterpreterData → Prop
  tensorPreservation_holds :
    ∀ interp : primitive.InterpreterData, tensorPreservationTarget interp
  shiftSuspensionPreservationTarget : primitive.InterpreterData → Prop
  shiftSuspensionPreservation_holds :
    ∀ interp : primitive.InterpreterData, shiftSuspensionPreservationTarget interp
  coneCofiberLocalizationPreservationTarget : primitive.InterpreterData → Prop
  coneCofiberLocalizationPreservation_holds :
    ∀ interp : primitive.InterpreterData, coneCofiberLocalizationPreservationTarget interp
  envelopeIdempotentClosurePreservationTarget : primitive.InterpreterData → Prop
  envelopeIdempotentClosurePreservation_holds :
    ∀ interp : primitive.InterpreterData,
      envelopeIdempotentClosurePreservationTarget interp

namespace TraceInterpreterRespectsTensorConeReplay

def ofTransport
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext}
    {admissible : AdmissibleMotivicTarget trace presentation}
    (primitive :
      PrimitiveFiveFamilyInterpreterData trace presentation traceCategory assignmentTable closure
        admissible)
    (informationTransport :
      TraceAbsoluteInformationPreservationTransport trace presentation traceCategory
        assignmentTable closure)
    (tensorPreservation :
      ∀ interp : primitive.InterpreterData,
        TraceTensorExactnessLaw
            informationTransport.tensorExactnessTransport.tensorClosureWitness
            informationTransport.tensorExactnessTransport.coneClosureWitness
            informationTransport.tensorExactnessTransport.cofiberClosureWitness ∧
          TraceSymmetricMonoidalStructureLaw
            informationTransport.symmetricMonoidalReplayTransport.leftUnitorReplay
            informationTransport.symmetricMonoidalReplayTransport.rightUnitorReplay
            informationTransport.symmetricMonoidalReplayTransport.associatorReplay
            informationTransport.symmetricMonoidalReplayTransport.braidingReplay)
    (shiftSuspensionPreservation :
      ∀ interp : primitive.InterpreterData,
        informationTransport.triangulatedCoherenceTransport.shiftClosureWitness.formalClosureTarget)
    (coneCofiberLocalizationPreservation :
      ∀ interp : primitive.InterpreterData,
        TraceExactTriangulatedStructureLaw
            informationTransport.triangulatedCoherenceTransport.shiftClosureWitness
            informationTransport.triangulatedCoherenceTransport.coneClosureWitness
            informationTransport.triangulatedCoherenceTransport.cofiberClosureWitness ∧
          TraceTensorPreservesLocalizationLaw
            informationTransport.tensorExactnessTransport.tensorClosureWitness
            informationTransport.tensorExactnessTransport.coneClosureWitness
            informationTransport.tensorExactnessTransport.cofiberClosureWitness)
    (envelopeIdempotentClosurePreservation :
      ∀ interp : primitive.InterpreterData,
        closure.closureComparisonTarget ∧
          TraceFiveFamilyClosurePreservationLaw
            informationTransport.symmetricMonoidalReplayTransport.leftUnitorReplay
            informationTransport.symmetricMonoidalReplayTransport.rightUnitorReplay
            informationTransport.symmetricMonoidalReplayTransport.associatorReplay) :
    TraceInterpreterRespectsTensorConeReplay (primitive := primitive) where
  tensorPreservationTarget :=
    fun _ =>
      TraceTensorExactnessLaw
          informationTransport.tensorExactnessTransport.tensorClosureWitness
          informationTransport.tensorExactnessTransport.coneClosureWitness
          informationTransport.tensorExactnessTransport.cofiberClosureWitness ∧
        TraceSymmetricMonoidalStructureLaw
          informationTransport.symmetricMonoidalReplayTransport.leftUnitorReplay
          informationTransport.symmetricMonoidalReplayTransport.rightUnitorReplay
          informationTransport.symmetricMonoidalReplayTransport.associatorReplay
          informationTransport.symmetricMonoidalReplayTransport.braidingReplay
  tensorPreservation_holds := tensorPreservation
  shiftSuspensionPreservationTarget :=
    fun _ =>
      informationTransport.triangulatedCoherenceTransport.shiftClosureWitness.formalClosureTarget
  shiftSuspensionPreservation_holds := shiftSuspensionPreservation
  coneCofiberLocalizationPreservationTarget :=
    fun _ =>
      TraceExactTriangulatedStructureLaw
          informationTransport.triangulatedCoherenceTransport.shiftClosureWitness
          informationTransport.triangulatedCoherenceTransport.coneClosureWitness
          informationTransport.triangulatedCoherenceTransport.cofiberClosureWitness ∧
        TraceTensorPreservesLocalizationLaw
          informationTransport.tensorExactnessTransport.tensorClosureWitness
          informationTransport.tensorExactnessTransport.coneClosureWitness
          informationTransport.tensorExactnessTransport.cofiberClosureWitness
  coneCofiberLocalizationPreservation_holds := coneCofiberLocalizationPreservation
  envelopeIdempotentClosurePreservationTarget :=
    fun _ =>
      closure.closureComparisonTarget ∧
        TraceFiveFamilyClosurePreservationLaw
          informationTransport.symmetricMonoidalReplayTransport.leftUnitorReplay
          informationTransport.symmetricMonoidalReplayTransport.rightUnitorReplay
          informationTransport.symmetricMonoidalReplayTransport.associatorReplay
  envelopeIdempotentClosurePreservation_holds := envelopeIdempotentClosurePreservation

end TraceInterpreterRespectsTensorConeReplay

/-- Exact theorem surface asserting that the interpreter respects certified
trace equivalence and admissible closure. -/
structure TraceInterpreterRespectsCertifiedClosure
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext}
    {admissible : AdmissibleMotivicTarget trace presentation}
    (primitive :
      PrimitiveFiveFamilyInterpreterData trace presentation traceCategory assignmentTable closure
        admissible) where
  certifiedClosureRespectTarget : primitive.InterpreterData → Prop
  certifiedClosureRespect_holds :
    ∀ interp : primitive.InterpreterData, certifiedClosureRespectTarget interp

namespace TraceInterpreterRespectsCertifiedClosure

def ofClosureComparison
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext}
    {admissible : AdmissibleMotivicTarget trace presentation}
    (primitive :
      PrimitiveFiveFamilyInterpreterData trace presentation traceCategory assignmentTable closure
        admissible)
    (certifiedClosureRespect :
      ∀ interp : primitive.InterpreterData, closure.closureComparisonTarget) :
    TraceInterpreterRespectsCertifiedClosure (primitive := primitive) where
  certifiedClosureRespectTarget := fun _ => closure.closureComparisonTarget
  certifiedClosureRespect_holds := certifiedClosureRespect

end TraceInterpreterRespectsCertifiedClosure

/-- Exact uniqueness theorem surface for interpreter recursion via canonical
reconstruction / normalization. -/
structure TraceInterpreterUniquenessByReconstruction
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext}
    {admissible : AdmissibleMotivicTarget trace presentation}
    (primitive :
      PrimitiveFiveFamilyInterpreterData trace presentation traceCategory assignmentTable closure
        admissible) where
  uniqueFunctorCandidate :
    ∀ left right : primitive.InterpreterData,
      primitive.functorCandidate left = primitive.functorCandidate right

/-- Exact remaining Campaign 12 reconstruction-native theorem surface.

The existing repo now discharges the primitive five-family packet layer from
the assignment table, and the replay / certified-closure layers from concrete
transport and closure witnesses. What still does not follow from the current
interfaces is the final bridge from canonical reconstructed frontier data to
the object and morphism actions of the induced `MotivicFunctorCandidate`s.

The current codebase exposes canonical boundary/frontier reconstruction data,
but does not yet prove the two lower bridges needed to compute the functor
candidate itself:
- boundary data determines the chosen object action;
- frontier realization data determines the chosen morphism action.

The next eight structures isolate the exact remaining lower theorem surfaces and
the two derived canonical-frontier-word assembly points separately, so the
final interpreter uniqueness contract stays exact about what is still missing. -/
structure FunctorCandidateObjDefinedByBoundaryInterpreter
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext}
    {admissible : AdmissibleMotivicTarget trace presentation}
    (primitive :
      PrimitiveFiveFamilyInterpreterData trace presentation traceCategory assignmentTable closure
        admissible)
    (_tensorConeReplay :
      TraceInterpreterRespectsTensorConeReplay (primitive := primitive))
    (_certifiedClosure :
      TraceInterpreterRespectsCertifiedClosure (primitive := primitive)) where
  boundaryObjectInterpreter :
    presentation.motivicCategory.Object →
      admissible.realizationTarget.targetCategory.Object
  functorCandidateObj_eq_boundaryObjectInterpreter :
    ∀ interp : primitive.InterpreterData,
      (primitive.functorCandidate interp).obj = boundaryObjectInterpreter

namespace FunctorCandidateObjDefinedByBoundaryInterpreter

def ofAssignmentTableAndReadiness
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext}
    {admissible : AdmissibleMotivicTarget trace presentation}
    (readiness : CertifiedAdmissibleMotivicTargetReadiness trace presentation admissible)
    (InterpreterData : Type z)
    (distinguishedInterpreter : InterpreterData)
    {_tensorConeReplay :
      TraceInterpreterRespectsTensorConeReplay
        (primitive :=
          PrimitiveFiveFamilyInterpreterData.ofAssignmentTableAndReadiness
            (traceCategory := traceCategory)
            (assignmentTable := assignmentTable)
            (closure := closure)
            (admissible := admissible)
            readiness InterpreterData distinguishedInterpreter)}
    {_certifiedClosure :
      TraceInterpreterRespectsCertifiedClosure
        (primitive :=
          PrimitiveFiveFamilyInterpreterData.ofAssignmentTableAndReadiness
            (traceCategory := traceCategory)
            (assignmentTable := assignmentTable)
            (closure := closure)
            (admissible := admissible)
            readiness InterpreterData distinguishedInterpreter)} :
    FunctorCandidateObjDefinedByBoundaryInterpreter
      (primitive :=
        PrimitiveFiveFamilyInterpreterData.ofAssignmentTableAndReadiness
          (traceCategory := traceCategory)
          (assignmentTable := assignmentTable)
          (closure := closure)
          (admissible := admissible)
          readiness InterpreterData distinguishedInterpreter)
      (_tensorConeReplay := _tensorConeReplay)
      (_certifiedClosure := _certifiedClosure) where
  boundaryObjectInterpreter := readiness.semanticFunctorCandidateData.boundaryObjectInterpreter
  functorCandidateObj_eq_boundaryObjectInterpreter := by
    intro _interp
    rfl

end FunctorCandidateObjDefinedByBoundaryInterpreter

structure MotivicFunctorCandidateObjectActionDeterminedByBoundary
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext}
    {admissible : AdmissibleMotivicTarget trace presentation}
    (primitive :
      PrimitiveFiveFamilyInterpreterData trace presentation traceCategory assignmentTable closure
        admissible)
    (tensorConeReplay :
      TraceInterpreterRespectsTensorConeReplay (primitive := primitive))
    (certifiedClosure :
      TraceInterpreterRespectsCertifiedClosure (primitive := primitive)) where
  objectActionDeterminedByBoundary :
    ∀ left right : primitive.InterpreterData,
      (primitive.functorCandidate left).obj = (primitive.functorCandidate right).obj

namespace MotivicFunctorCandidateObjectActionDeterminedByBoundary

def ofBoundaryInterpreter
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext}
    {admissible : AdmissibleMotivicTarget trace presentation}
    {primitive :
      PrimitiveFiveFamilyInterpreterData trace presentation traceCategory assignmentTable closure
        admissible}
    {_tensorConeReplay :
      TraceInterpreterRespectsTensorConeReplay (primitive := primitive)}
    {_certifiedClosure :
      TraceInterpreterRespectsCertifiedClosure (primitive := primitive)}
    (boundaryInterpreter :
      FunctorCandidateObjDefinedByBoundaryInterpreter (primitive := primitive)
        (_tensorConeReplay := _tensorConeReplay)
        (_certifiedClosure := _certifiedClosure)) :
    MotivicFunctorCandidateObjectActionDeterminedByBoundary (primitive := primitive)
      (tensorConeReplay := _tensorConeReplay)
      (certifiedClosure := _certifiedClosure) where
  objectActionDeterminedByBoundary := by
    intro left right
    rw [boundaryInterpreter.functorCandidateObj_eq_boundaryObjectInterpreter left,
      boundaryInterpreter.functorCandidateObj_eq_boundaryObjectInterpreter right]

end MotivicFunctorCandidateObjectActionDeterminedByBoundary

structure CanonicalBoundaryDeterminesObjectAction
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext}
    {admissible : AdmissibleMotivicTarget trace presentation}
    (primitive :
      PrimitiveFiveFamilyInterpreterData trace presentation traceCategory assignmentTable closure
        admissible)
    (tensorConeReplay :
      TraceInterpreterRespectsTensorConeReplay (primitive := primitive))
    (certifiedClosure :
      TraceInterpreterRespectsCertifiedClosure (primitive := primitive)) where
  functorCandidateObjectActionDeterminedByBoundary :
    MotivicFunctorCandidateObjectActionDeterminedByBoundary (primitive := primitive)
      (tensorConeReplay := tensorConeReplay)
      (certifiedClosure := certifiedClosure)

namespace CanonicalBoundaryDeterminesObjectAction

def ofBoundaryInterpreter
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext}
    {admissible : AdmissibleMotivicTarget trace presentation}
    {primitive :
      PrimitiveFiveFamilyInterpreterData trace presentation traceCategory assignmentTable closure
        admissible}
    {_tensorConeReplay :
      TraceInterpreterRespectsTensorConeReplay (primitive := primitive)}
    {_certifiedClosure :
      TraceInterpreterRespectsCertifiedClosure (primitive := primitive)}
    (boundaryInterpreter :
      FunctorCandidateObjDefinedByBoundaryInterpreter (primitive := primitive)
        (_tensorConeReplay := _tensorConeReplay)
        (_certifiedClosure := _certifiedClosure)) :
    CanonicalBoundaryDeterminesObjectAction (primitive := primitive)
      (tensorConeReplay := _tensorConeReplay)
      (certifiedClosure := _certifiedClosure) where
  functorCandidateObjectActionDeterminedByBoundary :=
    MotivicFunctorCandidateObjectActionDeterminedByBoundary.ofBoundaryInterpreter
      boundaryInterpreter

theorem objectMapDeterminedByCanonicalBoundary
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext}
    {admissible : AdmissibleMotivicTarget trace presentation}
    {primitive :
      PrimitiveFiveFamilyInterpreterData trace presentation traceCategory assignmentTable closure
        admissible}
    {_tensorConeReplay :
      TraceInterpreterRespectsTensorConeReplay (primitive := primitive)}
    {_certifiedClosure :
      TraceInterpreterRespectsCertifiedClosure (primitive := primitive)}
    (boundary :
      CanonicalBoundaryDeterminesObjectAction (primitive := primitive)
        (tensorConeReplay := _tensorConeReplay)
        (certifiedClosure := _certifiedClosure)) :
    ∀ left right : primitive.InterpreterData,
      (primitive.functorCandidate left).obj = (primitive.functorCandidate right).obj :=
  boundary.functorCandidateObjectActionDeterminedByBoundary.objectActionDeterminedByBoundary

end CanonicalBoundaryDeterminesObjectAction

structure CanonicalFrontierWordDeterminesObj
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext}
    {admissible : AdmissibleMotivicTarget trace presentation}
    (primitive :
      PrimitiveFiveFamilyInterpreterData trace presentation traceCategory assignmentTable closure
        admissible)
    (tensorConeReplay :
      TraceInterpreterRespectsTensorConeReplay (primitive := primitive))
    (certifiedClosure :
      TraceInterpreterRespectsCertifiedClosure (primitive := primitive)) where
  boundaryDeterminesObjectAction :
    CanonicalBoundaryDeterminesObjectAction (primitive := primitive)
      (tensorConeReplay := tensorConeReplay)
      (certifiedClosure := certifiedClosure)

namespace CanonicalFrontierWordDeterminesObj

theorem objectMapDeterminedByCanonicalFrontierWord
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext}
    {admissible : AdmissibleMotivicTarget trace presentation}
    {primitive :
      PrimitiveFiveFamilyInterpreterData trace presentation traceCategory assignmentTable closure
        admissible}
    {_tensorConeReplay :
      TraceInterpreterRespectsTensorConeReplay (primitive := primitive)}
    {_certifiedClosure :
      TraceInterpreterRespectsCertifiedClosure (primitive := primitive)}
    (canonicalObj :
      CanonicalFrontierWordDeterminesObj (primitive := primitive)
        (tensorConeReplay := _tensorConeReplay)
        (certifiedClosure := _certifiedClosure)) :
    ∀ left right : primitive.InterpreterData,
      (primitive.functorCandidate left).obj = (primitive.functorCandidate right).obj :=
  CanonicalBoundaryDeterminesObjectAction.objectMapDeterminedByCanonicalBoundary
    canonicalObj.boundaryDeterminesObjectAction

end CanonicalFrontierWordDeterminesObj

structure FunctorCandidateMapDefinedByFrontierEvaluation
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext}
    {admissible : AdmissibleMotivicTarget trace presentation}
    (primitive :
      PrimitiveFiveFamilyInterpreterData trace presentation traceCategory assignmentTable closure
        admissible)
    (_tensorConeReplay :
      TraceInterpreterRespectsTensorConeReplay (primitive := primitive))
    (_certifiedClosure :
      TraceInterpreterRespectsCertifiedClosure (primitive := primitive))
    (boundaryObjectInterpreter :
      presentation.motivicCategory.Object →
        admissible.realizationTarget.targetCategory.Object) where
  frontierEvaluator :
    ∀ {X Y : presentation.motivicCategory.Object},
      presentation.motivicCategory.Hom X Y →
        admissible.realizationTarget.targetCategory.Hom
          (boundaryObjectInterpreter X)
          (boundaryObjectInterpreter Y)
  functorCandidateMap_heq_frontierEvaluator :
    ∀ (interp : primitive.InterpreterData)
      {X Y : presentation.motivicCategory.Object}
      (f : presentation.motivicCategory.Hom X Y),
        HEq ((primitive.functorCandidate interp).map f) (frontierEvaluator f)

namespace FunctorCandidateMapDefinedByFrontierEvaluation

def ofAssignmentTableAndReadiness
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext}
    {admissible : AdmissibleMotivicTarget trace presentation}
    (readiness : CertifiedAdmissibleMotivicTargetReadiness trace presentation admissible)
    (InterpreterData : Type z)
    (distinguishedInterpreter : InterpreterData)
    {_tensorConeReplay :
      TraceInterpreterRespectsTensorConeReplay
        (primitive :=
          PrimitiveFiveFamilyInterpreterData.ofAssignmentTableAndReadiness
            (traceCategory := traceCategory)
            (assignmentTable := assignmentTable)
            (closure := closure)
            (admissible := admissible)
            readiness InterpreterData distinguishedInterpreter)}
    {_certifiedClosure :
      TraceInterpreterRespectsCertifiedClosure
        (primitive :=
          PrimitiveFiveFamilyInterpreterData.ofAssignmentTableAndReadiness
            (traceCategory := traceCategory)
            (assignmentTable := assignmentTable)
            (closure := closure)
            (admissible := admissible)
            readiness InterpreterData distinguishedInterpreter)} :
    FunctorCandidateMapDefinedByFrontierEvaluation
      (primitive :=
        PrimitiveFiveFamilyInterpreterData.ofAssignmentTableAndReadiness
          (traceCategory := traceCategory)
          (assignmentTable := assignmentTable)
          (closure := closure)
          (admissible := admissible)
          readiness InterpreterData distinguishedInterpreter)
      (_tensorConeReplay := _tensorConeReplay)
      (_certifiedClosure := _certifiedClosure)
      readiness.semanticFunctorCandidateData.boundaryObjectInterpreter where
  frontierEvaluator := readiness.semanticFunctorCandidateData.frontierMorphismEvaluator
  functorCandidateMap_heq_frontierEvaluator := by
    intro _interp X Y f
    exact (show
      HEq
        (((PrimitiveFiveFamilyInterpreterData.ofAssignmentTableAndReadiness
              (traceCategory := traceCategory)
              (assignmentTable := assignmentTable)
              (closure := closure)
              (admissible := admissible)
              readiness InterpreterData distinguishedInterpreter).functorCandidate
            _interp).map f)
        (readiness.semanticFunctorCandidateData.frontierMorphismEvaluator f) from HEq.rfl)

end FunctorCandidateMapDefinedByFrontierEvaluation

structure MotivicFunctorCandidateMapDeterminedByFrontierRealization
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext}
    {admissible : AdmissibleMotivicTarget trace presentation}
    (primitive :
      PrimitiveFiveFamilyInterpreterData trace presentation traceCategory assignmentTable closure
        admissible)
    (tensorConeReplay :
      TraceInterpreterRespectsTensorConeReplay (primitive := primitive))
    (certifiedClosure :
      TraceInterpreterRespectsCertifiedClosure (primitive := primitive)) where
  mapActionDeterminedByFrontierRealization :
    ∀ left right : primitive.InterpreterData,
      ∀ {X Y : presentation.motivicCategory.Object}
        (f : presentation.motivicCategory.Hom X Y),
          HEq ((primitive.functorCandidate left).map f)
            ((primitive.functorCandidate right).map f)

namespace MotivicFunctorCandidateMapDeterminedByFrontierRealization

def ofFrontierEvaluation
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext}
    {admissible : AdmissibleMotivicTarget trace presentation}
    {primitive :
      PrimitiveFiveFamilyInterpreterData trace presentation traceCategory assignmentTable closure
        admissible}
    {_tensorConeReplay :
      TraceInterpreterRespectsTensorConeReplay (primitive := primitive)}
    {_certifiedClosure :
      TraceInterpreterRespectsCertifiedClosure (primitive := primitive)}
    (boundaryInterpreter :
      FunctorCandidateObjDefinedByBoundaryInterpreter (primitive := primitive)
        (_tensorConeReplay := _tensorConeReplay)
        (_certifiedClosure := _certifiedClosure))
    (frontierEvaluation :
      FunctorCandidateMapDefinedByFrontierEvaluation (primitive := primitive)
        (_tensorConeReplay := _tensorConeReplay)
        (_certifiedClosure := _certifiedClosure)
        boundaryInterpreter.boundaryObjectInterpreter) :
    MotivicFunctorCandidateMapDeterminedByFrontierRealization (primitive := primitive)
      (tensorConeReplay := _tensorConeReplay)
      (certifiedClosure := _certifiedClosure) where
  mapActionDeterminedByFrontierRealization := by
    intro left right X Y f
    exact HEq.trans
      (frontierEvaluation.functorCandidateMap_heq_frontierEvaluator left f)
      (HEq.symm (frontierEvaluation.functorCandidateMap_heq_frontierEvaluator right f))

end MotivicFunctorCandidateMapDeterminedByFrontierRealization

structure CanonicalFrontierRealizationDeterminesMorphismAction
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext}
    {admissible : AdmissibleMotivicTarget trace presentation}
    (primitive :
      PrimitiveFiveFamilyInterpreterData trace presentation traceCategory assignmentTable closure
        admissible)
    (tensorConeReplay :
      TraceInterpreterRespectsTensorConeReplay (primitive := primitive))
    (certifiedClosure :
      TraceInterpreterRespectsCertifiedClosure (primitive := primitive)) where
  functorCandidateMapDeterminedByFrontierRealization :
    MotivicFunctorCandidateMapDeterminedByFrontierRealization (primitive := primitive)
      (tensorConeReplay := tensorConeReplay)
      (certifiedClosure := certifiedClosure)

namespace CanonicalFrontierRealizationDeterminesMorphismAction

def ofFrontierEvaluation
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext}
    {admissible : AdmissibleMotivicTarget trace presentation}
    {primitive :
      PrimitiveFiveFamilyInterpreterData trace presentation traceCategory assignmentTable closure
        admissible}
    {_tensorConeReplay :
      TraceInterpreterRespectsTensorConeReplay (primitive := primitive)}
    {_certifiedClosure :
      TraceInterpreterRespectsCertifiedClosure (primitive := primitive)}
    (boundaryInterpreter :
      FunctorCandidateObjDefinedByBoundaryInterpreter (primitive := primitive)
        (_tensorConeReplay := _tensorConeReplay)
        (_certifiedClosure := _certifiedClosure))
    (frontierEvaluation :
      FunctorCandidateMapDefinedByFrontierEvaluation (primitive := primitive)
        (_tensorConeReplay := _tensorConeReplay)
        (_certifiedClosure := _certifiedClosure)
        boundaryInterpreter.boundaryObjectInterpreter) :
    CanonicalFrontierRealizationDeterminesMorphismAction (primitive := primitive)
      (tensorConeReplay := _tensorConeReplay)
      (certifiedClosure := _certifiedClosure) where
  functorCandidateMapDeterminedByFrontierRealization :=
    MotivicFunctorCandidateMapDeterminedByFrontierRealization.ofFrontierEvaluation
      boundaryInterpreter frontierEvaluation

theorem morphismMapDeterminedByCanonicalFrontierRealization
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext}
    {admissible : AdmissibleMotivicTarget trace presentation}
    {primitive :
      PrimitiveFiveFamilyInterpreterData trace presentation traceCategory assignmentTable closure
        admissible}
    {_tensorConeReplay :
      TraceInterpreterRespectsTensorConeReplay (primitive := primitive)}
    {_certifiedClosure :
      TraceInterpreterRespectsCertifiedClosure (primitive := primitive)}
    (frontier :
      CanonicalFrontierRealizationDeterminesMorphismAction (primitive := primitive)
        (tensorConeReplay := _tensorConeReplay)
        (certifiedClosure := _certifiedClosure)) :
    ∀ left right : primitive.InterpreterData,
      ∀ {X Y : presentation.motivicCategory.Object}
        (f : presentation.motivicCategory.Hom X Y),
          HEq ((primitive.functorCandidate left).map f)
            ((primitive.functorCandidate right).map f) :=
  frontier.functorCandidateMapDeterminedByFrontierRealization.mapActionDeterminedByFrontierRealization

end CanonicalFrontierRealizationDeterminesMorphismAction

structure CanonicalFrontierWordDeterminesMap
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext}
    {admissible : AdmissibleMotivicTarget trace presentation}
    (primitive :
      PrimitiveFiveFamilyInterpreterData trace presentation traceCategory assignmentTable closure
        admissible)
    (tensorConeReplay :
      TraceInterpreterRespectsTensorConeReplay (primitive := primitive))
    (certifiedClosure :
      TraceInterpreterRespectsCertifiedClosure (primitive := primitive)) where
  frontierRealizationDeterminesMorphismAction :
    CanonicalFrontierRealizationDeterminesMorphismAction (primitive := primitive)
      (tensorConeReplay := tensorConeReplay)
      (certifiedClosure := certifiedClosure)

namespace CanonicalFrontierWordDeterminesMap

theorem morphismMapDeterminedByCanonicalFrontierWord
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext}
    {admissible : AdmissibleMotivicTarget trace presentation}
    {primitive :
      PrimitiveFiveFamilyInterpreterData trace presentation traceCategory assignmentTable closure
        admissible}
    {_tensorConeReplay :
      TraceInterpreterRespectsTensorConeReplay (primitive := primitive)}
    {_certifiedClosure :
      TraceInterpreterRespectsCertifiedClosure (primitive := primitive)}
    (canonicalMap :
      CanonicalFrontierWordDeterminesMap (primitive := primitive)
        (tensorConeReplay := _tensorConeReplay)
        (certifiedClosure := _certifiedClosure)) :
    ∀ left right : primitive.InterpreterData,
      ∀ {X Y : presentation.motivicCategory.Object}
        (f : presentation.motivicCategory.Hom X Y),
          HEq ((primitive.functorCandidate left).map f)
            ((primitive.functorCandidate right).map f) := by
  exact
    CanonicalFrontierRealizationDeterminesMorphismAction.morphismMapDeterminedByCanonicalFrontierRealization
      canonicalMap.frontierRealizationDeterminesMorphismAction

end CanonicalFrontierWordDeterminesMap

structure CanonicalFrontierWordDeterminesInterpreter
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext}
    {admissible : AdmissibleMotivicTarget trace presentation}
    (primitive :
      PrimitiveFiveFamilyInterpreterData trace presentation traceCategory assignmentTable closure
        admissible)
    (tensorConeReplay :
      TraceInterpreterRespectsTensorConeReplay (primitive := primitive))
    (certifiedClosure :
      TraceInterpreterRespectsCertifiedClosure (primitive := primitive)) where
  objectAction :
    CanonicalFrontierWordDeterminesObj (primitive := primitive)
      (tensorConeReplay := tensorConeReplay)
      (certifiedClosure := certifiedClosure)
  morphismAction :
    CanonicalFrontierWordDeterminesMap (primitive := primitive)
      (tensorConeReplay := tensorConeReplay)
      (certifiedClosure := certifiedClosure)

namespace CanonicalFrontierWordDeterminesInterpreter

theorem uniqueFunctorCandidate
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext}
    {admissible : AdmissibleMotivicTarget trace presentation}
    {primitive :
      PrimitiveFiveFamilyInterpreterData trace presentation traceCategory assignmentTable closure
        admissible}
    {_tensorConeReplay :
      TraceInterpreterRespectsTensorConeReplay (primitive := primitive)}
    {_certifiedClosure :
      TraceInterpreterRespectsCertifiedClosure (primitive := primitive)}
    (canonical :
      CanonicalFrontierWordDeterminesInterpreter (primitive := primitive)
        (tensorConeReplay := _tensorConeReplay)
        (certifiedClosure := _certifiedClosure)) :
    ∀ left right : primitive.InterpreterData,
      primitive.functorCandidate left = primitive.functorCandidate right := by
  intro left right
  apply MotivicFunctorCandidate.ext_of_obj_map
  · exact canonical.objectAction.objectMapDeterminedByCanonicalFrontierWord left right
  · exact canonical.morphismAction.morphismMapDeterminedByCanonicalFrontierWord left right
  · exact primitive.identityPreservation left
  · exact primitive.identityPreservation right
  · exact primitive.compositionPreservation left
  · exact primitive.compositionPreservation right

end CanonicalFrontierWordDeterminesInterpreter

namespace TraceInterpreterUniquenessByReconstruction

def ofCanonicalFrontierWord
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext}
    {admissible : AdmissibleMotivicTarget trace presentation}
    (primitive :
      PrimitiveFiveFamilyInterpreterData trace presentation traceCategory assignmentTable closure
        admissible)
    (tensorConeReplay :
      TraceInterpreterRespectsTensorConeReplay (primitive := primitive))
    (certifiedClosure :
      TraceInterpreterRespectsCertifiedClosure (primitive := primitive))
    (canonical :
      CanonicalFrontierWordDeterminesInterpreter (primitive := primitive)
        (tensorConeReplay := tensorConeReplay)
        (certifiedClosure := certifiedClosure)) :
    TraceInterpreterUniquenessByReconstruction (primitive := primitive) where
  uniqueFunctorCandidate :=
    CanonicalFrontierWordDeterminesInterpreter.uniqueFunctorCandidate canonical

end TraceInterpreterUniquenessByReconstruction

/-- Constructive Campaign 12A interpreter package for a fixed admissible
recipient.

Campaign 12A -- Triangulated/stable motivic recognition -- is closed at the
trace-interpreter level. The load-bearing recognition path is now:

`BoundaryFrontierFunctorCandidateData`
→ semantic `MotivicFunctorCandidate`
→ object/map determination
→ `CanonicalFrontierWordDeterminesInterpreter`
→ `TraceInterpreterUniquenessByReconstruction`
→ `TraceInterpreterForAdmissibleMotivicTarget.ofConcreteTransport`
→ `CertifiedAdmissibleMotivicTargetReadiness`
→ `ConcreteMotivicLocalizationFactorizationFamily`
→ `MotivicLocalizationUniversalFactorizationTransport`
→ `TraceCategoryMotivicLocalizationUniversalProperty`.

This packages exactly the proof-relevant data expected from trace recursion:
primitive five-family interpretation, replay compatibility, certified-closure
respect, and uniqueness by canonical reconstruction. -/
structure TraceInterpreterForAdmissibleMotivicTarget
    (trace : TracePresentation.{u, v, w, x, y})
    (presentation : ClassicalMotivicPresentation trace)
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext)
    (admissible : AdmissibleMotivicTarget trace presentation) where
  semanticFunctorCandidateData :
    BoundaryFrontierFunctorCandidateData trace presentation admissible
  primitiveFiveFamily :
    PrimitiveFiveFamilyInterpreterData trace presentation traceCategory assignmentTable closure
      admissible
  tensorConeReplay :
    TraceInterpreterRespectsTensorConeReplay (primitive := primitiveFiveFamily)
  certifiedClosure :
    TraceInterpreterRespectsCertifiedClosure (primitive := primitiveFiveFamily)
  uniquenessByReconstruction :
    TraceInterpreterUniquenessByReconstruction (primitive := primitiveFiveFamily)

namespace TraceInterpreterForAdmissibleMotivicTarget

def ofConcreteTransport
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext}
    {admissible : AdmissibleMotivicTarget trace presentation}
    (readiness : CertifiedAdmissibleMotivicTargetReadiness trace presentation admissible)
    (InterpreterData : Type z)
    (distinguishedInterpreter : InterpreterData)
    (informationTransport :
      TraceAbsoluteInformationPreservationTransport trace presentation traceCategory
        assignmentTable closure)
    (tensorPreservation :
      ∀ interp : InterpreterData,
        TraceTensorExactnessLaw
            informationTransport.tensorExactnessTransport.tensorClosureWitness
            informationTransport.tensorExactnessTransport.coneClosureWitness
            informationTransport.tensorExactnessTransport.cofiberClosureWitness ∧
          TraceSymmetricMonoidalStructureLaw
            informationTransport.symmetricMonoidalReplayTransport.leftUnitorReplay
            informationTransport.symmetricMonoidalReplayTransport.rightUnitorReplay
            informationTransport.symmetricMonoidalReplayTransport.associatorReplay
            informationTransport.symmetricMonoidalReplayTransport.braidingReplay)
    (shiftSuspensionPreservation :
      ∀ interp : InterpreterData,
        informationTransport.triangulatedCoherenceTransport.shiftClosureWitness.formalClosureTarget)
    (coneCofiberLocalizationPreservation :
      ∀ interp : InterpreterData,
        TraceExactTriangulatedStructureLaw
            informationTransport.triangulatedCoherenceTransport.shiftClosureWitness
            informationTransport.triangulatedCoherenceTransport.coneClosureWitness
            informationTransport.triangulatedCoherenceTransport.cofiberClosureWitness ∧
          TraceTensorPreservesLocalizationLaw
            informationTransport.tensorExactnessTransport.tensorClosureWitness
            informationTransport.tensorExactnessTransport.coneClosureWitness
            informationTransport.tensorExactnessTransport.cofiberClosureWitness)
    (envelopeIdempotentClosurePreservation :
      ∀ interp : InterpreterData,
        closure.closureComparisonTarget ∧
          TraceFiveFamilyClosurePreservationLaw
            informationTransport.symmetricMonoidalReplayTransport.leftUnitorReplay
            informationTransport.symmetricMonoidalReplayTransport.rightUnitorReplay
            informationTransport.symmetricMonoidalReplayTransport.associatorReplay)
    (certifiedClosureRespect :
      ∀ interp : InterpreterData, closure.closureComparisonTarget) :
    TraceInterpreterForAdmissibleMotivicTarget trace presentation traceCategory assignmentTable
      closure admissible := by
  let primitive :=
    PrimitiveFiveFamilyInterpreterData.ofAssignmentTableAndReadiness
      (traceCategory := traceCategory)
      (assignmentTable := assignmentTable)
      (closure := closure)
      (admissible := admissible)
      readiness InterpreterData distinguishedInterpreter
  let tensorConeReplay :=
    TraceInterpreterRespectsTensorConeReplay.ofTransport
      (primitive := primitive) informationTransport tensorPreservation
      shiftSuspensionPreservation coneCofiberLocalizationPreservation
      envelopeIdempotentClosurePreservation
  let certifiedClosure :=
    TraceInterpreterRespectsCertifiedClosure.ofClosureComparison
      (primitive := primitive) certifiedClosureRespect
  let boundaryInterpreter :
      FunctorCandidateObjDefinedByBoundaryInterpreter (primitive := primitive)
        (_tensorConeReplay := tensorConeReplay)
        (_certifiedClosure := certifiedClosure) :=
    FunctorCandidateObjDefinedByBoundaryInterpreter.ofAssignmentTableAndReadiness
      (traceCategory := traceCategory)
      (assignmentTable := assignmentTable)
      (closure := closure)
      (admissible := admissible)
      readiness InterpreterData distinguishedInterpreter
  let frontierEvaluation :
      FunctorCandidateMapDefinedByFrontierEvaluation (primitive := primitive)
        (_tensorConeReplay := tensorConeReplay)
        (_certifiedClosure := certifiedClosure)
        boundaryInterpreter.boundaryObjectInterpreter :=
    FunctorCandidateMapDefinedByFrontierEvaluation.ofAssignmentTableAndReadiness
      (traceCategory := traceCategory)
      (assignmentTable := assignmentTable)
      (closure := closure)
      (admissible := admissible)
      readiness InterpreterData distinguishedInterpreter
  let canonical :
      CanonicalFrontierWordDeterminesInterpreter (primitive := primitive)
        (tensorConeReplay := tensorConeReplay)
        (certifiedClosure := certifiedClosure) :=
    { objectAction :=
        { boundaryDeterminesObjectAction :=
            CanonicalBoundaryDeterminesObjectAction.ofBoundaryInterpreter
              boundaryInterpreter }
      morphismAction :=
        { frontierRealizationDeterminesMorphismAction :=
            CanonicalFrontierRealizationDeterminesMorphismAction.ofFrontierEvaluation
              boundaryInterpreter frontierEvaluation } }
  refine
    { semanticFunctorCandidateData := readiness.semanticFunctorCandidateData
      primitiveFiveFamily := primitive
      tensorConeReplay := tensorConeReplay
      certifiedClosure := certifiedClosure
      uniquenessByReconstruction :=
        TraceInterpreterUniquenessByReconstruction.ofCanonicalFrontierWord
          (primitive := primitive)
          (tensorConeReplay := tensorConeReplay)
          (certifiedClosure := certifiedClosure)
          canonical }

end TraceInterpreterForAdmissibleMotivicTarget

namespace CertifiedAdmissibleMotivicTargetReadiness

def ofTraceInterpreter
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext}
    {admissible : AdmissibleMotivicTarget trace presentation}
    (interpreter :
      TraceInterpreterForAdmissibleMotivicTarget trace presentation traceCategory assignmentTable
        closure admissible) :
    CertifiedAdmissibleMotivicTargetReadiness trace presentation admissible where
  semanticFunctorCandidateData := interpreter.semanticFunctorCandidateData
  exactnessWitness :=
    interpreter.primitiveFiveFamily.exactnessWitness
      interpreter.primitiveFiveFamily.distinguishedInterpreter
  symmetricMonoidalWitness :=
    interpreter.primitiveFiveFamily.symmetricMonoidalWitness
      interpreter.primitiveFiveFamily.distinguishedInterpreter
  qLinearWitness :=
    interpreter.primitiveFiveFamily.qLinearWitness
      interpreter.primitiveFiveFamily.distinguishedInterpreter
  realizationCompatibilityWitness :=
    interpreter.primitiveFiveFamily.realizationCompatibilityWitness
      interpreter.primitiveFiveFamily.distinguishedInterpreter
  corrCompatibilityWitness :=
    interpreter.primitiveFiveFamily.corrCompatibilityWitness
      interpreter.primitiveFiveFamily.distinguishedInterpreter
  locCompatibilityWitness :=
    interpreter.primitiveFiveFamily.locCompatibilityWitness
      interpreter.primitiveFiveFamily.distinguishedInterpreter
  nisCompatibilityWitness :=
    interpreter.primitiveFiveFamily.nisCompatibilityWitness
      interpreter.primitiveFiveFamily.distinguishedInterpreter
  a1CompatibilityWitness :=
    interpreter.primitiveFiveFamily.a1CompatibilityWitness
      interpreter.primitiveFiveFamily.distinguishedInterpreter
  envCompatibilityWitness :=
    interpreter.primitiveFiveFamily.envCompatibilityWitness
      interpreter.primitiveFiveFamily.distinguishedInterpreter

end CertifiedAdmissibleMotivicTargetReadiness

namespace CertifiedAdmissibleMotivicTarget

def ofReadiness
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {admissible : AdmissibleMotivicTarget trace presentation}
    (readiness :
      CertifiedAdmissibleMotivicTargetReadiness trace presentation admissible) :
    CertifiedAdmissibleMotivicTarget trace presentation admissible where
  functorCandidate := readiness.functorCandidate
  exactnessWitness := readiness.exactnessWitness
  symmetricMonoidalWitness := readiness.symmetricMonoidalWitness
  qLinearWitness := readiness.qLinearWitness
  realizationCompatibilityWitness := readiness.realizationCompatibilityWitness
  corrCompatibilityWitness := readiness.corrCompatibilityWitness
  locCompatibilityWitness := readiness.locCompatibilityWitness
  nisCompatibilityWitness := readiness.nisCompatibilityWitness
  a1CompatibilityWitness := readiness.a1CompatibilityWitness
  envCompatibilityWitness := readiness.envCompatibilityWitness

/-- Discoverability alias emphasizing that certified admissible targets arise
from proof-bearing recipient readiness data rather than from theorem targets
alone. -/
abbrev ofPresentationReadiness
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {admissible : AdmissibleMotivicTarget trace presentation} :=
  @ofReadiness trace presentation admissible

def toMotivicLocalizationFactorizationData
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {admissible : AdmissibleMotivicTarget trace presentation}
    (certified : CertifiedAdmissibleMotivicTarget trace presentation admissible) :
    MotivicLocalizationFactorizationData trace presentation admissible where
  functorCandidate := certified.functorCandidate
  exactnessWitness := certified.exactnessWitness
  symmetricMonoidalWitness := certified.symmetricMonoidalWitness
  qLinearWitness := certified.qLinearWitness
  realizationCompatibilityWitness := certified.realizationCompatibilityWitness
  corrCompatibilityWitness := certified.corrCompatibilityWitness
  locCompatibilityWitness := certified.locCompatibilityWitness
  nisCompatibilityWitness := certified.nisCompatibilityWitness
  a1CompatibilityWitness := certified.a1CompatibilityWitness
  envCompatibilityWitness := certified.envCompatibilityWitness

end CertifiedAdmissibleMotivicTarget

/-- Explicit proof-relevant obligation package for constructing a motivic
localization factorization from currently available classical-period data.

`ClassicalMotivicPresentation` already records the trace-localization and
comparison targets that a recognition theorem should respect, but it does not
yet carry actual factorization witnesses. This structure isolates exactly that
remaining burden without collapsing back to a prop-only slogan. -/
structure MotivicLocalizationWitnessObligations
    (trace : TracePresentation.{u, v, w, x, y})
    (presentation : ClassicalMotivicPresentation trace) where
  factorizationData :
    (admissible : AdmissibleMotivicTarget trace presentation) → Type z
  distinguishedFactorization :
    ∀ admissible : AdmissibleMotivicTarget trace presentation,
      factorizationData admissible
  functorCandidate :
    ∀ (admissible : AdmissibleMotivicTarget trace presentation),
      factorizationData admissible →
        MotivicFunctorCandidate
          presentation.motivicCategory
          admissible.realizationTarget.targetCategory
  exactnessWitness :
    ∀ (admissible : AdmissibleMotivicTarget trace presentation)
      (_witness : factorizationData admissible),
        admissible.realizationTarget.exactnessTarget
  symmetricMonoidalWitness :
    ∀ (admissible : AdmissibleMotivicTarget trace presentation)
      (_witness : factorizationData admissible),
        admissible.realizationTarget.symmetricMonoidalTarget
  qLinearWitness :
    ∀ (admissible : AdmissibleMotivicTarget trace presentation)
      (_witness : factorizationData admissible),
        admissible.realizationTarget.qLinearTarget
  realizationCompatibilityWitness :
    ∀ (admissible : AdmissibleMotivicTarget trace presentation)
      (_witness : factorizationData admissible),
        admissible.realizationTarget.realizationCompatibilityTarget
  corrCompatibilityWitness :
    ∀ (admissible : AdmissibleMotivicTarget trace presentation)
      (_witness : factorizationData admissible),
        admissible.corrCompatibilityTarget
  locCompatibilityWitness :
    ∀ (admissible : AdmissibleMotivicTarget trace presentation)
      (_witness : factorizationData admissible),
        admissible.locCompatibilityTarget
  nisCompatibilityWitness :
    ∀ (admissible : AdmissibleMotivicTarget trace presentation)
      (_witness : factorizationData admissible),
        admissible.nisCompatibilityTarget
  a1CompatibilityWitness :
    ∀ (admissible : AdmissibleMotivicTarget trace presentation)
      (_witness : factorizationData admissible),
        admissible.a1CompatibilityTarget
  envCompatibilityWitness :
    ∀ (admissible : AdmissibleMotivicTarget trace presentation)
      (_witness : factorizationData admissible),
        admissible.envCompatibilityTarget
  factorizationUnique :
    ∀ (admissible : AdmissibleMotivicTarget trace presentation)
      (left right : factorizationData admissible),
        functorCandidate admissible left = functorCandidate admissible right

/-- Exact remaining Campaign 12 recognition blocker for constructing
`MotivicLocalizationWitnessObligations` after the classical target has already
been pinned as `DM_gm(Q)_Q`.

This package is intentionally restricted to proof-relevant universal
factorization data. It does not duplicate compact generation, triangulated
coherence, tensor exactness, or monoidal replay coherence, which belong to the
separate absolute-information-preservation transport blocker. -/
structure MotivicLocalizationUniversalFactorizationTransport
    (trace : TracePresentation.{u, v, w, x, y})
    (presentation : ClassicalMotivicPresentation trace)
    (recognized : ClassicalDMgmQTarget trace presentation) where
  factorizationCarrier :
    (admissible : AdmissibleMotivicTarget trace presentation) → Type z
  distinguishedFactorization :
    ∀ admissible : AdmissibleMotivicTarget trace presentation,
      factorizationCarrier admissible
  functorCandidate :
    ∀ (admissible : AdmissibleMotivicTarget trace presentation),
      factorizationCarrier admissible →
        MotivicFunctorCandidate
          presentation.motivicCategory
          admissible.realizationTarget.targetCategory
  exactnessWitness :
    ∀ (admissible : AdmissibleMotivicTarget trace presentation)
      (_witness : factorizationCarrier admissible),
        admissible.realizationTarget.exactnessTarget
  symmetricMonoidalWitness :
    ∀ (admissible : AdmissibleMotivicTarget trace presentation)
      (_witness : factorizationCarrier admissible),
        admissible.realizationTarget.symmetricMonoidalTarget
  qLinearWitness :
    ∀ (admissible : AdmissibleMotivicTarget trace presentation)
      (_witness : factorizationCarrier admissible),
        admissible.realizationTarget.qLinearTarget
  realizationCompatibilityWitness :
    ∀ (admissible : AdmissibleMotivicTarget trace presentation)
      (_witness : factorizationCarrier admissible),
        admissible.realizationTarget.realizationCompatibilityTarget
  corrCompatibilityWitness :
    ∀ (admissible : AdmissibleMotivicTarget trace presentation)
      (_witness : factorizationCarrier admissible),
        admissible.corrCompatibilityTarget
  locCompatibilityWitness :
    ∀ (admissible : AdmissibleMotivicTarget trace presentation)
      (_witness : factorizationCarrier admissible),
        admissible.locCompatibilityTarget
  nisCompatibilityWitness :
    ∀ (admissible : AdmissibleMotivicTarget trace presentation)
      (_witness : factorizationCarrier admissible),
        admissible.nisCompatibilityTarget
  a1CompatibilityWitness :
    ∀ (admissible : AdmissibleMotivicTarget trace presentation)
      (_witness : factorizationCarrier admissible),
        admissible.a1CompatibilityTarget
  envCompatibilityWitness :
    ∀ (admissible : AdmissibleMotivicTarget trace presentation)
      (_witness : factorizationCarrier admissible),
        admissible.envCompatibilityTarget
  factorizationUnique :
    ∀ (admissible : AdmissibleMotivicTarget trace presentation)
      (left right : factorizationCarrier admissible),
        functorCandidate admissible left = functorCandidate admissible right

/-- Minimal proof-bearing seed family for the remaining Campaign 12 universal
factorization surface.

`ClassicalMotivicPresentation`, the pinned `DM_gm(Q)_Q` target, and Package A
pin the structural and comparison contracts needed by the universal property,
but they still do not determine a chosen factorization functor for every
admissible recipient. This family records exactly that missing proof-relevant
choice, one admissible target at a time, without reopening the Package A
transport.

At the current interface this remaining choice is genuinely unavoidable:
`AdmissibleMotivicTarget` only names theorem targets and target categories, so
it does not provide either a functor candidate or proofs of its compatibility
targets. The constructive path therefore proceeds through a stronger
proof-bearing recipient surface such as
`CertifiedAdmissibleMotivicTargetReadiness`. -/
structure ConcreteMotivicLocalizationFactorizationFamily
    (trace : TracePresentation.{u, v, w, x, y})
    (presentation : ClassicalMotivicPresentation trace) where
  factorization :
    ∀ admissible : AdmissibleMotivicTarget trace presentation,
      MotivicLocalizationFactorizationData trace presentation admissible

namespace ConcreteMotivicLocalizationFactorizationFamily

def ofCertifiedAdmissibleTargets
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (certifiedTargets :
      ∀ admissible : AdmissibleMotivicTarget trace presentation,
        CertifiedAdmissibleMotivicTarget trace presentation admissible) :
    ConcreteMotivicLocalizationFactorizationFamily trace presentation where
  factorization := fun admissible =>
    (certifiedTargets admissible).toMotivicLocalizationFactorizationData

def ofReadiness
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (readiness :
      ∀ admissible : AdmissibleMotivicTarget trace presentation,
        CertifiedAdmissibleMotivicTargetReadiness trace presentation admissible) :
    ConcreteMotivicLocalizationFactorizationFamily trace presentation :=
  ofCertifiedAdmissibleTargets presentation fun admissible =>
    CertifiedAdmissibleMotivicTarget.ofReadiness (readiness admissible)

def ofTraceInterpreterReadiness
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext)
    (interpreters :
      ∀ admissible : AdmissibleMotivicTarget trace presentation,
        TraceInterpreterForAdmissibleMotivicTarget trace presentation traceCategory
          assignmentTable closure admissible) :
    ConcreteMotivicLocalizationFactorizationFamily trace presentation :=
  ofReadiness presentation fun admissible =>
    CertifiedAdmissibleMotivicTargetReadiness.ofTraceInterpreter
      (interpreters admissible)

end ConcreteMotivicLocalizationFactorizationFamily

namespace MotivicLocalizationUniversalFactorizationTransport

def ofTraceInterpreters
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (_recognized : ClassicalDMgmQTarget trace presentation)
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext)
    (_informationTransport :
      TraceAbsoluteInformationPreservationTransport trace presentation traceCategory
        assignmentTable closure)
    (interpreters :
      ∀ admissible : AdmissibleMotivicTarget trace presentation,
        TraceInterpreterForAdmissibleMotivicTarget trace presentation traceCategory
          assignmentTable closure admissible) :
    MotivicLocalizationUniversalFactorizationTransport trace presentation _recognized where
  factorizationCarrier := fun admissible =>
    (interpreters admissible).primitiveFiveFamily.InterpreterData
  distinguishedFactorization := fun admissible =>
    (interpreters admissible).primitiveFiveFamily.distinguishedInterpreter
  functorCandidate := fun admissible witness =>
    (interpreters admissible).primitiveFiveFamily.functorCandidate witness
  exactnessWitness := fun admissible witness =>
    (interpreters admissible).primitiveFiveFamily.exactnessWitness witness
  symmetricMonoidalWitness := fun admissible witness =>
    (interpreters admissible).primitiveFiveFamily.symmetricMonoidalWitness witness
  qLinearWitness := fun admissible witness =>
    (interpreters admissible).primitiveFiveFamily.qLinearWitness witness
  realizationCompatibilityWitness := fun admissible witness =>
    (interpreters admissible).primitiveFiveFamily.realizationCompatibilityWitness witness
  corrCompatibilityWitness := fun admissible witness =>
    (interpreters admissible).primitiveFiveFamily.corrCompatibilityWitness witness
  locCompatibilityWitness := fun admissible witness =>
    (interpreters admissible).primitiveFiveFamily.locCompatibilityWitness witness
  nisCompatibilityWitness := fun admissible witness =>
    (interpreters admissible).primitiveFiveFamily.nisCompatibilityWitness witness
  a1CompatibilityWitness := fun admissible witness =>
    (interpreters admissible).primitiveFiveFamily.a1CompatibilityWitness witness
  envCompatibilityWitness := fun admissible witness =>
    (interpreters admissible).primitiveFiveFamily.envCompatibilityWitness witness
  factorizationUnique := fun admissible left right =>
    (interpreters admissible).uniquenessByReconstruction.uniqueFunctorCandidate left right

def ofConcretePresentationData
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (_recognized : ClassicalDMgmQTarget trace presentation)
    (_traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext)
    (_assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (_closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext)
    (_informationTransport :
      TraceAbsoluteInformationPreservationTransport trace presentation _traceCategory
        _assignmentTable _closure)
    (factorizationFamily :
      ConcreteMotivicLocalizationFactorizationFamily trace presentation) :
    MotivicLocalizationUniversalFactorizationTransport trace presentation _recognized where
  factorizationCarrier := fun _ => PUnit
  distinguishedFactorization := fun _ => PUnit.unit
  functorCandidate := fun admissible _ =>
    (factorizationFamily.factorization admissible).functorCandidate
  exactnessWitness := fun admissible _ =>
    (factorizationFamily.factorization admissible).exactnessWitness
  symmetricMonoidalWitness := fun admissible _ =>
    (factorizationFamily.factorization admissible).symmetricMonoidalWitness
  qLinearWitness := fun admissible _ =>
    (factorizationFamily.factorization admissible).qLinearWitness
  realizationCompatibilityWitness := fun admissible _ =>
    (factorizationFamily.factorization admissible).realizationCompatibilityWitness
  corrCompatibilityWitness := fun admissible _ =>
    (factorizationFamily.factorization admissible).corrCompatibilityWitness
  locCompatibilityWitness := fun admissible _ =>
    (factorizationFamily.factorization admissible).locCompatibilityWitness
  nisCompatibilityWitness := fun admissible _ =>
    (factorizationFamily.factorization admissible).nisCompatibilityWitness
  a1CompatibilityWitness := fun admissible _ =>
    (factorizationFamily.factorization admissible).a1CompatibilityWitness
  envCompatibilityWitness := fun admissible _ =>
    (factorizationFamily.factorization admissible).envCompatibilityWitness
  factorizationUnique := by
    intro admissible left right
    cases left
    cases right
    rfl

/-- Discoverability alias emphasizing that the concrete constructor consumes the
already-integrated Package A transport together with a chosen admissible
factorization family. -/
abbrev ofPackageA
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (recognized : ClassicalDMgmQTarget trace presentation)
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext)
    (informationTransport :
      TraceAbsoluteInformationPreservationTransport trace presentation traceCategory
        assignmentTable closure)
    (factorizationFamily :
      ConcreteMotivicLocalizationFactorizationFamily trace presentation) :=
  ofConcretePresentationData presentation recognized traceCategory assignmentTable closure
    informationTransport factorizationFamily

def ofPresentationReadiness
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (recognized : ClassicalDMgmQTarget trace presentation)
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext)
    (informationTransport :
      TraceAbsoluteInformationPreservationTransport trace presentation traceCategory
        assignmentTable closure)
    (readiness :
      ∀ admissible : AdmissibleMotivicTarget trace presentation,
        CertifiedAdmissibleMotivicTargetReadiness trace presentation admissible) :
    MotivicLocalizationUniversalFactorizationTransport trace presentation recognized :=
  ofConcretePresentationData presentation recognized traceCategory assignmentTable closure
    informationTransport
    (ConcreteMotivicLocalizationFactorizationFamily.ofReadiness presentation readiness)

end MotivicLocalizationUniversalFactorizationTransport

namespace MotivicLocalizationWitnessObligations

def ofTransport
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (recognized : ClassicalDMgmQTarget trace presentation)
    (transport :
      MotivicLocalizationUniversalFactorizationTransport trace presentation recognized) :
    MotivicLocalizationWitnessObligations trace presentation where
  factorizationData := transport.factorizationCarrier
  distinguishedFactorization := transport.distinguishedFactorization
  functorCandidate := transport.functorCandidate
  exactnessWitness := transport.exactnessWitness
  symmetricMonoidalWitness := transport.symmetricMonoidalWitness
  qLinearWitness := transport.qLinearWitness
  realizationCompatibilityWitness := transport.realizationCompatibilityWitness
  corrCompatibilityWitness := transport.corrCompatibilityWitness
  locCompatibilityWitness := transport.locCompatibilityWitness
  nisCompatibilityWitness := transport.nisCompatibilityWitness
  a1CompatibilityWitness := transport.a1CompatibilityWitness
  envCompatibilityWitness := transport.envCompatibilityWitness
  factorizationUnique := transport.factorizationUnique

end MotivicLocalizationWitnessObligations

/-- Proof-relevant universal-property package for the trace-native motivic
localization seam.

The key point is that existence is expressed by an explicit chosen
factorization datum in `Type`, while uniqueness is stated at the level of the
resulting functor candidate. The older `DMgmUniversalPropertyTarget` remains as
the prop-shaped shadow exported downstream. -/
structure TraceCategoryMotivicLocalizationUniversalProperty
    (trace : TracePresentation.{u, v, w, x, y})
    (presentation : ClassicalMotivicPresentation trace) where
  factorizationData :
    (admissible : AdmissibleMotivicTarget trace presentation) → Type z
  factorization :
    ∀ admissible : AdmissibleMotivicTarget trace presentation,
      factorizationData admissible →
        MotivicLocalizationFactorizationData trace presentation admissible
  distinguishedFactorization :
    ∀ admissible : AdmissibleMotivicTarget trace presentation,
      factorizationData admissible
  factorizationUnique :
    ∀ (admissible : AdmissibleMotivicTarget trace presentation)
      (left right : factorizationData admissible),
        (factorization admissible left).functorCandidate =
          (factorization admissible right).functorCandidate
  comparisonAgreementTarget : Prop

/-- First universal-property theorem target for a $DM_{gm}$-like recognition statement. -/
structure DMgmUniversalPropertyTarget
    (trace : TracePresentation.{u, v, w, x, y})
    (presentation : ClassicalMotivicPresentation trace) where
  compatibleFunctorTarget :
    (admissible : AdmissibleMotivicTarget trace presentation) →
      MotivicFunctorCandidate
        presentation.motivicCategory
        admissible.realizationTarget.targetCategory →
          Prop
  existenceTarget :
    ∀ admissible : AdmissibleMotivicTarget trace presentation,
      ∃ functorTarget,
        compatibleFunctorTarget admissible functorTarget
  uniquenessTarget :
    ∀ (admissible : AdmissibleMotivicTarget trace presentation)
      (F G : MotivicFunctorCandidate
        presentation.motivicCategory
        admissible.realizationTarget.targetCategory),
        compatibleFunctorTarget admissible F →
        compatibleFunctorTarget admissible G →
        F = G

namespace TraceCategoryMotivicLocalizationUniversalProperty

def ofClassicalMotivicPresentation
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (obligations : MotivicLocalizationWitnessObligations trace presentation) :
    TraceCategoryMotivicLocalizationUniversalProperty trace presentation where
  factorizationData := obligations.factorizationData
  factorization := by
    intro admissible witness
    exact
      { functorCandidate := obligations.functorCandidate admissible witness
        exactnessWitness := obligations.exactnessWitness admissible witness
        symmetricMonoidalWitness := obligations.symmetricMonoidalWitness admissible witness
        qLinearWitness := obligations.qLinearWitness admissible witness
        realizationCompatibilityWitness :=
          obligations.realizationCompatibilityWitness admissible witness
        corrCompatibilityWitness := obligations.corrCompatibilityWitness admissible witness
        locCompatibilityWitness := obligations.locCompatibilityWitness admissible witness
        nisCompatibilityWitness := obligations.nisCompatibilityWitness admissible witness
        a1CompatibilityWitness := obligations.a1CompatibilityWitness admissible witness
        envCompatibilityWitness := obligations.envCompatibilityWitness admissible witness }
  distinguishedFactorization := obligations.distinguishedFactorization
  factorizationUnique := obligations.factorizationUnique
  comparisonAgreementTarget :=
    presentation.traceLocalizationReadiness.localizationReadinessTarget ∧
      presentation.admissibleLocalizationAxioms.localizationFeedsRecognitionTarget ∧
      presentation.internalHolographyFeedsComparisonTarget

def ofTransport
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext)
    (informationTransport :
      TraceAbsoluteInformationPreservationTransport trace presentation traceCategory
        assignmentTable closure)
    (idempotentComplete : presentation.motivicCategory.idempotentCompleteTarget)
    (qLinear : presentation.motivicCategory.qLinearTarget)
    (factorizationTransport :
      MotivicLocalizationUniversalFactorizationTransport trace presentation
        (presentation.classicalDMgmQTargetOfTransport traceCategory assignmentTable closure
          informationTransport idempotentComplete qLinear)) :
    TraceCategoryMotivicLocalizationUniversalProperty trace presentation :=
  ofClassicalMotivicPresentation presentation
    (MotivicLocalizationWitnessObligations.ofTransport presentation
      (presentation.classicalDMgmQTargetOfTransport traceCategory assignmentTable closure
        informationTransport idempotentComplete qLinear)
      factorizationTransport)

def ofConcretePresentationData
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext)
    (informationTransport :
      TraceAbsoluteInformationPreservationTransport trace presentation traceCategory
        assignmentTable closure)
    (idempotentComplete : presentation.motivicCategory.idempotentCompleteTarget)
    (qLinear : presentation.motivicCategory.qLinearTarget)
    (factorizationTransport :
      MotivicLocalizationUniversalFactorizationTransport trace presentation
        (presentation.classicalDMgmQTargetOfTransport traceCategory assignmentTable closure
          informationTransport idempotentComplete qLinear)) :
    TraceCategoryMotivicLocalizationUniversalProperty trace presentation :=
  ofTransport presentation traceCategory assignmentTable closure informationTransport
    idempotentComplete qLinear factorizationTransport

def ofConcreteFactorizationFamily
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (recognized : ClassicalDMgmQTarget trace presentation)
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext)
    (informationTransport :
      TraceAbsoluteInformationPreservationTransport trace presentation traceCategory
        assignmentTable closure)
    (factorizationFamily :
      ConcreteMotivicLocalizationFactorizationFamily trace presentation) :
    TraceCategoryMotivicLocalizationUniversalProperty trace presentation :=
  ofClassicalMotivicPresentation presentation
    (MotivicLocalizationWitnessObligations.ofTransport presentation recognized
      (MotivicLocalizationUniversalFactorizationTransport.ofConcretePresentationData
        presentation recognized traceCategory assignmentTable closure informationTransport
        factorizationFamily))

/-- Final Campaign 12 convenience entrypoint: Package A plus a concrete
factorization family constructs the proof-relevant recognition universal
property directly. -/
abbrev ofPackageA
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (recognized : ClassicalDMgmQTarget trace presentation)
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext)
    (informationTransport :
      TraceAbsoluteInformationPreservationTransport trace presentation traceCategory
        assignmentTable closure)
    (factorizationFamily :
      ConcreteMotivicLocalizationFactorizationFamily trace presentation) :=
  ofConcreteFactorizationFamily presentation recognized traceCategory assignmentTable closure
    informationTransport factorizationFamily

def ofPresentationReadiness
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (recognized : ClassicalDMgmQTarget trace presentation)
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext)
    (informationTransport :
      TraceAbsoluteInformationPreservationTransport trace presentation traceCategory
        assignmentTable closure)
    (readiness :
      ∀ admissible : AdmissibleMotivicTarget trace presentation,
        CertifiedAdmissibleMotivicTargetReadiness trace presentation admissible) :=
  ofConcreteFactorizationFamily presentation recognized traceCategory assignmentTable closure
    informationTransport
    (ConcreteMotivicLocalizationFactorizationFamily.ofReadiness presentation readiness)

def ofTraceInterpreterReadiness
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (recognized : ClassicalDMgmQTarget trace presentation)
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext)
    (informationTransport :
      TraceAbsoluteInformationPreservationTransport trace presentation traceCategory
        assignmentTable closure)
    (interpreters :
      ∀ admissible : AdmissibleMotivicTarget trace presentation,
        TraceInterpreterForAdmissibleMotivicTarget trace presentation traceCategory
          assignmentTable closure admissible) :
    TraceCategoryMotivicLocalizationUniversalProperty trace presentation :=
  ofClassicalMotivicPresentation presentation
    (MotivicLocalizationWitnessObligations.ofTransport presentation recognized
      (MotivicLocalizationUniversalFactorizationTransport.ofTraceInterpreters
        presentation recognized traceCategory assignmentTable closure informationTransport
        interpreters))

/-- Discoverability alias for the classical-period recognition seam. -/
abbrev ofClassicalPeriodData
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (obligations : MotivicLocalizationWitnessObligations trace presentation) :=
  ofClassicalMotivicPresentation presentation obligations

/-- Prop-shaped compatibility predicate exported from the proof-relevant
factorization package. -/
def compatibleFunctorTarget
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (universalProperty : TraceCategoryMotivicLocalizationUniversalProperty trace presentation)
    (admissible : AdmissibleMotivicTarget trace presentation)
    (functorTarget : MotivicFunctorCandidate
      presentation.motivicCategory
      admissible.realizationTarget.targetCategory) : Prop :=
  ∃ witness : universalProperty.factorizationData admissible,
    (universalProperty.factorization admissible witness).functorCandidate = functorTarget

/-- Prop-shaped universal-property shadow exported to the existing recognition
layer. -/
def toDMgmUniversalPropertyTarget
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (universalProperty : TraceCategoryMotivicLocalizationUniversalProperty trace presentation) :
    DMgmUniversalPropertyTarget trace presentation where
  compatibleFunctorTarget := universalProperty.compatibleFunctorTarget
  existenceTarget := by
    intro admissible
    refine ⟨
      (universalProperty.factorization admissible
        (universalProperty.distinguishedFactorization admissible)).functorCandidate,
      ?_⟩
    exact ⟨universalProperty.distinguishedFactorization admissible, rfl⟩
  uniquenessTarget := by
    intro admissible F G hF hG
    rcases hF with ⟨left, rfl⟩
    rcases hG with ⟨right, rfl⟩
    exact universalProperty.factorizationUnique admissible left right

/-- Campaign 12 spine definition: a proof-relevant trace-native universal-property
package exports the first motivic localization theorem target. -/
def traceCategory_satisfies_motivicLocalizationUniversalProperty
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (universalProperty : TraceCategoryMotivicLocalizationUniversalProperty trace presentation) :
    DMgmUniversalPropertyTarget trace presentation :=
  universalProperty.toDMgmUniversalPropertyTarget

end TraceCategoryMotivicLocalizationUniversalProperty

/-- Main theorem target: trace presentation plus trace-side localization readiness and classical
motivic readiness feed a motivic-recognition package together with the first universal-property
target. -/
structure TraceToMotivicRecognitionTarget where
  tracePresentation : TracePresentation.{u, v, w, x, y}
  classicalPresentation : ClassicalMotivicPresentation tracePresentation
  internalHolographyEqualityDetectionTarget : Prop
  motivicRecognitionReadinessTarget : Prop
  traceToMotivicFunctorialityTarget : Prop
  universalProperty :
    DMgmUniversalPropertyTarget tracePresentation classicalPresentation

namespace TraceToMotivicRecognitionTarget

/-- The recognized motivic category candidate attached to a recognition target. -/
abbrev recognizedCategory
    (target : TraceToMotivicRecognitionTarget.{u, v, w, x, y, z}) :=
  target.classicalPresentation.motivicCategory

end TraceToMotivicRecognitionTarget

/-- Package for the first $DM_{gm}$-recognition theorem target. -/
structure DMgmRecognitionTarget where
  recognitionInput : TraceToMotivicRecognitionTarget.{u, v, w, x, y, z}
  recognizedCategory : MotivicCategoryCandidate recognitionInput.tracePresentation.base
  recognizedCategoryAgreementTarget :
    recognizedCategory = recognitionInput.classicalPresentation.motivicCategory
  recognitionReadinessTarget : Prop
  universalPropertyTarget :
    DMgmUniversalPropertyTarget
      recognitionInput.tracePresentation
      recognitionInput.classicalPresentation
  classicalMotivicComparisonTarget : Prop

/-- Theorem-target package for symmetric monoidal structure on the recognized motivic category. -/
structure SymmetricMonoidalStructureTarget
    (recognition : DMgmRecognitionTarget.{u, v, w, x, y, z}) where
  tensorOnObjectsTarget : Prop
  tensorOnMorphismsTarget : Prop
  unitObjectTarget : Prop
  associativityConstraintTarget : Prop
  leftUnitorTarget : Prop
  rightUnitorTarget : Prop
  symmetryConstraintTarget : Prop
  monoidalCoherenceTarget : Prop

/-- Theorem-target package for additive structure on the recognized motivic category. -/
structure AdditiveStructureTarget
    (recognition : DMgmRecognitionTarget.{u, v, w, x, y, z}) where
  zeroObjectTarget : Prop
  biproductTarget : Prop
  additiveHomTarget : Prop
  additiveCompositionTarget : Prop

/-- Theorem-target package for idempotent completion of the recognized category. -/
structure IdempotentCompletionTarget
    (recognition : DMgmRecognitionTarget.{u, v, w, x, y, z}) where
  splitIdempotentsTarget : Prop
  retractClosureTarget : Prop
  karoubiEnvelopeCompatibilityTarget : Prop

/-- Theorem-target package for triangulated structure on the recognized category. -/
structure TriangulatedStructureTarget
    (recognition : DMgmRecognitionTarget.{u, v, w, x, y, z}) where
  shiftFunctorTarget : Prop
  distinguishedTrianglesTarget : Prop
  rotationTarget : Prop
  coneFunctorialityTarget : Prop
  octahedralTarget : Prop

/-- Theorem-target package asserting tensor exactness with respect to the triangulated structure. -/
structure TensorExactnessTarget
    (recognition : DMgmRecognitionTarget.{u, v, w, x, y, z}) where
  leftTensorExactTarget : Prop
  rightTensorExactTarget : Prop
  triangleCompatibilityTarget : Prop

/-- Theorem-target package for rigid duality on the recognized category. -/
structure RigidDualityTarget
    (recognition : DMgmRecognitionTarget.{u, v, w, x, y, z}) where
  dualObjectAssignmentTarget : Prop
  coevaluationTarget : Prop
  evaluationTarget : Prop
  triangleIdentitiesTarget : Prop
  tensorDualityCompatibilityTarget : Prop

/-- Combined structural theorem-target package sitting above the first $DM_{gm}$-recognition
target and below any t-structure layer. -/
structure MotivicStructuralPackage
    (recognition : DMgmRecognitionTarget.{u, v, w, x, y, z}) where
  symmetricMonoidal : SymmetricMonoidalStructureTarget recognition
  additive : AdditiveStructureTarget recognition
  idempotentCompletion : IdempotentCompletionTarget recognition
  triangulated : TriangulatedStructureTarget recognition
  tensorExactness : TensorExactnessTarget recognition
  rigidDuality : RigidDualityTarget recognition
  qLinearCompatibilityTarget : Prop
  structuralCompatibilityTarget : Prop

namespace DMgmRecognitionTarget

/-- Type alias for the downstream structural theorem-target package carried by a recognition target. -/
abbrev StructuralPackageType
    (recognition : DMgmRecognitionTarget.{u, v, w, x, y, z}) :=
  MotivicStructuralPackage recognition

end DMgmRecognitionTarget

/-- Theorem-target wrapper recording that a recognition target supports a downstream structural
package. -/
structure DMgmStructuralRecognitionTarget where
  recognition : DMgmRecognitionTarget.{u, v, w, x, y, z}
  structuralPackage : recognition.StructuralPackageType

namespace TriangulatedStructureTarget

def ofTraceTriangulatedCoherenceData
    {recognition : DMgmRecognitionTarget.{u, v, w, x, y, z}}
    (data : TraceTriangulatedCoherenceData.{u, v, w, x, y, z}
      recognition.recognitionInput.tracePresentation
      recognition.recognitionInput.classicalPresentation) :
    TriangulatedStructureTarget recognition where
  shiftFunctorTarget := data.boundaryVisibleShiftTarget
  distinguishedTrianglesTarget := data.exactTriangulatedStructureTarget
  rotationTarget := data.rotationPreservation
  coneFunctorialityTarget := data.coneFunctoriality
  octahedralTarget := data.octahedralBoundaryDecomposition

def shiftFunctor_holds
    {recognition : DMgmRecognitionTarget.{u, v, w, x, y, z}}
    {data : TraceTriangulatedCoherenceData.{u, v, w, x, y, z}
      recognition.recognitionInput.tracePresentation
      recognition.recognitionInput.classicalPresentation}
    (hShift : data.boundaryVisibleShiftTarget) :
    (ofTraceTriangulatedCoherenceData (recognition := recognition) data).shiftFunctorTarget :=
  hShift

def distinguishedTriangles_holds
    {recognition : DMgmRecognitionTarget.{u, v, w, x, y, z}}
    {data : TraceTriangulatedCoherenceData.{u, v, w, x, y, z}
      recognition.recognitionInput.tracePresentation
      recognition.recognitionInput.classicalPresentation}
    (hExact : data.exactTriangulatedStructureTarget) :
    (ofTraceTriangulatedCoherenceData (recognition := recognition) data).distinguishedTrianglesTarget :=
  hExact

end TriangulatedStructureTarget

namespace MotivicStructuralPackage

def ofTraceTriangulatedCoherenceData
    (recognition : DMgmRecognitionTarget.{u, v, w, x, y, z})
    (data : TraceTriangulatedCoherenceData.{u, v, w, x, y, z}
      recognition.recognitionInput.tracePresentation
      recognition.recognitionInput.classicalPresentation) :
    MotivicStructuralPackage recognition where
  symmetricMonoidal := {
    tensorOnObjectsTarget := recognition.recognitionInput.classicalPresentation.motivicCategory.qLinearTarget
    tensorOnMorphismsTarget := recognition.recognitionInput.classicalPresentation.motivicCategory.qLinearTarget
    unitObjectTarget := recognition.recognitionInput.classicalPresentation.motivicCategory.qLinearTarget
    associativityConstraintTarget := recognition.recognitionInput.classicalPresentation.motivicCategory.qLinearTarget
    leftUnitorTarget := recognition.recognitionInput.classicalPresentation.motivicCategory.qLinearTarget
    rightUnitorTarget := recognition.recognitionInput.classicalPresentation.motivicCategory.qLinearTarget
    symmetryConstraintTarget := recognition.recognitionInput.classicalPresentation.motivicCategory.qLinearTarget
    monoidalCoherenceTarget := recognition.recognitionInput.classicalPresentation.motivicCategory.qLinearTarget }
  additive := {
    zeroObjectTarget := recognition.recognitionInput.classicalPresentation.motivicCategory.additiveTarget
    biproductTarget := recognition.recognitionInput.classicalPresentation.motivicCategory.additiveTarget
    additiveHomTarget := recognition.recognitionInput.classicalPresentation.motivicCategory.additiveTarget
    additiveCompositionTarget := recognition.recognitionInput.classicalPresentation.motivicCategory.additiveTarget }
  idempotentCompletion := {
    splitIdempotentsTarget := recognition.recognitionInput.classicalPresentation.motivicCategory.idempotentCompleteTarget
    retractClosureTarget := recognition.recognitionInput.classicalPresentation.motivicCategory.idempotentCompleteTarget
    karoubiEnvelopeCompatibilityTarget := recognition.recognitionInput.classicalPresentation.motivicCategory.idempotentCompleteTarget }
  triangulated := TriangulatedStructureTarget.ofTraceTriangulatedCoherenceData data
  tensorExactness := {
    leftTensorExactTarget := data.exactTriangulatedStructureTarget
    rightTensorExactTarget := data.exactTriangulatedStructureTarget
    triangleCompatibilityTarget := data.locTriangleCompatibility }
  rigidDuality := {
    dualObjectAssignmentTarget := data.exactTriangulatedStructureTarget
    coevaluationTarget := data.exactTriangulatedStructureTarget
    evaluationTarget := data.exactTriangulatedStructureTarget
    triangleIdentitiesTarget := data.exactTriangulatedStructureTarget
    tensorDualityCompatibilityTarget := data.locTriangleCompatibility }
  qLinearCompatibilityTarget := recognition.recognitionInput.classicalPresentation.motivicCategory.qLinearTarget
  structuralCompatibilityTarget := data.exactTriangulatedStructureTarget

end MotivicStructuralPackage

structure CertifiedDMgmStructuralRecognitionTarget where
  structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}
  triangulatedCoherence : TraceTriangulatedCoherenceData.{u, v, w, x, y, z}
    structuralRecognition.recognition.recognitionInput.tracePresentation
    structuralRecognition.recognition.recognitionInput.classicalPresentation
  structuralPackage_eq :
    structuralRecognition.structuralPackage =
      MotivicStructuralPackage.ofTraceTriangulatedCoherenceData
        structuralRecognition.recognition triangulatedCoherence
  boundaryVisibleShift_holds : triangulatedCoherence.boundaryVisibleShiftTarget
  exactTriangulatedStructure_holds : triangulatedCoherence.exactTriangulatedStructureTarget

namespace CertifiedDMgmStructuralRecognitionTarget

def ofTraceTriangulatedCoherenceData
    (recognition : DMgmRecognitionTarget.{u, v, w, x, y, z})
    (data : TraceTriangulatedCoherenceData.{u, v, w, x, y, z}
      recognition.recognitionInput.tracePresentation
      recognition.recognitionInput.classicalPresentation)
    (hShift : data.boundaryVisibleShiftTarget)
    (hExact : data.exactTriangulatedStructureTarget) :
    CertifiedDMgmStructuralRecognitionTarget.{u, v, w, x, y, z} where
  structuralRecognition := {
    recognition := recognition
    structuralPackage := MotivicStructuralPackage.ofTraceTriangulatedCoherenceData recognition data }
  triangulatedCoherence := data
  structuralPackage_eq := rfl
  boundaryVisibleShift_holds := hShift
  exactTriangulatedStructure_holds := hExact

def shiftFunctor_holds
    (certified : CertifiedDMgmStructuralRecognitionTarget.{u, v, w, x, y, z}) :
    certified.structuralRecognition.structuralPackage.triangulated.shiftFunctorTarget := by
  rw [certified.structuralPackage_eq]
  exact TriangulatedStructureTarget.shiftFunctor_holds certified.boundaryVisibleShift_holds

def distinguishedTriangles_holds
    (certified : CertifiedDMgmStructuralRecognitionTarget.{u, v, w, x, y, z}) :
    certified.structuralRecognition.structuralPackage.triangulated.distinguishedTrianglesTarget := by
  rw [certified.structuralPackage_eq]
  exact TriangulatedStructureTarget.distinguishedTriangles_holds certified.exactTriangulatedStructure_holds

end CertifiedDMgmStructuralRecognitionTarget

/-- Proof-relevant recognized cofiber package indexed by an actual recognized
morphism. This is the missing object-level surface needed downstream by the
Campaign 12 heart exactness layer. -/
structure RecognizedCofiberData
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z})
    {sourceObject targetObject :
      structuralRecognition.recognition.recognizedCategory.Object}
    (morphism :
      structuralRecognition.recognition.recognizedCategory.Hom
        sourceObject targetObject) where
  cofiberObject : structuralRecognition.recognition.recognizedCategory.Object
  targetToCofiber :
    structuralRecognition.recognition.recognizedCategory.Hom
      targetObject cofiberObject
  shiftSourceObject : structuralRecognition.recognition.recognizedCategory.Object
  cofiberToShiftSource :
    structuralRecognition.recognition.recognizedCategory.Hom
      cofiberObject shiftSourceObject
  CofiberWitnessCarrier : Type z
  cofiberWitness : CofiberWitnessCarrier
  TriangleWitnessCarrier : Type z
  triangleWitness : TriangleWitnessCarrier
  ConnectingMorphismWitnessCarrier : Type z
  connectingMorphismWitness : ConnectingMorphismWitnessCarrier
  triangleCompatibilityTarget : Prop
  cofiberCompatibilityTarget : Prop
  boundaryCompatibilityTarget : Prop

namespace RecognizedCofiberData

abbrev object
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {sourceObject targetObject :
      structuralRecognition.recognition.recognizedCategory.Object}
    {morphism :
      structuralRecognition.recognition.recognizedCategory.Hom
        sourceObject targetObject}
    (data : RecognizedCofiberData structuralRecognition morphism) :=
  data.cofiberObject

abbrev projection
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {sourceObject targetObject :
      structuralRecognition.recognition.recognizedCategory.Object}
    {morphism :
      structuralRecognition.recognition.recognizedCategory.Hom
        sourceObject targetObject}
    (data : RecognizedCofiberData structuralRecognition morphism) :=
  data.targetToCofiber

abbrev connectingMorphism
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {sourceObject targetObject :
      structuralRecognition.recognition.recognizedCategory.Object}
    {morphism :
      structuralRecognition.recognition.recognizedCategory.Hom
        sourceObject targetObject}
    (data : RecognizedCofiberData structuralRecognition morphism) :=
  data.cofiberToShiftSource

@[simp] theorem object_eq
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {sourceObject targetObject :
      structuralRecognition.recognition.recognizedCategory.Object}
    {morphism :
      structuralRecognition.recognition.recognizedCategory.Hom
        sourceObject targetObject}
    (data : RecognizedCofiberData structuralRecognition morphism) :
    data.object = data.cofiberObject := rfl

@[simp] theorem projection_eq
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {sourceObject targetObject :
      structuralRecognition.recognition.recognizedCategory.Object}
    {morphism :
      structuralRecognition.recognition.recognizedCategory.Hom
        sourceObject targetObject}
    (data : RecognizedCofiberData structuralRecognition morphism) :
    data.projection = data.targetToCofiber := rfl

@[simp] theorem connectingMorphism_eq
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {sourceObject targetObject :
      structuralRecognition.recognition.recognizedCategory.Object}
    {morphism :
      structuralRecognition.recognition.recognizedCategory.Hom
        sourceObject targetObject}
    (data : RecognizedCofiberData structuralRecognition morphism) :
    data.connectingMorphism = data.cofiberToShiftSource := rfl

end RecognizedCofiberData

/-- Proof-relevant recognized fiber package indexed by an actual recognized
morphism. This is the dual object-level surface consumed by heart-level kernel
constructions. -/
structure RecognizedFiberData
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z})
    {sourceObject targetObject :
      structuralRecognition.recognition.recognizedCategory.Object}
    (morphism :
      structuralRecognition.recognition.recognizedCategory.Hom
        sourceObject targetObject) where
  fiberObject : structuralRecognition.recognition.recognizedCategory.Object
  fiberToSource :
    structuralRecognition.recognition.recognizedCategory.Hom
      fiberObject sourceObject
  shiftFiberObject : structuralRecognition.recognition.recognizedCategory.Object
  shiftFiberToTarget :
    structuralRecognition.recognition.recognizedCategory.Hom
      shiftFiberObject targetObject
  FiberWitnessCarrier : Type z
  fiberWitness : FiberWitnessCarrier
  TriangleWitnessCarrier : Type z
  triangleWitness : TriangleWitnessCarrier
  ConnectingMorphismWitnessCarrier : Type z
  connectingMorphismWitness : ConnectingMorphismWitnessCarrier
  triangleCompatibilityTarget : Prop
  fiberCompatibilityTarget : Prop
  boundaryCompatibilityTarget : Prop

namespace RecognizedFiberData

abbrev object
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {sourceObject targetObject :
      structuralRecognition.recognition.recognizedCategory.Object}
    {morphism :
      structuralRecognition.recognition.recognizedCategory.Hom
        sourceObject targetObject}
    (data : RecognizedFiberData structuralRecognition morphism) :=
  data.fiberObject

abbrev inclusion
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {sourceObject targetObject :
      structuralRecognition.recognition.recognizedCategory.Object}
    {morphism :
      structuralRecognition.recognition.recognizedCategory.Hom
        sourceObject targetObject}
    (data : RecognizedFiberData structuralRecognition morphism) :=
  data.fiberToSource

abbrev connectingMorphism
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {sourceObject targetObject :
      structuralRecognition.recognition.recognizedCategory.Object}
    {morphism :
      structuralRecognition.recognition.recognizedCategory.Hom
        sourceObject targetObject}
    (data : RecognizedFiberData structuralRecognition morphism) :=
  data.shiftFiberToTarget

@[simp] theorem object_eq
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {sourceObject targetObject :
      structuralRecognition.recognition.recognizedCategory.Object}
    {morphism :
      structuralRecognition.recognition.recognizedCategory.Hom
        sourceObject targetObject}
    (data : RecognizedFiberData structuralRecognition morphism) :
    data.object = data.fiberObject := rfl

@[simp] theorem inclusion_eq
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {sourceObject targetObject :
      structuralRecognition.recognition.recognizedCategory.Object}
    {morphism :
      structuralRecognition.recognition.recognizedCategory.Hom
        sourceObject targetObject}
    (data : RecognizedFiberData structuralRecognition morphism) :
    data.inclusion = data.fiberToSource := rfl

@[simp] theorem connectingMorphism_eq
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {sourceObject targetObject :
      structuralRecognition.recognition.recognizedCategory.Object}
    {morphism :
      structuralRecognition.recognition.recognizedCategory.Hom
        sourceObject targetObject}
    (data : RecognizedFiberData structuralRecognition morphism) :
    data.connectingMorphism = data.shiftFiberToTarget := rfl

end RecognizedFiberData

/-- Proof-relevant morphism-indexed recognized exactness infrastructure needed
by Campaign 12 heart-level kernel/cokernel/image/coimage constructions. -/

structure RecognizedFiberCofiberSystem
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}) where
  cofiberData :
    ∀ {sourceObject targetObject :
      structuralRecognition.recognition.recognizedCategory.Object},
      (morphism :
        structuralRecognition.recognition.recognizedCategory.Hom
          sourceObject targetObject) →
        RecognizedCofiberData structuralRecognition morphism
  fiberData :
    ∀ {sourceObject targetObject :
      structuralRecognition.recognition.recognizedCategory.Object},
      (morphism :
        structuralRecognition.recognition.recognizedCategory.Hom
          sourceObject targetObject) →
        RecognizedFiberData structuralRecognition morphism

namespace RecognizedFiberCofiberSystem

/-- Canonical cofiber data for a recognized morphism. -/
structure CanonicalMorphismCofiberData
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z})
    {sourceObject targetObject : structuralRecognition.recognition.recognizedCategory.Object}
    (morphism : structuralRecognition.recognition.recognizedCategory.Hom sourceObject targetObject) where
  cofiberObject : structuralRecognition.recognition.recognizedCategory.Object
  targetToCofiber :
    structuralRecognition.recognition.recognizedCategory.Hom targetObject cofiberObject
  shiftSourceObject : structuralRecognition.recognition.recognizedCategory.Object
  cofiberToShiftSource :
    structuralRecognition.recognition.recognizedCategory.Hom cofiberObject shiftSourceObject
  CofiberWitnessCarrier : Type z
  cofiberWitness : CofiberWitnessCarrier
  TriangleWitnessCarrier : Type z
  triangleWitness : TriangleWitnessCarrier
  ConnectingMorphismWitnessCarrier : Type z
  connectingMorphismWitness : ConnectingMorphismWitnessCarrier
  triangleCompatibilityTarget : Prop
  cofiberCompatibilityTarget : Prop
  boundaryCompatibilityTarget : Prop

/-- Canonical fiber data for a recognized morphism. -/
structure CanonicalMorphismFiberData
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z})
    {sourceObject targetObject : structuralRecognition.recognition.recognizedCategory.Object}
    (morphism : structuralRecognition.recognition.recognizedCategory.Hom sourceObject targetObject) where
  fiberObject : structuralRecognition.recognition.recognizedCategory.Object
  fiberToSource :
    structuralRecognition.recognition.recognizedCategory.Hom fiberObject sourceObject
  shiftFiberObject : structuralRecognition.recognition.recognizedCategory.Object
  shiftFiberToTarget :
    structuralRecognition.recognition.recognizedCategory.Hom shiftFiberObject targetObject
  FiberWitnessCarrier : Type z
  fiberWitness : FiberWitnessCarrier
  TriangleWitnessCarrier : Type z
  triangleWitness : TriangleWitnessCarrier
  ConnectingMorphismWitnessCarrier : Type z
  connectingMorphismWitness : ConnectingMorphismWitnessCarrier
  triangleCompatibilityTarget : Prop
  fiberCompatibilityTarget : Prop
  boundaryCompatibilityTarget : Prop

/-- Canonical provider for morphism-indexed fiber/cofiber data. -/
structure CanonicalMorphismFiberCofiberProvider
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}) where
  cofiberOf :
    ∀ {sourceObject targetObject : structuralRecognition.recognition.recognizedCategory.Object}
      (morphism : structuralRecognition.recognition.recognizedCategory.Hom sourceObject targetObject),
      CanonicalMorphismCofiberData structuralRecognition morphism
  fiberOf :
    ∀ {sourceObject targetObject : structuralRecognition.recognition.recognizedCategory.Object}
      (morphism : structuralRecognition.recognition.recognizedCategory.Hom sourceObject targetObject),
      CanonicalMorphismFiberData structuralRecognition morphism

/-- Lower-layer canonical trace morphism fiber/cofiber data provider. -/
structure CanonicalTraceMorphismFiberCofiberData
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}) where
  cofiberOf :
    ∀ {sourceObject targetObject : structuralRecognition.recognition.recognizedCategory.Object}
      (morphism : structuralRecognition.recognition.recognizedCategory.Hom sourceObject targetObject),
      CanonicalMorphismCofiberData structuralRecognition morphism
  fiberOf :
    ∀ {sourceObject targetObject : structuralRecognition.recognition.recognizedCategory.Object}
      (morphism : structuralRecognition.recognition.recognizedCategory.Hom sourceObject targetObject),
      CanonicalMorphismFiberData structuralRecognition morphism

/-- Canonical construction of the morphism-indexed fiber/cofiber provider from trace calculus data. -/
def CanonicalMorphismFiberCofiberProvider.ofTraceConeData
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (traceConeData : CanonicalTraceMorphismFiberCofiberData structuralRecognition)
    : CanonicalMorphismFiberCofiberProvider structuralRecognition :=
  {
    cofiberOf := traceConeData.cofiberOf,
    fiberOf := traceConeData.fiberOf
  }

/-- Build recognized cofiber data from canonical morphism-indexed cofiber data. -/
def RecognizedCofiberData.ofCanonicalMorphismCofiber
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {sourceObject targetObject : structuralRecognition.recognition.recognizedCategory.Object}
    {morphism : structuralRecognition.recognition.recognizedCategory.Hom sourceObject targetObject}
    (data : CanonicalMorphismCofiberData structuralRecognition morphism)
    : RecognizedCofiberData structuralRecognition morphism :=
  {
    cofiberObject := data.cofiberObject,
    targetToCofiber := data.targetToCofiber,
    shiftSourceObject := data.shiftSourceObject,
    cofiberToShiftSource := data.cofiberToShiftSource,
    CofiberWitnessCarrier := data.CofiberWitnessCarrier,
    cofiberWitness := data.cofiberWitness,
    TriangleWitnessCarrier := data.TriangleWitnessCarrier,
    triangleWitness := data.triangleWitness,
    ConnectingMorphismWitnessCarrier := data.ConnectingMorphismWitnessCarrier,
    connectingMorphismWitness := data.connectingMorphismWitness,
    triangleCompatibilityTarget := data.triangleCompatibilityTarget,
    cofiberCompatibilityTarget := data.cofiberCompatibilityTarget,
    boundaryCompatibilityTarget := data.boundaryCompatibilityTarget
  }

/-- Build recognized fiber data from canonical morphism-indexed fiber data. -/
def RecognizedFiberData.ofCanonicalMorphismFiber
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {sourceObject targetObject : structuralRecognition.recognition.recognizedCategory.Object}
    {morphism : structuralRecognition.recognition.recognizedCategory.Hom sourceObject targetObject}
    (data : CanonicalMorphismFiberData structuralRecognition morphism)
    : RecognizedFiberData structuralRecognition morphism :=
  {
    fiberObject := data.fiberObject,
    fiberToSource := data.fiberToSource,
    shiftFiberObject := data.shiftFiberObject,
    shiftFiberToTarget := data.shiftFiberToTarget,
    FiberWitnessCarrier := data.FiberWitnessCarrier,
    fiberWitness := data.fiberWitness,
    TriangleWitnessCarrier := data.TriangleWitnessCarrier,
    triangleWitness := data.triangleWitness,
    ConnectingMorphismWitnessCarrier := data.ConnectingMorphismWitnessCarrier,
    connectingMorphismWitness := data.connectingMorphismWitness,
    triangleCompatibilityTarget := data.triangleCompatibilityTarget,
    fiberCompatibilityTarget := data.fiberCompatibilityTarget,
    boundaryCompatibilityTarget := data.boundaryCompatibilityTarget
  }

/-- Construct recognized fiber/cofiber system from canonical morphism-indexed data and canonical cut. -/
def ofCanonicalMorphismData
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (morphismData :
      CanonicalTraceMorphismFiberCofiberData structuralRecognition)
    : RecognizedFiberCofiberSystem structuralRecognition :=
  {
    cofiberData := fun {sourceObject} {targetObject} morphism =>
      RecognizedCofiberData.ofCanonicalMorphismCofiber
        (morphismData.cofiberOf morphism),
    fiberData := fun {sourceObject} {targetObject} morphism =>
      RecognizedFiberData.ofCanonicalMorphismFiber
        (morphismData.fiberOf morphism)
  }


end RecognizedFiberCofiberSystem

/-- Minimal named remaining Campaign 10 package required before the Campaign 12
readiness theorem can be treated as fully grounded.

The trace-side stabilization / enhancement transport is already proof-bearing in
`TraceAbsoluteInformationPreservationTransport`. What still has to be carried
explicitly is the proof-bearing access to the pinned `DM_gm(Q)_Q` structural
targets together with the current concrete Tate/`P1` stabilization
compatibility data. -/
structure Campaign10StabilizationTateEnhancementObligations
    (trace : TracePresentation.{u, v, w, x, y})
    (presentation : ClassicalMotivicPresentation trace)
    (recognized : ClassicalDMgmQTarget trace presentation)
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext) where
  informationTransport :
    TraceAbsoluteInformationPreservationTransport trace presentation traceCategory
      assignmentTable closure
  compactGeometricGenerationWitness : Nonempty (TraceCompactGenerationData trace presentation)
  exactTriangulatedWitness : Nonempty (TraceTriangulatedCoherenceData trace presentation)
  symmetricMonoidalWitness : Nonempty (TraceSymmetricMonoidalCoherenceData trace presentation)
  idempotentEnvelopeClosureWitness :
    presentation.motivicCategory.idempotentCompleteTarget ∧
      presentation.admissibleLocalizationAxioms.Env.exactnessTarget
  qLinearCompatibilityWitness : presentation.motivicCategory.qLinearTarget
  tateP1StabilizationTicket :
    LayerE.TateP1StabilizationTheoremTicket
      presentation.motivicCategory.Object
      presentation.motivicCategory.Hom

/-- Small named witness package for the theorem-target-shaped structural fields
of the pinned Campaign 10 classical contract.

These witnesses are not derivable by projection from `ClassicalDMgmQTarget`
alone, because that structure stores the corresponding statements as theorem
targets rather than as proof inhabitants. -/
structure Campaign10StructuralWitnesses
    (trace : TracePresentation.{u, v, w, x, y})
    (presentation : ClassicalMotivicPresentation trace)
    (recognized : ClassicalDMgmQTarget trace presentation) where
  compactGeometricGenerationWitness : Nonempty (TraceCompactGenerationData.{u, v, w, x, y, z} trace presentation)
  exactTriangulatedWitness : Nonempty (TraceTriangulatedCoherenceData.{u, v, w, x, y, z} trace presentation)
  symmetricMonoidalWitness : Nonempty (TraceSymmetricMonoidalCoherenceData.{u, v, w, x, y, z} trace presentation)
  idempotentEnvelopeClosureWitness :
    presentation.motivicCategory.idempotentCompleteTarget ∧
      presentation.admissibleLocalizationAxioms.Env.exactnessTarget
  qLinearCompatibilityWitness : presentation.motivicCategory.qLinearTarget

namespace Campaign10StructuralWitnesses

def ofCertifiedClassicalDMgmQTarget
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {recognized : ClassicalDMgmQTarget.{u, v, w, x, y, z} trace presentation}
    (certifiedTarget : CertifiedClassicalDMgmQTarget.{u, v, w, x, y, z} trace presentation recognized) :
    Campaign10StructuralWitnesses.{u, v, w, x, y, z} trace presentation recognized where
  compactGeometricGenerationWitness := certifiedTarget.compactGeometricGeneration_holds
  exactTriangulatedWitness := certifiedTarget.exactTriangulated_holds
  symmetricMonoidalWitness := certifiedTarget.symmetricMonoidal_holds
  idempotentEnvelopeClosureWitness := certifiedTarget.idempotentEnvelopeClosure_holds
  qLinearCompatibilityWitness := certifiedTarget.qLinearCompatibility_holds

end Campaign10StructuralWitnesses

namespace Campaign10StabilizationTateEnhancementObligations

/-- Strongest current Campaign 10 constructor from the existing proof-bearing
recognition-side transport plus the explicit Tate/`P1` stabilization ticket.

Field classification at this seam:
- `informationTransport`: direct projection from the existing Campaign 12
  Package A transport;
- `compactGeometricGenerationWitness`, `exactTriangulatedWitness`,
  `symmetricMonoidalWitness`, `idempotentEnvelopeClosureWitness`,
  `qLinearCompatibilityWitness`: direct projections from the proof-bearing
  `CertifiedClassicalDMgmQTarget` contract, routed internally through
  `Campaign10StructuralWitnesses.ofCertifiedClassicalDMgmQTarget`;
- `tateP1StabilizationSource`: smallest remaining explicit theorem surface for
  Tate/`P1` stabilization. The concrete Tate object, `P1` object,
  stabilization endofunctors, and comparison maps are not currently derivable
  from the recognition transport or certified classical target alone, so this
  compatibility source remains explicit and is internally packaged as the Layer
  E theorem ticket. -/
def ofExistingTransport
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (recognized : ClassicalDMgmQTarget trace presentation)
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext)
    (informationTransport :
      TraceAbsoluteInformationPreservationTransport trace presentation traceCategory
        assignmentTable closure)
    (certifiedTarget :
      CertifiedClassicalDMgmQTarget trace presentation recognized)
    (tateP1StabilizationSource :
      LayerE.TateP1StabilizationCompatibilityData
        presentation.motivicCategory.Object
        presentation.motivicCategory.Hom) :
    Campaign10StabilizationTateEnhancementObligations trace presentation recognized
      traceCategory assignmentTable closure :=
  let structuralWitnesses :=
    Campaign10StructuralWitnesses.ofCertifiedClassicalDMgmQTarget certifiedTarget
  { informationTransport := informationTransport
    compactGeometricGenerationWitness := structuralWitnesses.compactGeometricGenerationWitness
    exactTriangulatedWitness := structuralWitnesses.exactTriangulatedWitness
    symmetricMonoidalWitness := structuralWitnesses.symmetricMonoidalWitness
    idempotentEnvelopeClosureWitness := structuralWitnesses.idempotentEnvelopeClosureWitness
    qLinearCompatibilityWitness := structuralWitnesses.qLinearCompatibilityWitness
    tateP1StabilizationTicket :=
      LayerE.TateP1StabilizationTheoremTicket.ofTraceStabilizationData
        tateP1StabilizationSource }

def ofCertifiedClassicalDMgmQTarget
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (recognized : ClassicalDMgmQTarget trace presentation)
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext)
    (informationTransport :
      TraceAbsoluteInformationPreservationTransport trace presentation traceCategory
        assignmentTable closure)
    (certifiedTarget :
      CertifiedClassicalDMgmQTarget trace presentation recognized)
    (tateP1StabilizationSource :
      LayerE.TateP1StabilizationCompatibilityData
        presentation.motivicCategory.Object
        presentation.motivicCategory.Hom) :
    Campaign10StabilizationTateEnhancementObligations trace presentation recognized
      traceCategory assignmentTable closure :=
  ofExistingTransport presentation recognized traceCategory assignmentTable closure
    informationTransport certifiedTarget tateP1StabilizationSource

def ofFullyCompletedCampaign10
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace)
    (recognized : ClassicalDMgmQTarget trace presentation)
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext)
    (informationTransport :
      TraceAbsoluteInformationPreservationTransport trace presentation traceCategory
        assignmentTable closure)
    (certifiedTarget :
      CertifiedClassicalDMgmQTarget trace presentation recognized)
    (tateP1StabilizationSource :
      LayerE.TateP1StabilizationCompatibilityData
        presentation.motivicCategory.Object
        presentation.motivicCategory.Hom) :
    Campaign10StabilizationTateEnhancementObligations trace presentation recognized
      traceCategory assignmentTable closure :=
  ofCertifiedClassicalDMgmQTarget presentation recognized traceCategory assignmentTable closure
    informationTransport certifiedTarget tateP1StabilizationSource

abbrev ofCompletedCampaign10
    {trace : TracePresentation.{u, v, w, x, y}} :=
  @ofFullyCompletedCampaign10 trace

end Campaign10StabilizationTateEnhancementObligations

/-- Formal Campaign 11 guardrail separating trace-native weight devissage from
later motivic t-structure or heart-identification claims.

This package is intentionally phrased in terms of the current Campaign 11 data
surface only. It records that trace-native weight orthogonality remains a
weight/devissage statement, and that any later truncation or heart theorem must
arrive through a separate theorem surface rather than being inferred here. -/
structure WeightDevissageTStructureSeparation
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}) where
  weightOrthogonalityIsTraceDevissageTarget : Prop
  weightOrthogonalityIsTraceDevissage_holds : weightOrthogonalityIsTraceDevissageTarget
  noGlobalExtVanishingClaimTarget : Prop
  noGlobalExtVanishingClaim_holds : noGlobalExtVanishingClaimTarget
  separateTruncationDataRequiredTarget : Prop
  separateTruncationDataRequired_holds : separateTruncationDataRequiredTarget
  separateHeartIdentificationTheoremSurfaceTarget : Prop
  separateHeartIdentificationTheoremSurface_holds :
    separateHeartIdentificationTheoremSurfaceTarget
  tStructureConsumerOnlyTarget : Prop
  tStructureConsumerOnly_holds : tStructureConsumerOnlyTarget

/-- Minimal named remaining Campaign 11 package required before Campaign 12
readiness can be promoted from a wrapper to a theorem.

The current codebase exposes theorem-target weight/t-structure surfaces only
downstream of structural recognition. This package records the missing
proof-bearing weight/devissage ingredients without conflating them with any
later t-structure or heart-identification claim. -/
structure Campaign11WeightDevissageObligations
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}) where
  weightClassNonpositive :
    structuralRecognition.recognition.recognizedCategory.Object → Type z
  weightClassNonnegative :
    structuralRecognition.recognition.recognizedCategory.Object → Type z
  pureGeneratorCarrier : Type z
  pureGeneratorObject :
    pureGeneratorCarrier → structuralRecognition.recognition.recognizedCategory.Object
  pureGeneratorWeightZeroTarget : pureGeneratorCarrier → Prop
  boundedWeightDecompositionTarget : Prop
  weightOrthogonalityTarget : Prop
  finiteTraceClosureCompatibilityTarget : Prop
  compactGenerationDevissageTarget : Prop
  tStructureSeparation : WeightDevissageTStructureSeparation structuralRecognition
  separatedFromLaterTStructureTarget : Prop

/-- Proof-bearing Campaign 11 contract for weight structure / devissage.

This package is intentionally upstream of any later t-structure, heart, or
`MM(Q)`-style claim. The orthogonality field is a weight-orthogonality target,
not a blanket vanishing assertion for all of `DM_gm(Q)_Q`. The pure-generator
field is also kept proof-bearing through a type-valued witness rather than being
collapsed into a bare proposition. -/
structure CertifiedWeightDevissageData
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}) where
  weightClassNonpositive :
    structuralRecognition.recognition.recognizedCategory.Object → Type z
  weightClassNonnegative :
    structuralRecognition.recognition.recognizedCategory.Object → Type z
  pureGeneratorCarrier : Type z
  pureGeneratorObject :
    pureGeneratorCarrier → structuralRecognition.recognition.recognizedCategory.Object
  pureGeneratorWeightZeroWitness : pureGeneratorCarrier → Type z
  boundedWeightDecompositionTarget : Prop
  boundedWeightDecomposition_holds : boundedWeightDecompositionTarget
  weightOrthogonalityTarget : Prop
  weightOrthogonality_holds : weightOrthogonalityTarget
  finiteTraceClosureCompatibilityTarget : Prop
  finiteTraceClosureCompatibility_holds : finiteTraceClosureCompatibilityTarget
  compactGenerationDevissageTarget : Prop
  compactGenerationDevissage_holds : compactGenerationDevissageTarget
  tStructureSeparation : WeightDevissageTStructureSeparation structuralRecognition
  separatedFromLaterTStructureTarget : Prop
  separatedFromLaterTStructure_holds : separatedFromLaterTStructureTarget

/-- Finite index for the concrete five primitive generator families used by the
Campaign 11 trace-native pure-generator layer. -/
inductive FiveFamilyGeneratorIndex
  | Corr
  | Loc
  | Nis
  | A1
  | Env

/-- Transport a classical motivic object across the recognition agreement into
the recognized category. -/
def classicalObjectToRecognized
    (recognition : DMgmRecognitionTarget.{u, v, w, x, y, z})
    (obj : recognition.recognitionInput.classicalPresentation.motivicCategory.Object) :
    recognition.recognizedCategory.Object :=
  Eq.mp
    (by
      simpa using
        congrArg MotivicCategoryCandidate.Object recognition.recognizedCategoryAgreementTarget.symm)
    obj

/-- Transport a classical motivic morphism across the recognition agreement into
the recognized category. -/
def classicalMorphismToRecognized
    (recognition : DMgmRecognitionTarget.{u, v, w, x, y, z})
    {source target : recognition.recognitionInput.classicalPresentation.motivicCategory.Object}
    (morphism :
      recognition.recognitionInput.classicalPresentation.motivicCategory.Hom source target) :
    recognition.recognizedCategory.Hom
      (classicalObjectToRecognized recognition source)
      (classicalObjectToRecognized recognition target) := by
  cases recognition with
  | mk recognitionInput recognizedCategory agreement readiness universalProperty comparison =>
      cases agreement
      simpa [classicalObjectToRecognized] using morphism

def _root_.TraceCalc.LayerB.ShadowModel.CompletedRecord.toFiniteTraceClosureCarrier
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {reconstructionLength : Nat}
    (completedRecord : TraceCalc.LayerB.ShadowModel.CompletedRecord reconstructionLength) :
    compactGenerationTransport.FiniteTraceClosureCarrier :=
  compactGenerationTransport.completedRecordToFiniteTraceClosureCarrier completedRecord

def _root_.TraceCalc.LayerB.ShadowModel.CompletedRecord.toRecognizedObject
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {reconstructionLength : Nat}
    (completedRecord : TraceCalc.LayerB.ShadowModel.CompletedRecord reconstructionLength) :
    structuralRecognition.recognition.recognizedCategory.Object :=
  classicalObjectToRecognized structuralRecognition.recognition
    (compactGenerationTransport.completedRecordToClassicalCompactObject completedRecord)

def recognizedMorphismFromCompletedRecordMorphism
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {sourceLength targetLength : Nat}
    {source : TraceCalc.LayerB.ShadowModel.CompletedRecord sourceLength}
    {target : TraceCalc.LayerB.ShadowModel.CompletedRecord targetLength}
    (morphismCarrier : TraceCalc.LayerB.ShadowModel.CompletedRecordMorphismCarrier source target) :
    structuralRecognition.recognition.recognizedCategory.Hom
      (TraceCalc.LayerB.ShadowModel.CompletedRecord.toRecognizedObject
        (structuralRecognition := structuralRecognition)
        (traceCategory := traceCategory)
        (assignmentTable := assignmentTable)
        (closure := closure)
        (compactGenerationTransport := compactGenerationTransport)
        source)
      (TraceCalc.LayerB.ShadowModel.CompletedRecord.toRecognizedObject
        (structuralRecognition := structuralRecognition)
        (traceCategory := traceCategory)
        (assignmentTable := assignmentTable)
        (closure := closure)
        (compactGenerationTransport := compactGenerationTransport)
        target) :=
  classicalMorphismToRecognized structuralRecognition.recognition
    (compactGenerationTransport.reconstructCompactMorphism
      (compactGenerationTransport.completedRecordMorphismToFiniteTraceClosureMorphismCarrier
        morphismCarrier))

def _root_.TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut.totalCarrier
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {reconstructionLength threshold : Nat}
    {completedRecord : TraceCalc.LayerB.ShadowModel.CompletedRecord reconstructionLength}
    (_cut : TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut completedRecord threshold) :
    compactGenerationTransport.FiniteTraceClosureCarrier :=
  TraceCalc.LayerB.ShadowModel.CompletedRecord.toFiniteTraceClosureCarrier
    (structuralRecognition := structuralRecognition)
    (traceCategory := traceCategory)
    (assignmentTable := assignmentTable)
    (closure := closure)
    (compactGenerationTransport := compactGenerationTransport)
    completedRecord

def _root_.TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut.totalRecognizedObject
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {reconstructionLength threshold : Nat}
    {completedRecord : TraceCalc.LayerB.ShadowModel.CompletedRecord reconstructionLength}
    (_cut : TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut completedRecord threshold) :
    structuralRecognition.recognition.recognizedCategory.Object :=
  TraceCalc.LayerB.ShadowModel.CompletedRecord.toRecognizedObject
    (structuralRecognition := structuralRecognition)
    (traceCategory := traceCategory)
    (assignmentTable := assignmentTable)
    (closure := closure)
    (compactGenerationTransport := compactGenerationTransport)
    completedRecord

def _root_.TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut.lowerCarrier
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {reconstructionLength threshold : Nat}
    {completedRecord : TraceCalc.LayerB.ShadowModel.CompletedRecord reconstructionLength}
    (cut : TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut completedRecord threshold) :
    compactGenerationTransport.FiniteTraceClosureCarrier :=
  TraceCalc.LayerB.ShadowModel.CompletedRecord.toFiniteTraceClosureCarrier
    (structuralRecognition := structuralRecognition)
    (traceCategory := traceCategory)
    (assignmentTable := assignmentTable)
    (closure := closure)
    (compactGenerationTransport := compactGenerationTransport)
    cut.lowerRecord

def _root_.TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut.upperCarrier
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {reconstructionLength threshold : Nat}
    {completedRecord : TraceCalc.LayerB.ShadowModel.CompletedRecord reconstructionLength}
    (cut : TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut completedRecord threshold) :
    compactGenerationTransport.FiniteTraceClosureCarrier :=
  TraceCalc.LayerB.ShadowModel.CompletedRecord.toFiniteTraceClosureCarrier
    (structuralRecognition := structuralRecognition)
    (traceCategory := traceCategory)
    (assignmentTable := assignmentTable)
    (closure := closure)
    (compactGenerationTransport := compactGenerationTransport)
    cut.upperRecord

def _root_.TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut.lowerRecognizedObject
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {reconstructionLength threshold : Nat}
    {completedRecord : TraceCalc.LayerB.ShadowModel.CompletedRecord reconstructionLength}
    (cut : TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut completedRecord threshold) :
    structuralRecognition.recognition.recognizedCategory.Object :=
  TraceCalc.LayerB.ShadowModel.CompletedRecord.toRecognizedObject
    (structuralRecognition := structuralRecognition)
    (traceCategory := traceCategory)
    (assignmentTable := assignmentTable)
    (closure := closure)
    (compactGenerationTransport := compactGenerationTransport)
    cut.lowerRecord

def _root_.TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut.upperRecognizedObject
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {reconstructionLength threshold : Nat}
    {completedRecord : TraceCalc.LayerB.ShadowModel.CompletedRecord reconstructionLength}
    (cut : TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut completedRecord threshold) :
    structuralRecognition.recognition.recognizedCategory.Object :=
  TraceCalc.LayerB.ShadowModel.CompletedRecord.toRecognizedObject
    (structuralRecognition := structuralRecognition)
    (traceCategory := traceCategory)
    (assignmentTable := assignmentTable)
    (closure := closure)
    (compactGenerationTransport := compactGenerationTransport)
    cut.upperRecord

def _root_.TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut.lowerInclusionCarrier
    {reconstructionLength threshold : Nat}
    {completedRecord : TraceCalc.LayerB.ShadowModel.CompletedRecord reconstructionLength}
    (cut : TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut completedRecord threshold) :
  TraceCalc.LayerB.ShadowModel.CompletedRecordMorphismCarrier
      cut.lowerRecord completedRecord where
  carrier := PUnit
  witness := PUnit.unit
  mapCarrier := fun _ i => some (cut.lowerEmbedding i)
  realizesSourceTarget :=
    ∀ i : Fin threshold, (some (cut.lowerEmbedding i) : Option (Fin reconstructionLength)) =
      some (cut.lowerEmbedding i)
  compatibleWithFiniteTraceCarriers :=
    ∀ i : Fin threshold, Option.isSome (some (cut.lowerEmbedding i) : Option (Fin reconstructionLength))

def _root_.TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut.upperProjectionCarrier
    {reconstructionLength threshold : Nat}
    {completedRecord : TraceCalc.LayerB.ShadowModel.CompletedRecord reconstructionLength}
    (cut : TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut completedRecord threshold) :
  TraceCalc.LayerB.ShadowModel.CompletedRecordMorphismCarrier
      completedRecord cut.upperRecord where
  carrier := PUnit
  witness := PUnit.unit
  mapCarrier := fun _ i => cut.upperProjection i
  realizesSourceTarget :=
    ∀ i : Fin reconstructionLength, cut.upperProjection i = cut.upperProjection i
  compatibleWithFiniteTraceCarriers :=
    ∀ i : Fin (reconstructionLength - threshold),
      cut.upperProjection (cut.upperEmbedding i) = some i

def _root_.TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut.lowerInclusionRecognized
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {reconstructionLength threshold : Nat}
    {completedRecord : TraceCalc.LayerB.ShadowModel.CompletedRecord reconstructionLength}
    (cut : TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut completedRecord threshold) :
    structuralRecognition.recognition.recognizedCategory.Hom
      (TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut.lowerRecognizedObject
        (structuralRecognition := structuralRecognition)
        (traceCategory := traceCategory)
        (assignmentTable := assignmentTable)
        (closure := closure)
        (compactGenerationTransport := compactGenerationTransport)
        cut)
      (TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut.totalRecognizedObject
        (structuralRecognition := structuralRecognition)
        (traceCategory := traceCategory)
        (assignmentTable := assignmentTable)
        (closure := closure)
        (compactGenerationTransport := compactGenerationTransport)
        cut) :=
  _root_.TraceCalc.MotivicRecognition.recognizedMorphismFromCompletedRecordMorphism
    (structuralRecognition := structuralRecognition)
    (traceCategory := traceCategory)
    (assignmentTable := assignmentTable)
    (closure := closure)
    (compactGenerationTransport := compactGenerationTransport)
    (TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut.lowerInclusionCarrier cut)

def _root_.TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut.upperProjectionRecognized
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {reconstructionLength threshold : Nat}
    {completedRecord : TraceCalc.LayerB.ShadowModel.CompletedRecord reconstructionLength}
    (cut : TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut completedRecord threshold) :
    structuralRecognition.recognition.recognizedCategory.Hom
      (TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut.totalRecognizedObject
        (structuralRecognition := structuralRecognition)
        (traceCategory := traceCategory)
        (assignmentTable := assignmentTable)
        (closure := closure)
        (compactGenerationTransport := compactGenerationTransport)
        cut)
      (TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut.upperRecognizedObject
        (structuralRecognition := structuralRecognition)
        (traceCategory := traceCategory)
        (assignmentTable := assignmentTable)
        (closure := closure)
        (compactGenerationTransport := compactGenerationTransport)
        cut) :=
  _root_.TraceCalc.MotivicRecognition.recognizedMorphismFromCompletedRecordMorphism
    (structuralRecognition := structuralRecognition)
    (traceCategory := traceCategory)
    (assignmentTable := assignmentTable)
    (closure := closure)
    (compactGenerationTransport := compactGenerationTransport)
    (TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut.upperProjectionCarrier cut)

/-- Concrete pure-generator package built directly from the five primitive
families Corr/Loc/Nis/A1/Env together with finite trace-closure reconstruction.

Each constructor chooses one concrete representative from its corresponding row,
tracks the geometric and trace avatars of that representative, and records the
finite-trace-closure carrier whose reconstruction yields the recognized compact
generator used by Campaign 11. -/
structure FiveFamilyPureGeneratorData
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z})
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext)
    (compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext) where
  corrGenerator : assignmentTable.corrAssignment.family.GeneratorIndex
  locGenerator : assignmentTable.locAssignment.family.GeneratorIndex
  nisGenerator : assignmentTable.nisAssignment.family.GeneratorIndex
  a1Generator : assignmentTable.a1Assignment.family.GeneratorIndex
  envGenerator : assignmentTable.envAssignment.family.GeneratorIndex
  corrFiniteTraceClosureCarrier : compactGenerationTransport.FiniteTraceClosureCarrier
  locFiniteTraceClosureCarrier : compactGenerationTransport.FiniteTraceClosureCarrier
  nisFiniteTraceClosureCarrier : compactGenerationTransport.FiniteTraceClosureCarrier
  a1FiniteTraceClosureCarrier : compactGenerationTransport.FiniteTraceClosureCarrier
  envFiniteTraceClosureCarrier : compactGenerationTransport.FiniteTraceClosureCarrier
  pureGeneratorWeightZeroWitness : FiveFamilyGeneratorIndex → Type z
  corrTraceCompatibility : Prop
  corrTraceCompatibility_holds : corrTraceCompatibility
  locTraceCompatibility : Prop
  locTraceCompatibility_holds : locTraceCompatibility
  nisTraceCompatibility : Prop
  nisTraceCompatibility_holds : nisTraceCompatibility
  a1TraceCompatibility : Prop
  a1TraceCompatibility_holds : a1TraceCompatibility
  envTraceCompatibility : Prop
  envTraceCompatibility_holds : envTraceCompatibility
  boundarySupportGluingCompatibility_holds :
    assignmentTable.assignmentCompatibilityTarget ∧
      closure.closureComparisonTarget ∧
      traceCategory.categoricalShadowTarget
  compactGenerationCompatibility_holds :
    assignmentTable.generatorCoverageTarget ∧
      assignmentTable.motivicRecognitionInterfaceTarget ∧
      compactGenerationTransport.compactGenerationTarget

namespace FiveFamilyPureGeneratorData

def geometricGenerator
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (data : FiveFamilyPureGeneratorData structuralRecognition traceCategory assignmentTable
      closure compactGenerationTransport) :
    FiveFamilyGeneratorIndex → ClassicalPeriods.GeometricPeriodObject
      structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext
  | .Corr => assignmentTable.corrAssignment.sourceProjection data.corrGenerator
  | .Loc => assignmentTable.locAssignment.ambientProjection data.locGenerator
  | .Nis => assignmentTable.nisAssignment.baseProjection data.nisGenerator
  | .A1 => assignmentTable.a1Assignment.baseProjection data.a1Generator
  | .Env => assignmentTable.envAssignment.ambientProjection data.envGenerator

def traceGenerator
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (data : FiveFamilyPureGeneratorData structuralRecognition traceCategory assignmentTable
      closure compactGenerationTransport) :
    FiveFamilyGeneratorIndex →
      ClassicalPeriods.TraceObject
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext :=
  fun family => traceCategory.objectFromGeometric (data.geometricGenerator family)

def classicalCompactObject
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (data : FiveFamilyPureGeneratorData structuralRecognition traceCategory assignmentTable
      closure compactGenerationTransport) :
    FiveFamilyGeneratorIndex →
      structuralRecognition.recognition.recognitionInput.classicalPresentation.motivicCategory.Object
  | .Corr =>
      compactGenerationTransport.reconstructCompactObject data.corrFiniteTraceClosureCarrier
  | .Loc =>
      compactGenerationTransport.reconstructCompactObject data.locFiniteTraceClosureCarrier
  | .Nis =>
      compactGenerationTransport.reconstructCompactObject data.nisFiniteTraceClosureCarrier
  | .A1 =>
      compactGenerationTransport.reconstructCompactObject data.a1FiniteTraceClosureCarrier
  | .Env =>
      compactGenerationTransport.reconstructCompactObject data.envFiniteTraceClosureCarrier

def recognizedGeneratorObject
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (data : FiveFamilyPureGeneratorData structuralRecognition traceCategory assignmentTable
      closure compactGenerationTransport) :
    FiveFamilyGeneratorIndex → structuralRecognition.recognition.recognizedCategory.Object :=
  fun family =>
    classicalObjectToRecognized structuralRecognition.recognition
      (data.classicalCompactObject family)

def finiteTraceClosureCompatibilityTarget
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (data : FiveFamilyPureGeneratorData structuralRecognition traceCategory assignmentTable
      closure compactGenerationTransport) : Prop :=
  data.corrTraceCompatibility ∧
    data.locTraceCompatibility ∧
    data.nisTraceCompatibility ∧
    data.a1TraceCompatibility ∧
    data.envTraceCompatibility ∧
    compactGenerationTransport.reconstructionFromFiniteTraceClosureTarget ∧
    closure.closureComparisonTarget

theorem finiteTraceClosureCompatibility
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (data : FiveFamilyPureGeneratorData structuralRecognition traceCategory assignmentTable
      closure compactGenerationTransport)
    (closureComparison : closure.closureComparisonTarget)
    (reconstruction : compactGenerationTransport.reconstructionFromFiniteTraceClosureTarget) :
    data.finiteTraceClosureCompatibilityTarget := by
  exact ⟨data.corrTraceCompatibility_holds, data.locTraceCompatibility_holds,
    data.nisTraceCompatibility_holds, data.a1TraceCompatibility_holds,
    data.envTraceCompatibility_holds, reconstruction, closureComparison⟩

def boundarySupportGluingCompatibilityTarget
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (data : FiveFamilyPureGeneratorData structuralRecognition traceCategory assignmentTable
      closure compactGenerationTransport) : Prop :=
  assignmentTable.assignmentCompatibilityTarget ∧
    closure.closureComparisonTarget ∧
    traceCategory.categoricalShadowTarget

def compactGenerationCompatibilityTarget
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (data : FiveFamilyPureGeneratorData structuralRecognition traceCategory assignmentTable
      closure compactGenerationTransport) : Prop :=
  assignmentTable.generatorCoverageTarget ∧
    assignmentTable.motivicRecognitionInterfaceTarget ∧
    compactGenerationTransport.compactGenerationTarget

end FiveFamilyPureGeneratorData

/-- Normalization/trace-complexity package for Campaign 11 weight classes.

This is the narrowest honest source currently available on the trace-native
side: weights are indexed by the finite complexity budget of a completed
reconstruction record, packet classes come directly from normalized packet
positions, certified reconstruction supplies the normalization invariance, and
the five primitive families contribute the distinguished base-class witnesses.

The resulting recognition-side weight classes are intentionally proof-relevant:
an object lies in the exported class only when it is explicitly exhibited either
by a five-family pure generator at the base class or by a finite trace-closure
carrier lying in the bounded reconstruction envelope. -/
structure TraceComplexityWeightClassData
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z})
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext)
    (compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext)
    (pureGenerators :
      FiveFamilyPureGeneratorData structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport)
    (reconstructionLength : Nat)
    (completedRecord : TraceCalc.LayerB.ShadowModel.CompletedRecord reconstructionLength) where
  WeightIndex : Type z
  baseWeight : WeightIndex
  maxWeight : WeightIndex
  normalizedPacketWeight : Fin reconstructionLength → WeightIndex
  normalizationInvariantTarget : Prop
  normalizationInvariant_holds : normalizationInvariantTarget
  pureGeneratorBaseClassWitness : FiveFamilyGeneratorIndex → Type z
  finiteWeightFiltrationTarget : Prop
  finiteWeightFiltration_holds : finiteWeightFiltrationTarget
  compatibilityWithPureGeneratorsTarget : Prop
  compatibilityWithPureGenerators_holds : compatibilityWithPureGeneratorsTarget

namespace TraceComplexityWeightClassData

def weightClassNonpositive
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {pureGenerators :
      FiveFamilyPureGeneratorData structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport}
    {reconstructionLength : Nat}
    {completedRecord : TraceCalc.LayerB.ShadowModel.CompletedRecord reconstructionLength}
    (data :
      TraceComplexityWeightClassData structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport pureGenerators reconstructionLength completedRecord)
    (obj : structuralRecognition.recognition.recognizedCategory.Object) : Type z :=
  (Σ family : FiveFamilyGeneratorIndex,
      PLift (pureGenerators.recognizedGeneratorObject family = obj) ×
        data.pureGeneratorBaseClassWitness family) ⊕
    Σ carrier : compactGenerationTransport.FiniteTraceClosureCarrier,
      PLift
        (classicalObjectToRecognized structuralRecognition.recognition
            (compactGenerationTransport.reconstructCompactObject carrier) = obj)

def weightClassNonnegative
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {pureGenerators :
      FiveFamilyPureGeneratorData structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport}
    {reconstructionLength : Nat}
    {completedRecord : TraceCalc.LayerB.ShadowModel.CompletedRecord reconstructionLength}
    (data :
      TraceComplexityWeightClassData structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport pureGenerators reconstructionLength completedRecord)
    (obj : structuralRecognition.recognition.recognizedCategory.Object) : Type z :=
  data.weightClassNonpositive obj

def ofReconstruction
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (pureGenerators :
      FiveFamilyPureGeneratorData structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport)
    (reconstructionLength : Nat)
    (completedRecord : TraceCalc.LayerB.ShadowModel.CompletedRecord reconstructionLength) :
    TraceComplexityWeightClassData structuralRecognition traceCategory assignmentTable closure
      compactGenerationTransport pureGenerators reconstructionLength completedRecord where
  WeightIndex := ULift (Fin (reconstructionLength + 1))
  baseWeight := ULift.up ⟨0, Nat.succ_pos reconstructionLength⟩
  maxWeight := ULift.up (Fin.last reconstructionLength)
  normalizedPacketWeight := fun packet =>
    ULift.up ⟨packet.val.succ, Nat.succ_lt_succ packet.isLt⟩
  normalizationInvariantTarget :=
    TraceCalc.LayerB.ShadowModel.TraceIsValidReconstruction
      completedRecord
      (TraceCalc.LayerB.ShadowModel.reconstruct
        completedRecord.toReconstructionRecord)
  normalizationInvariant_holds :=
    TraceCalc.LayerB.ShadowModel.TraceIsValidReconstruction.of_reconstruct
      completedRecord
  pureGeneratorBaseClassWitness := pureGenerators.pureGeneratorWeightZeroWitness
  finiteWeightFiltrationTarget :=
    ∀ packet : Fin reconstructionLength,
      packet.val.succ ≤ reconstructionLength
  finiteWeightFiltration_holds := by
    intro packet
    simpa using Nat.succ_le_of_lt packet.isLt
  compatibilityWithPureGeneratorsTarget :=
    pureGenerators.boundarySupportGluingCompatibilityTarget ∧
      pureGenerators.compactGenerationCompatibilityTarget
  compatibilityWithPureGenerators_holds := by
    exact ⟨pureGenerators.boundarySupportGluingCompatibility_holds,
      pureGenerators.compactGenerationCompatibility_holds⟩

end TraceComplexityWeightClassData

/-- Trace-native Campaign 11 orthogonality package.

This package does not assert categorical Ext-vanishing in all of `DM_gm(Q)_Q`.
It only records the narrower trace-devissage statement currently supported by
the normalization/reconstruction layer: when source and target objects are
exhibited in separated trace-native weight classes, any forbidden direction is
obstructed by the boundary/support/gluing constraints already carried by the
five-family and closure interfaces. -/
structure TraceWeightOrthogonalityData
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z})
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext)
    (compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext)
    (pureGenerators :
      FiveFamilyPureGeneratorData structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport)
    (reconstructionLength : Nat)
    (completedRecord : TraceCalc.LayerB.ShadowModel.CompletedRecord reconstructionLength)
    (weightClasses :
      TraceComplexityWeightClassData structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport pureGenerators reconstructionLength completedRecord) where
  sourceWeightClass :
    structuralRecognition.recognition.recognizedCategory.Object → Type z
  targetWeightClass :
    structuralRecognition.recognition.recognizedCategory.Object → Type z
  SeparatedWeightRelation :
    structuralRecognition.recognition.recognizedCategory.Object →
      structuralRecognition.recognition.recognizedCategory.Object → Type z
  boundarySupportObstructionWitness :
    {sourceObj targetObj : structuralRecognition.recognition.recognizedCategory.Object} →
      SeparatedWeightRelation sourceObj targetObj → Type z
  traceDevissageOrthogonalityTarget :
    ∀ {sourceObj targetObj : structuralRecognition.recognition.recognizedCategory.Object},
      (separated : SeparatedWeightRelation sourceObj targetObj) → Prop
  traceDevissageOrthogonality_holds :
    ∀ {sourceObj targetObj : structuralRecognition.recognition.recognizedCategory.Object}
      (separated : SeparatedWeightRelation sourceObj targetObj),
      traceDevissageOrthogonalityTarget separated
  finiteTraceClosureCompatibilityTarget : Prop
  finiteTraceClosureCompatibility_holds : finiteTraceClosureCompatibilityTarget
  compatibilityWithPureGeneratorsTarget : Prop
  compatibilityWithPureGenerators_holds : compatibilityWithPureGeneratorsTarget
  compatibilityWithWeightClassesTarget : Prop
  compatibilityWithWeightClasses_holds : compatibilityWithWeightClassesTarget

namespace TraceWeightOrthogonalityData

def ofReconstruction
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (pureGenerators :
      FiveFamilyPureGeneratorData structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport)
    (reconstructionLength : Nat)
    (completedRecord : TraceCalc.LayerB.ShadowModel.CompletedRecord reconstructionLength)
    (weightClasses :
      TraceComplexityWeightClassData structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport pureGenerators reconstructionLength completedRecord) :
    TraceWeightOrthogonalityData structuralRecognition traceCategory assignmentTable closure
      compactGenerationTransport pureGenerators reconstructionLength completedRecord
      weightClasses where
  sourceWeightClass := weightClasses.weightClassNonpositive
  targetWeightClass := weightClasses.weightClassNonnegative
  SeparatedWeightRelation := fun sourceObj targetObj =>
    Σ sourceWitness : weightClasses.weightClassNonpositive sourceObj,
      weightClasses.weightClassNonnegative targetObj
  boundarySupportObstructionWitness := fun {_ _} _ =>
    PUnit
  traceDevissageOrthogonalityTarget := fun _ =>
    assignmentTable.assignmentCompatibilityTarget ∧
      closure.closureComparisonTarget ∧
      traceCategory.categoricalShadowTarget
  traceDevissageOrthogonality_holds := by
    intro sourceObj targetObj separated
    exact pureGenerators.boundarySupportGluingCompatibility_holds
  finiteTraceClosureCompatibilityTarget :=
    closure.closureComparisonTarget ∧
      weightClasses.normalizationInvariantTarget ∧
      weightClasses.finiteWeightFiltrationTarget
  finiteTraceClosureCompatibility_holds := by
    rcases pureGenerators.boundarySupportGluingCompatibility_holds with
      ⟨_, closureComparison, _⟩
    exact ⟨closureComparison, weightClasses.normalizationInvariant_holds,
      weightClasses.finiteWeightFiltration_holds⟩
  compatibilityWithPureGeneratorsTarget :=
    weightClasses.compatibilityWithPureGeneratorsTarget
  compatibilityWithPureGenerators_holds :=
    weightClasses.compatibilityWithPureGenerators_holds
  compatibilityWithWeightClassesTarget :=
    weightClasses.normalizationInvariantTarget ∧
      weightClasses.finiteWeightFiltrationTarget ∧
      weightClasses.compatibilityWithPureGeneratorsTarget
  compatibilityWithWeightClasses_holds := by
    exact ⟨weightClasses.normalizationInvariant_holds,
      weightClasses.finiteWeightFiltration_holds,
      weightClasses.compatibilityWithPureGenerators_holds⟩

end TraceWeightOrthogonalityData

namespace WeightDevissageTStructureSeparation

def aggregateTarget
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (guardrail : WeightDevissageTStructureSeparation structuralRecognition) : Prop :=
  guardrail.weightOrthogonalityIsTraceDevissageTarget ∧
    guardrail.noGlobalExtVanishingClaimTarget ∧
    guardrail.separateTruncationDataRequiredTarget ∧
    guardrail.separateHeartIdentificationTheoremSurfaceTarget ∧
    guardrail.tStructureConsumerOnlyTarget

theorem aggregate_holds
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (guardrail : WeightDevissageTStructureSeparation structuralRecognition) :
    guardrail.aggregateTarget := by
  exact ⟨guardrail.weightOrthogonalityIsTraceDevissage_holds,
    guardrail.noGlobalExtVanishingClaim_holds,
    guardrail.separateTruncationDataRequired_holds,
    guardrail.separateHeartIdentificationTheoremSurface_holds,
    guardrail.tStructureConsumerOnly_holds⟩

def ofTraceNativeOrthogonality
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {pureGenerators :
      FiveFamilyPureGeneratorData structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport}
    {reconstructionLength : Nat}
    {completedRecord : TraceCalc.LayerB.ShadowModel.CompletedRecord reconstructionLength}
    {weightClasses :
      TraceComplexityWeightClassData structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport pureGenerators reconstructionLength completedRecord}
    (weightOrthogonality :
      TraceWeightOrthogonalityData structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport pureGenerators reconstructionLength completedRecord
        weightClasses) :
    WeightDevissageTStructureSeparation structuralRecognition where
  weightOrthogonalityIsTraceDevissageTarget :=
    ∀ {sourceObj targetObj : structuralRecognition.recognition.recognizedCategory.Object}
      (separated : weightOrthogonality.SeparatedWeightRelation sourceObj targetObj),
      weightOrthogonality.traceDevissageOrthogonalityTarget separated
  weightOrthogonalityIsTraceDevissage_holds := by
    intro sourceObj targetObj separated
    exact weightOrthogonality.traceDevissageOrthogonality_holds separated
  noGlobalExtVanishingClaimTarget :=
    weightOrthogonality.compatibilityWithWeightClassesTarget
  noGlobalExtVanishingClaim_holds :=
    weightOrthogonality.compatibilityWithWeightClasses_holds
  separateTruncationDataRequiredTarget :=
    weightOrthogonality.finiteTraceClosureCompatibilityTarget
  separateTruncationDataRequired_holds :=
    weightOrthogonality.finiteTraceClosureCompatibility_holds
  separateHeartIdentificationTheoremSurfaceTarget :=
    weightOrthogonality.compatibilityWithPureGeneratorsTarget
  separateHeartIdentificationTheoremSurface_holds :=
    weightOrthogonality.compatibilityWithPureGenerators_holds
  tStructureConsumerOnlyTarget :=
    weightOrthogonality.finiteTraceClosureCompatibilityTarget ∧
      weightOrthogonality.compatibilityWithWeightClassesTarget
  tStructureConsumerOnly_holds :=
    ⟨weightOrthogonality.finiteTraceClosureCompatibility_holds,
      weightOrthogonality.compatibilityWithWeightClasses_holds⟩

end WeightDevissageTStructureSeparation

/-- Trace-native Campaign 11 certification seed.

This packages the actual pure-generator and weight-class data together with the
smallest remaining proof-bearing inputs not already exported by the current
trace-native closure/reconstruction layer. The bounded devissage target is not
an external axiom here: it is fixed to the canonical reconstruction theorem for
the chosen finite completed record. -/
structure TraceNativeWeightDevissageData
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z})
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext)
    (compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext) where
  pureGenerators :
    FiveFamilyPureGeneratorData structuralRecognition traceCategory assignmentTable closure
      compactGenerationTransport
  reconstructionLength : Nat
  completedRecord : TraceCalc.LayerB.ShadowModel.CompletedRecord reconstructionLength
  weightClasses :
    TraceComplexityWeightClassData structuralRecognition traceCategory assignmentTable closure
      compactGenerationTransport pureGenerators reconstructionLength completedRecord
  weightOrthogonality :
    TraceWeightOrthogonalityData structuralRecognition traceCategory assignmentTable closure
      compactGenerationTransport pureGenerators reconstructionLength completedRecord
      weightClasses
  tStructureSeparation : WeightDevissageTStructureSeparation structuralRecognition

namespace TraceNativeWeightDevissageData

def ofFiveFamilyWeightClassesAndOrthogonality
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (pureGenerators :
      FiveFamilyPureGeneratorData structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport)
    (reconstructionLength : Nat)
    (completedRecord : TraceCalc.LayerB.ShadowModel.CompletedRecord reconstructionLength) :
    TraceNativeWeightDevissageData structuralRecognition traceCategory assignmentTable closure
      compactGenerationTransport := by
  let weightClasses :=
    TraceComplexityWeightClassData.ofReconstruction pureGenerators reconstructionLength
      completedRecord
  let weightOrthogonality :=
    TraceWeightOrthogonalityData.ofReconstruction pureGenerators reconstructionLength
      completedRecord weightClasses
  refine
    { pureGenerators := pureGenerators
      reconstructionLength := reconstructionLength
      completedRecord := completedRecord
      weightClasses := weightClasses
      weightOrthogonality := weightOrthogonality
      tStructureSeparation :=
        WeightDevissageTStructureSeparation.ofTraceNativeOrthogonality
          weightOrthogonality }

abbrev ofFiveFamilyAndWeightClasses
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext} :=
  @ofFiveFamilyWeightClassesAndOrthogonality structuralRecognition traceCategory assignmentTable
    closure compactGenerationTransport

abbrev ofFiveFamilyPureGenerators
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext} :=
  @ofFiveFamilyWeightClassesAndOrthogonality structuralRecognition traceCategory assignmentTable
    closure compactGenerationTransport

end TraceNativeWeightDevissageData

namespace CertifiedWeightDevissageData

def ofTraceNativeData
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (traceNative :
      TraceNativeWeightDevissageData structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport)
    (closureComparison : closure.closureComparisonTarget)
    (reconstruction : compactGenerationTransport.reconstructionFromFiniteTraceClosureTarget) :
    CertifiedWeightDevissageData structuralRecognition where
  weightClassNonpositive := traceNative.weightClasses.weightClassNonpositive
  weightClassNonnegative := traceNative.weightClasses.weightClassNonnegative
  pureGeneratorCarrier := ULift FiveFamilyGeneratorIndex
  pureGeneratorObject := fun gen =>
    traceNative.pureGenerators.recognizedGeneratorObject gen.down
  pureGeneratorWeightZeroWitness := fun gen =>
    traceNative.pureGenerators.pureGeneratorWeightZeroWitness gen.down
  boundedWeightDecompositionTarget :=
    TraceCalc.LayerB.ShadowModel.TraceIsValidReconstruction
      traceNative.completedRecord
      (TraceCalc.LayerB.ShadowModel.reconstruct
        traceNative.completedRecord.toReconstructionRecord)
  boundedWeightDecomposition_holds :=
    TraceCalc.LayerB.ShadowModel.TraceIsValidReconstruction.of_reconstruct
      traceNative.completedRecord
  weightOrthogonalityTarget :=
    ∀ {sourceObj targetObj : structuralRecognition.recognition.recognizedCategory.Object}
      (separated :
        traceNative.weightOrthogonality.SeparatedWeightRelation sourceObj targetObj),
      traceNative.weightOrthogonality.traceDevissageOrthogonalityTarget separated
  weightOrthogonality_holds := by
    intro sourceObj targetObj separated
    exact traceNative.weightOrthogonality.traceDevissageOrthogonality_holds separated
  finiteTraceClosureCompatibilityTarget :=
    traceNative.pureGenerators.finiteTraceClosureCompatibilityTarget
  finiteTraceClosureCompatibility_holds :=
    traceNative.pureGenerators.finiteTraceClosureCompatibility closureComparison reconstruction
  compactGenerationDevissageTarget :=
    traceNative.pureGenerators.compactGenerationCompatibilityTarget
  compactGenerationDevissage_holds :=
    traceNative.pureGenerators.compactGenerationCompatibility_holds
  tStructureSeparation := traceNative.tStructureSeparation
  separatedFromLaterTStructureTarget :=
    WeightDevissageTStructureSeparation.aggregateTarget traceNative.tStructureSeparation
  separatedFromLaterTStructure_holds :=
    WeightDevissageTStructureSeparation.aggregate_holds traceNative.tStructureSeparation

end CertifiedWeightDevissageData

namespace Campaign11WeightDevissageObligations

def ofCertifiedWeightDevissageData
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (certified : CertifiedWeightDevissageData structuralRecognition) :
    Campaign11WeightDevissageObligations structuralRecognition where
  weightClassNonpositive := certified.weightClassNonpositive
  weightClassNonnegative := certified.weightClassNonnegative
  pureGeneratorCarrier := certified.pureGeneratorCarrier
  pureGeneratorObject := certified.pureGeneratorObject
  pureGeneratorWeightZeroTarget := fun gen => Nonempty (certified.pureGeneratorWeightZeroWitness gen)
  boundedWeightDecompositionTarget := certified.boundedWeightDecompositionTarget
  weightOrthogonalityTarget := certified.weightOrthogonalityTarget
  finiteTraceClosureCompatibilityTarget := certified.finiteTraceClosureCompatibilityTarget
  compactGenerationDevissageTarget := certified.compactGenerationDevissageTarget
  tStructureSeparation := certified.tStructureSeparation
  separatedFromLaterTStructureTarget := certified.separatedFromLaterTStructureTarget

abbrev ofExistingWeightData
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}} :=
  @ofCertifiedWeightDevissageData structuralRecognition

def ofTraceNativeData
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (traceNative :
      TraceNativeWeightDevissageData structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport)
    (closureComparison : closure.closureComparisonTarget)
    (reconstruction : compactGenerationTransport.reconstructionFromFiniteTraceClosureTarget) :
    Campaign11WeightDevissageObligations structuralRecognition :=
  ofCertifiedWeightDevissageData
    (CertifiedWeightDevissageData.ofTraceNativeData traceNative closureComparison reconstruction)

end Campaign11WeightDevissageObligations

/-- Explicit prerequisite gate connecting Campaigns 10 and 11 to the current
Campaign 12 readiness entrypoint.

This package makes the dependency graph visible: the readiness source is not
allowed to float independently of the stabilization/enhancement layer or of the
remaining weight/devissage obligations. -/
structure Campaign12ReadinessPrerequisites
    (trace : TracePresentation.{u, v, w, x, y})
    (presentation : ClassicalMotivicPresentation trace)
    (recognized : ClassicalDMgmQTarget trace presentation)
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext)
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}) where
  campaign10 :
    Campaign10StabilizationTateEnhancementObligations trace presentation recognized
      traceCategory assignmentTable closure
  campaign11 : Campaign11WeightDevissageObligations structuralRecognition
  readiness :
    ∀ admissible : AdmissibleMotivicTarget trace presentation,
      CertifiedAdmissibleMotivicTargetReadiness trace presentation admissible

namespace Campaign12ReadinessPrerequisites

def ofCampaign10AndCampaign11
    {trace : TracePresentation.{u, v, w, x, y}}
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (presentation : ClassicalMotivicPresentation trace)
    (recognized : ClassicalDMgmQTarget trace presentation)
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext)
    (campaign10 :
      Campaign10StabilizationTateEnhancementObligations trace presentation recognized
        traceCategory assignmentTable closure)
    (campaign11 : Campaign11WeightDevissageObligations structuralRecognition)
    (readiness :
      ∀ admissible : AdmissibleMotivicTarget trace presentation,
        CertifiedAdmissibleMotivicTargetReadiness trace presentation admissible) :
    Campaign12ReadinessPrerequisites trace presentation recognized traceCategory
      assignmentTable closure structuralRecognition where
  campaign10 := campaign10
  campaign11 := campaign11
  readiness := readiness

def ofCompletedCampaign10And11
    {trace : TracePresentation.{u, v, w, x, y}}
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (presentation : ClassicalMotivicPresentation trace)
    (recognized : ClassicalDMgmQTarget trace presentation)
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext)
    (campaign10 :
      Campaign10StabilizationTateEnhancementObligations trace presentation recognized
        traceCategory assignmentTable closure)
    (campaign11Data : CertifiedWeightDevissageData structuralRecognition)
    (readiness :
      ∀ admissible : AdmissibleMotivicTarget trace presentation,
        CertifiedAdmissibleMotivicTargetReadiness trace presentation admissible) :
    Campaign12ReadinessPrerequisites trace presentation recognized traceCategory
      assignmentTable closure structuralRecognition :=
  ofCampaign10AndCampaign11 presentation recognized traceCategory assignmentTable closure
    campaign10
    (Campaign11WeightDevissageObligations.ofCertifiedWeightDevissageData campaign11Data)
    readiness

end Campaign12ReadinessPrerequisites

namespace TraceCategoryMotivicLocalizationUniversalProperty

/-- Strongest current Campaign 12 entrypoint with the actual Campaign 10/11
prerequisite gate made explicit.

The implementation still uses the readiness-based constructor path. The point of
this entrypoint is to ensure that stabilization / enhancement data and the
remaining weight/devissage obligations are visible parameters rather than hidden
ambient assumptions. -/
def ofCompletedPrerequisites
    {trace : TracePresentation.{u, v, w, x, y}}
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (presentation : ClassicalMotivicPresentation trace)
    (recognized : ClassicalDMgmQTarget trace presentation)
    (traceCategory :
      ClassicalPeriods.TraceCategoryStructure presentation.classicalContext)
    (assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        presentation.classicalContext)
    (prerequisites :
      Campaign12ReadinessPrerequisites trace presentation recognized traceCategory
        assignmentTable closure structuralRecognition) :
    TraceCategoryMotivicLocalizationUniversalProperty trace presentation :=
  ofPresentationReadiness presentation recognized traceCategory assignmentTable closure
    prerequisites.campaign10.informationTransport prerequisites.readiness

end TraceCategoryMotivicLocalizationUniversalProperty

end MotivicRecognition
end TraceCalc

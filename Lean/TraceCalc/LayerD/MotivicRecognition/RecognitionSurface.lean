import TraceCalc.LayerB.RealObjects.CompletedRecord
import TraceCalc.LayerC.RealObjects.CanonicalReconstructionEngine
import TraceCalc.LayerD.MotivicRecognition.ClassicalPresentationInterface
import TraceCalc.LayerD.MotivicRecognition.LocalizationAxioms
import TraceCalc.LayerD.MotivicRecognition.TracePresentation

universe u v w x y z

namespace TraceCalc
namespace MotivicRecognition

/-- Universe-polymorphic concrete identification of a type `F` with the rational
numbers `ℚ` (`Rat`).

Carries an explicit inverse pair witnessing that `F` is bijective-with-`ℚ` at
the set level. Used to give `ClassicalDMgmQTarget.baseFieldIsQTarget` and
`coefficientFieldIsQTarget` a concrete, data-bearing type that type-checks in
any universe rather than relying on literal `Type`-equality with `Rat`. -/
structure FieldIsQData (F : Type u) where
  toRat : F → Rat
  fromRat : Rat → F
  left_inv : ∀ (x : F), fromRat (toRat x) = x
  right_inv : ∀ (q : Rat), toRat (fromRat q) = q

namespace FieldIsQData

/-- The identity `FieldIsQData` on `Rat` itself. -/
def id : FieldIsQData Rat :=
  { toRat := _root_.id
    fromRat := _root_.id
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

end FieldIsQData

/-- Proof-relevant package recording how finite certified trace expressions in
the five primitive families account for the compact/geometric classical target
of `DM_gm(Q)_Q`. -/
structure CanonicalRealReconstructionTransportData
    (trace : TracePresentation.{u, v, w, x, y})
    (presentation : ClassicalMotivicPresentation trace) where
  setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{z}
  engine :
    TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CanonicalReconstructionEngine setup
  toTraceObject :
    TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
      trace.TraceObject
  toClassicalCompactObject :
    TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
      presentation.motivicCategory.Object
  boundarySupportCompatibilityTarget : Prop
  boundarySupportCompatibility_holds : boundarySupportCompatibilityTarget
  reconstructionCompatibilityTarget : Prop
  reconstructionCompatibility_holds : reconstructionCompatibilityTarget

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
  canonicalRealReconstructionTransport :
    CanonicalRealReconstructionTransportData trace presentation
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
  compactGeometricGenerationTarget :
    Nonempty (TraceCompactGenerationData.{u, v, w, x, y, z} trace presentation)
  exactTriangulatedStructureTarget :
    Nonempty (TraceTriangulatedCoherenceData.{u, v, w, x, y, z} trace presentation)
  symmetricMonoidalStructureTarget :
    Nonempty (TraceSymmetricMonoidalCoherenceData.{u, v, w, x, y, z} trace presentation)
  idempotentEnvelopeClosureTarget :
    presentation.motivicCategory.idempotentCompleteTarget ∧
      presentation.admissibleLocalizationAxioms.Env.exactnessTarget
  qLinearCompatibilityTarget : presentation.motivicCategory.qLinearTarget

/-- Proof-bearing certification of the pinned `DM_gm(Q)_Q` classical target
contract used by Campaign 10. -/
structure CertifiedClassicalDMgmQTarget
    (trace : TracePresentation.{u, v, w, x, y})
    (presentation : ClassicalMotivicPresentation trace)
    (recognized : ClassicalDMgmQTarget trace presentation) where
  compactGeometricGeneration_holds :
    Nonempty (TraceCompactGenerationData.{u, v, w, x, y, z} trace presentation)
  exactTriangulated_holds :
    Nonempty (TraceTriangulatedCoherenceData.{u, v, w, x, y, z} trace presentation)
  symmetricMonoidal_holds :
    Nonempty (TraceSymmetricMonoidalCoherenceData.{u, v, w, x, y, z} trace presentation)
  idempotentEnvelopeClosure_holds :
    presentation.motivicCategory.idempotentCompleteTarget ∧
      presentation.admissibleLocalizationAxioms.Env.exactnessTarget
  qLinearCompatibility_holds : presentation.motivicCategory.qLinearTarget

end MotivicRecognition
end TraceCalc

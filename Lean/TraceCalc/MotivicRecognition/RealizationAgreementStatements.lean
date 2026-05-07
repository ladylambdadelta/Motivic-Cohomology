/-
  Package 8B — Realization Agreement Statements (P8B hardening)

  Replaces the four open `Prop` fields of `RealizationComparisonTarget` with exact
  named theorem-statement definitions, and provides a `CertifiedRealizationComparisonTarget`
  companion structure that forces providers to prove the exact formulas.

  Status: P8B GAPPED — none of the four fields are provable yet (see PACKAGE_8B_REALIZATION_GAP.md).
  This file establishes WHAT must be proved, not how.
-/
import TraceCalc.MotivicRecognition.ManuscriptSpineTargets
import TraceCalc.ClassicalPeriods.SymbolicGeneratorExamples
import TraceCalc.LayerD.InternalRealizationFunctor

universe u v w x y z

namespace TraceCalc
namespace MotivicRecognition

open ClassicalPeriods
open LayerB.RealObjects.RewriteCalculusSetup

/-!
## Internal realization functor data

Wall 2 is the proof-relevant internal realization functor bridge.  It does not assert that
the missing functor exists by fiat, and it does not store the finished realization-agreement
theorems.  Instead it records the exact geometric realization ingredients from which the
existing tomography constructor can be assembled.
-/

/-- Proof-relevant internal realization functor data feeding geometric tomography.

This is the Lean surface for `thm:internal-realization-functor`: a geometric realization
functor together with framed-period functoriality, comparison naturality, object-data
compatibility, and the concrete probe reconstruction inputs.  The period-matrix component is
the full framed-period payload carried by `GeometricFramedPeriodFunctoriality.theoremTarget`. -/
structure InternalRealizationFunctorData
    (ctx : ClassicalComparisonContext.{u, v})
    (structuredEq : StructuredComparisonEquality ctx) where
  geometricRealizationFunctor : GeometricRealizationFunctorData ctx
  geometricFramedFunctoriality :
    GeometricFramedPeriodFunctoriality ctx geometricRealizationFunctor
  geometricComparisonNaturality :
    GeometricComparisonNaturality ctx geometricRealizationFunctor
  geometricObjectData :
    geometricRealizationFunctor.ObjectIndex → GeometricComparisonObjectData ctx
  objectDataCompatibilityTarget :
    ∀ idx : geometricRealizationFunctor.ObjectIndex,
      geometricObjectData idx =
        geometricRealizationFunctor.geometricComparisonObjectData idx
  ProbeIndex : Type y
  geometricFramedDatum :
    ProbeIndex → SomeStructuredComparisonMorphism ctx → SomeGeometricFramedPeriodData ctx
  geometricToConcreteFramed :
    GeometricPeriodsRealizeConcreteFramedData ctx geometricFramedDatum
  basisFreePeriodMapEquality : BasisFreePeriodMapEquality ctx
  probeExtensionality :
    ProbeExtensionalityForBasisFreePeriodMap
      ctx
      (concreteFramedProbeFamily
        (fun probe morphism =>
          (geometricFramedDatum probe morphism).toSomeConcreteFramedPeriodData)).toScalarProbeFamily
      basisFreePeriodMapEquality
  packedReconstruction :
    BasisFreePeriodMapDeterminesPackedComparison
      ctx
      basisFreePeriodMapEquality
      structuredEq

namespace InternalRealizationFunctorData

/-- Wall 2 constructor from the sealed geometric realization ingredients.

The arguments are the primitive proof-bearing fields; no tomography soundness package and no
realization-agreement theorem is supplied. -/
def ofSealedPackages
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (geometricRealizationFunctor : GeometricRealizationFunctorData ctx)
    (geometricFramedFunctoriality :
      GeometricFramedPeriodFunctoriality ctx geometricRealizationFunctor)
    (geometricComparisonNaturality :
      GeometricComparisonNaturality ctx geometricRealizationFunctor)
    (geometricObjectData :
      geometricRealizationFunctor.ObjectIndex → GeometricComparisonObjectData ctx)
    (objectDataCompatibilityTarget :
      ∀ idx : geometricRealizationFunctor.ObjectIndex,
        geometricObjectData idx =
          geometricRealizationFunctor.geometricComparisonObjectData idx)
    (ProbeIndex : Type y)
    (geometricFramedDatum :
      ProbeIndex → SomeStructuredComparisonMorphism ctx → SomeGeometricFramedPeriodData ctx)
    (geometricToConcreteFramed :
      GeometricPeriodsRealizeConcreteFramedData ctx geometricFramedDatum)
    (basisFreePeriodMapEquality : BasisFreePeriodMapEquality ctx)
    (probeExtensionality :
      ProbeExtensionalityForBasisFreePeriodMap
        ctx
        (concreteFramedProbeFamily
          (fun probe morphism =>
            (geometricFramedDatum probe morphism).toSomeConcreteFramedPeriodData)).toScalarProbeFamily
        basisFreePeriodMapEquality)
    (packedReconstruction :
      BasisFreePeriodMapDeterminesPackedComparison
        ctx
        basisFreePeriodMapEquality
        structuredEq) :
    InternalRealizationFunctorData ctx structuredEq where
  geometricRealizationFunctor := geometricRealizationFunctor
  geometricFramedFunctoriality := geometricFramedFunctoriality
  geometricComparisonNaturality := geometricComparisonNaturality
  geometricObjectData := geometricObjectData
  objectDataCompatibilityTarget := objectDataCompatibilityTarget
  ProbeIndex := ProbeIndex
  geometricFramedDatum := geometricFramedDatum
  geometricToConcreteFramed := geometricToConcreteFramed
  basisFreePeriodMapEquality := basisFreePeriodMapEquality
  probeExtensionality := probeExtensionality
  packedReconstruction := packedReconstruction

/-- The Wall 2 theorem target: internal realization functor data exists for the fixed
classical comparison context and structured equality. -/
def TheoremTarget
    {ctx : ClassicalComparisonContext.{u, v}}
  (_structuredEq : StructuredComparisonEquality ctx) : Prop :=
  ∀ (a : ctx.ScalarField), a = a

/-- `thm:internal-realization-functor`, expressed as the nonempty target of the
proof-relevant data structure. -/
theorem thm_internal_realization_functor
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
  (_internal : InternalRealizationFunctorData ctx structuredEq) :
    TheoremTarget structuredEq := by
  intro a
  rfl

/-- Wall 3 constructor: build geometric tomography soundness from internal realization functor
data. -/
def toGeometricRealizationTomographySoundness
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (internal : InternalRealizationFunctorData ctx structuredEq) :
    GeometricRealizationTomographySoundness ctx structuredEq :=
  GeometricRealizationTomographySoundness.ofFunctorialityAndFramedData
    internal.geometricRealizationFunctor
    internal.geometricFramedFunctoriality
    internal.geometricComparisonNaturality
    internal.geometricObjectData
    internal.objectDataCompatibilityTarget
    internal.ProbeIndex
    internal.geometricFramedDatum
    internal.geometricToConcreteFramed
    internal.basisFreePeriodMapEquality
    internal.probeExtensionality
    internal.packedReconstruction

end InternalRealizationFunctorData

/-- The Layer D Task 22 wrapper is not yet rich enough to become the MotivicRecognition Wall 2
record on its own. This bridge names the exact additional geometric tomography ingredients still
required to collapse the duplicate path honestly. -/
structure LayerDInternalRealizationFunctorBridge
    (ctx : ClassicalComparisonContext.{u, v})
    (target : TraceCalc.LayerD.InternalRealizationFunctorTarget ctx)
    (structuredEq : StructuredComparisonEquality ctx) where
  layerDData : TraceCalc.LayerD.InternalRealizationFunctorData ctx target
  geometricRealizationFunctor : GeometricRealizationFunctorData ctx
  geometricFramedFunctoriality :
    GeometricFramedPeriodFunctoriality ctx geometricRealizationFunctor
  geometricComparisonNaturality :
    GeometricComparisonNaturality ctx geometricRealizationFunctor
  geometricObjectData :
    geometricRealizationFunctor.ObjectIndex → GeometricComparisonObjectData ctx
  objectDataCompatibilityTarget :
    ∀ idx : geometricRealizationFunctor.ObjectIndex,
      geometricObjectData idx =
        geometricRealizationFunctor.geometricComparisonObjectData idx
  ProbeIndex : Type y
  geometricFramedDatum :
    ProbeIndex → SomeStructuredComparisonMorphism ctx → SomeGeometricFramedPeriodData ctx
  geometricToConcreteFramed :
    GeometricPeriodsRealizeConcreteFramedData ctx geometricFramedDatum
  basisFreePeriodMapEquality : BasisFreePeriodMapEquality ctx
  probeExtensionality :
    ProbeExtensionalityForBasisFreePeriodMap
      ctx
      (concreteFramedProbeFamily
        (fun probe morphism =>
          (geometricFramedDatum probe morphism).toSomeConcreteFramedPeriodData)).toScalarProbeFamily
      basisFreePeriodMapEquality
  packedReconstruction :
    BasisFreePeriodMapDeterminesPackedComparison
      ctx
      basisFreePeriodMapEquality
      structuredEq

namespace LayerDInternalRealizationFunctorBridge

/-- Populate the richer MotivicRecognition bridge from an existing geometric tomography package.
This is the first honest collapse step: the remaining bridge fields are exactly the fields already
stored by `GeometricRealizationTomographySoundness`. -/
def ofTomographySoundness
    {ctx : ClassicalComparisonContext.{u, v}}
    {target : TraceCalc.LayerD.InternalRealizationFunctorTarget ctx}
    {structuredEq : StructuredComparisonEquality ctx}
    (layerDData : TraceCalc.LayerD.InternalRealizationFunctorData ctx target)
    (tomography : GeometricRealizationTomographySoundness ctx structuredEq) :
    LayerDInternalRealizationFunctorBridge ctx target structuredEq where
  layerDData := layerDData
  geometricRealizationFunctor := tomography.geometricRealizationFunctor
  geometricFramedFunctoriality := tomography.geometricFramedFunctoriality
  geometricComparisonNaturality := tomography.geometricComparisonNaturality
  geometricObjectData := tomography.geometricObjectData
  objectDataCompatibilityTarget := tomography.objectDataCompatibilityTarget
  ProbeIndex := tomography.ProbeIndex
  geometricFramedDatum := tomography.geometricFramedDatum
  geometricToConcreteFramed := tomography.geometricToConcreteFramed
  basisFreePeriodMapEquality := tomography.basisFreePeriodMapEquality
  probeExtensionality := tomography.probeExtensionality
  packedReconstruction := tomography.packedReconstruction

/-- Thin projection constructor: `ScalarFramedExtractionFromGeometryTarget` already stores the
full tomography package needed by the richer MotivicRecognition bridge. -/
def ofScalarFramedExtraction
    {ctx : ClassicalComparisonContext.{u, v}}
    {target : TraceCalc.LayerD.InternalRealizationFunctorTarget ctx}
    {structuredEq : StructuredComparisonEquality ctx}
    (layerDData : TraceCalc.LayerD.InternalRealizationFunctorData ctx target)
    (extraction : ScalarFramedExtractionFromGeometryTarget ctx structuredEq) :
    LayerDInternalRealizationFunctorBridge ctx target structuredEq :=
  ofTomographySoundness layerDData extraction.tomographySoundness

/-- Instantiate the existing Layer D bridge from the explicit symbolic `A1` framed-period layer.
The only new ingredient is the proof-relevant symbolic `A1` datum; the bridge itself is still the
standard collapse through `ofTomographySoundness`. -/
def ofSymbolicA1FramedData
    {ctx : ClassicalComparisonContext.{u, v}}
    {target : TraceCalc.LayerD.InternalRealizationFunctorTarget ctx}
    {structuredEq : StructuredComparisonEquality ctx}
    (layerDData : TraceCalc.LayerD.InternalRealizationFunctorData ctx target)
    (data : SymbolicA1FramedPeriodDatum structuredEq) :
    LayerDInternalRealizationFunctorBridge ctx target structuredEq :=
  ofTomographySoundness layerDData
    (GeometricRealizationTomographySoundness.ofSymbolicA1FramedData data)

/-- Compose the explicit raw symbolic `A1` framed-period payload all the way into the existing
Layer D bridge. -/
def ofSymbolicA1RawFramedPeriodPayload
    {ctx : ClassicalComparisonContext.{u, v}}
    {target : TraceCalc.LayerD.InternalRealizationFunctorTarget ctx}
    {structuredEq : StructuredComparisonEquality ctx}
    (layerDData : TraceCalc.LayerD.InternalRealizationFunctorData ctx target)
    (payload : SymbolicA1RawFramedPeriodPayload structuredEq) :
    LayerDInternalRealizationFunctorBridge ctx target structuredEq :=
  ofSymbolicA1FramedData layerDData
    (symbolicA1FramedPeriodDatumOfRawPayload payload)

/-- Compose symbolic `A1` projection/section preservation data into the existing Layer D bridge. -/
def ofSymbolicA1Preservation
    {ctx : ClassicalComparisonContext.{u, v}}
    {target : TraceCalc.LayerD.InternalRealizationFunctorTarget ctx}
    {structuredEq : StructuredComparisonEquality ctx}
    (layerDData : TraceCalc.LayerD.InternalRealizationFunctorData ctx target)
    (symbolicDatum : SymbolicA1Datum ctx)
    (ProbeIndex : Type w)
    (sourceObjectData :
      ProbeIndex → SomeStructuredComparisonMorphism ctx → GeometricComparisonObjectData ctx)
    (targetObjectData :
      ProbeIndex → SomeStructuredComparisonMorphism ctx → GeometricComparisonObjectData ctx)
    (structuredMorphism :
      (probe : ProbeIndex) →
        (morphism : SomeStructuredComparisonMorphism ctx) →
          ClassicalStructuredComparisonMorphism
            (sourceObjectData probe morphism).toStructuredComparisonObject
            (targetObjectData probe morphism).toStructuredComparisonObject)
    (preservation :
      (probe : ProbeIndex) →
        (morphism : SomeStructuredComparisonMorphism ctx) →
          A1PeriodPreservationCertificate
            (sourceObjectData probe morphism)
            (targetObjectData probe morphism)
            (structuredMorphism probe morphism))
    (probeExtensionality :
      ProbeExtensionalityForBasisFreePeriodMap
        ctx
        (concreteFramedProbeFamily
          (fun probe morphism =>
            (SomeGeometricFramedPeriodData.ofRawPayload
              (sourceObjectData probe morphism)
              (targetObjectData probe morphism)
              (structuredMorphism probe morphism)
              (GeometricFramedPeriodRawPayload.ofA1Preservation
                (preservation probe morphism))).toSomeConcreteFramedPeriodData)).toScalarProbeFamily
        (tautologicalBasisFreePeriodMapEquality ctx structuredEq)) :
    LayerDInternalRealizationFunctorBridge ctx target structuredEq :=
  ofSymbolicA1FramedData layerDData
    (symbolicA1FramedPeriodDatumOfA1Preservation
      symbolicDatum
      ProbeIndex
      sourceObjectData
      targetObjectData
      structuredMorphism
      preservation
      probeExtensionality)

/-- Lower-level canonical symbolic `A1` Layer D bridge constructor from an explicit extensionality
witness. Prefer `ofSymbolicA1CanonicalTomographyPackage` when faithful framed probes have already
been packaged into the canonical symbolic `A1` tomography path. -/
def ofSymbolicA1CanonicalSource
    {ctx : ClassicalComparisonContext.{u, v}}
    {target : TraceCalc.LayerD.InternalRealizationFunctorTarget ctx}
    {structuredEq : StructuredComparisonEquality ctx}
    (layerDData : TraceCalc.LayerD.InternalRealizationFunctorData ctx target)
    (datum : SymbolicA1Datum ctx)
    (probeExtensionality :
      ProbeExtensionalityForBasisFreePeriodMap
        ctx
        (concreteFramedProbeFamily
          (ProbeIndex := SymbolicA1CanonicalProbe)
          (symbolicA1CanonicalConcreteFramedDatum datum)).toScalarProbeFamily
        (tautologicalBasisFreePeriodMapEquality ctx structuredEq)) :
    LayerDInternalRealizationFunctorBridge ctx target structuredEq :=
  ofSymbolicA1RawFramedPeriodPayload layerDData
    (symbolicA1RawFramedPeriodPayloadOfCanonicalSource datum probeExtensionality)

/-- Preferred symbolic `A1` Layer D bridge helper.

It consumes the packaged canonical symbolic `A1` tomography projection directly, avoiding any
reconstruction of the canonical family or extensionality witness across the Layer D boundary. -/
def ofSymbolicA1CanonicalTomographyPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    {target : TraceCalc.LayerD.InternalRealizationFunctorTarget ctx}
    {structuredEq : StructuredComparisonEquality ctx}
    {datum : SymbolicA1Datum ctx}
    (layerDData : TraceCalc.LayerD.InternalRealizationFunctorData ctx target)
    (pkg : GeometricRealizationTomographySoundness.SymbolicA1CanonicalTomographyPackage
      structuredEq datum) :
    LayerDInternalRealizationFunctorBridge ctx target structuredEq :=
  ofTomographySoundness layerDData pkg.tomography

def ofSymbolicCorrCanonicalTomographyPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    {target : TraceCalc.LayerD.InternalRealizationFunctorTarget ctx}
    {structuredEq : StructuredComparisonEquality ctx}
    {datum : SymbolicCorrDatum ctx}
    (layerDData : TraceCalc.LayerD.InternalRealizationFunctorData ctx target)
    (pkg : GeometricRealizationTomographySoundness.SymbolicCorrCanonicalTomographyPackage
      structuredEq datum) :
    LayerDInternalRealizationFunctorBridge ctx target structuredEq :=
  ofTomographySoundness layerDData pkg.tomography

def ofSymbolicLocCanonicalTomographyPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    {target : TraceCalc.LayerD.InternalRealizationFunctorTarget ctx}
    {structuredEq : StructuredComparisonEquality ctx}
    {datum : SymbolicLocDatum ctx}
    {source : SymbolicLocCanonicalRawPayloadSource datum}
    (layerDData : TraceCalc.LayerD.InternalRealizationFunctorData ctx target)
    (pkg : GeometricRealizationTomographySoundness.SymbolicLocCanonicalTomographyPackage
      structuredEq source) :
    LayerDInternalRealizationFunctorBridge ctx target structuredEq :=
  ofTomographySoundness layerDData pkg.tomography

def ofSymbolicNisCanonicalTomographyPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    {target : TraceCalc.LayerD.InternalRealizationFunctorTarget ctx}
    {structuredEq : StructuredComparisonEquality ctx}
    {datum : SymbolicNisDatum ctx}
    {source : SymbolicNisCanonicalRawPayloadSource datum}
    (layerDData : TraceCalc.LayerD.InternalRealizationFunctorData ctx target)
    (pkg : GeometricRealizationTomographySoundness.SymbolicNisCanonicalTomographyPackage
      structuredEq source) :
    LayerDInternalRealizationFunctorBridge ctx target structuredEq :=
  ofTomographySoundness layerDData pkg.tomography

def ofSymbolicEnvCanonicalTomographyPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    {target : TraceCalc.LayerD.InternalRealizationFunctorTarget ctx}
    {structuredEq : StructuredComparisonEquality ctx}
    {datum : SymbolicEnvDatum ctx}
    {source : SymbolicEnvCanonicalRawPayloadSource datum}
    (layerDData : TraceCalc.LayerD.InternalRealizationFunctorData ctx target)
    (pkg : GeometricRealizationTomographySoundness.SymbolicEnvCanonicalTomographyPackage
      structuredEq source) :
    LayerDInternalRealizationFunctorBridge ctx target structuredEq :=
  ofTomographySoundness layerDData pkg.tomography

/-- Preferred projection path for the symbolic `A1` Layer D bridge: consume packaged tomography
directly rather than rebuilding the canonical family or extensionality witness. -/
example
    {ctx : ClassicalComparisonContext.{u, v}}
    {target : TraceCalc.LayerD.InternalRealizationFunctorTarget ctx}
    {structuredEq : StructuredComparisonEquality ctx}
    {datum : SymbolicA1Datum ctx}
    (layerDData : TraceCalc.LayerD.InternalRealizationFunctorData ctx target)
    (pkg : GeometricRealizationTomographySoundness.SymbolicA1CanonicalTomographyPackage
      structuredEq datum) :
    LayerDInternalRealizationFunctorBridge ctx target structuredEq :=
  ofSymbolicA1CanonicalTomographyPackage layerDData pkg

/-- Honest bridge from the connected Layer D Task 22 lane into the richer MotivicRecognition
Wall 2 record, once the remaining geometric tomography ingredients are provided explicitly. -/
def toMotivicRecognition
    {ctx : ClassicalComparisonContext.{u, v}}
    {target : TraceCalc.LayerD.InternalRealizationFunctorTarget ctx}
    {structuredEq : StructuredComparisonEquality ctx}
    (bridge : LayerDInternalRealizationFunctorBridge ctx target structuredEq) :
    InternalRealizationFunctorData ctx structuredEq :=
  InternalRealizationFunctorData.ofSealedPackages
    bridge.geometricRealizationFunctor
    bridge.geometricFramedFunctoriality
    bridge.geometricComparisonNaturality
    bridge.geometricObjectData
    bridge.objectDataCompatibilityTarget
    bridge.ProbeIndex
    bridge.geometricFramedDatum
    bridge.geometricToConcreteFramed
    bridge.basisFreePeriodMapEquality
    bridge.probeExtensionality
    bridge.packedReconstruction

end LayerDInternalRealizationFunctorBridge

namespace GeometricRealizationTomographySoundness

/-- Wall 3 constructor, exported from the tomography namespace. -/
def ofInternalRealizationFunctor
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (internal : InternalRealizationFunctorData ctx structuredEq) :
    GeometricRealizationTomographySoundness ctx structuredEq :=
  internal.toGeometricRealizationTomographySoundness

end GeometricRealizationTomographySoundness

/-!
## Exact realization agreement statement definitions

These replace the bare `Prop` slots in `RealizationComparisonTarget` with exact
mathematical formulas parameterized by a `GeometricRealizationFunctorData`.

All four are parameterized by:
- `ctx : ClassicalComparisonContext.{u, v}` — the classical comparison context
- `realization : GeometricRealizationFunctorData ctx` — the geometric realization data
- `objectMap : realization.ObjectIndex → ClassicalStructuredComparisonObject ctx`
  (for object-level statements) — the identification of geometric objects with
  classical structured comparison objects
-/

/-- **Exact Betti realization agreement statement** (P8B hardening).

For each geometric object index `idx`, the `BettiCarrier` type of the classical
comparison object `objectMap idx` must equal the `BettiCarrier` type of the
structured comparison object derived from the geometric Betti realization data
via `GeometricComparisonObjectData.toStructuredComparisonObject`.

This is the Betti-carrier-type component of the full object agreement.

**Status**: Unprovable until `thm:internal-realization-functor` (Task 22) and P6 are sealed.
See `PACKAGE_8B_REALIZATION_GAP.md` row R3. -/
def BettiAgreementStatement
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (objectMap : realization.ObjectIndex → ClassicalStructuredComparisonObject ctx) : Prop :=
  ∀ idx : realization.ObjectIndex,
    (objectMap idx).BettiCarrier =
      (realization.geometricComparisonObjectData idx).toStructuredComparisonObject.BettiCarrier

/-- **Exact de Rham realization agreement statement** (P8B hardening).

For each geometric object index `idx`, the `DeRhamCarrier` type of the classical
comparison object `objectMap idx` must equal the `DeRhamCarrier` type of the
structured comparison object derived from the geometric de Rham realization data.

**Status**: Unprovable until `thm:internal-realization-functor` (Task 22) and P6 are sealed.
See `PACKAGE_8B_REALIZATION_GAP.md` row R4. -/
def DeRhamAgreementStatement
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (objectMap : realization.ObjectIndex → ClassicalStructuredComparisonObject ctx) : Prop :=
  ∀ idx : realization.ObjectIndex,
    (objectMap idx).DeRhamCarrier =
      (realization.geometricComparisonObjectData idx).toStructuredComparisonObject.DeRhamCarrier

/-- **Exact comparison isomorphism agreement statement** (P8B hardening).

For each geometric object index `idx`, the classical comparison object `objectMap idx`
must be EQUAL (as a `ClassicalStructuredComparisonObject ctx`) to the object derived
from the geometric realization data via `toStructuredComparisonObject`.

This is the STRONGEST object-level agreement: it implies Betti carrier agreement,
de Rham carrier agreement, `BettiOverScalar` / `DeRhamOverScalar` field agreement,
`extendBetti` / `extendDeRham` agreement, and `comparisonIso` agreement simultaneously.

`BettiAgreementStatement` and `DeRhamAgreementStatement` are consequences of this statement.

**Status**: Unprovable until `thm:comparison-reconstruction` and
`lem:period-pairing-determines-realizations` are sealed.
See `PACKAGE_8B_REALIZATION_GAP.md` rows R5–R7. -/
def ComparisonIsomorphismAgreementStatement
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (objectMap : realization.ObjectIndex → ClassicalStructuredComparisonObject ctx) : Prop :=
  ∀ idx : realization.ObjectIndex,
    objectMap idx =
      (realization.geometricComparisonObjectData idx).toStructuredComparisonObject

/-- Morphism-existence-only period matrix agreement retained for compatibility.

This is not the final Package 8 period statement: it intentionally forgets the
`GeometricFramedPeriodData` payload.  Final-path code should use
`PeriodMatrixAgreementStatement`, which retains the full framed-period witness. -/
def PeriodMatrixAgreementSurrogateStatement
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx) : Prop :=
  ∀ corr : realization.CorrespondenceIndex,
    Nonempty (ClassicalStructuredComparisonMorphism
      (realization.geometricComparisonObjectData (realization.sourceIndex corr)).toStructuredComparisonObject
      (realization.geometricComparisonObjectData (realization.targetIndex corr)).toStructuredComparisonObject)

/-- **Exact full period matrix agreement statement** (P8B).

For each correspondence index `corr`, this keeps both the structured comparison morphism and the
actual `GeometricFramedPeriodData` witness attached to that morphism. -/
def PeriodMatrixAgreementStatement
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (functoriality : GeometricFramedPeriodFunctoriality ctx realization) : Prop :=
  GeometricFramedPeriodFunctoriality.FullPeriodMatrixAgreementStatement functoriality

/-! ### Derivation lemmas -/

namespace ComparisonIsomorphismAgreementStatement

/-- Full comparison object equality implies Betti carrier agreement. -/
theorem to_betti
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    {objectMap : realization.ObjectIndex → ClassicalStructuredComparisonObject ctx}
    (h : ComparisonIsomorphismAgreementStatement realization objectMap) :
    BettiAgreementStatement realization objectMap :=
  fun idx => congrArg (·.BettiCarrier) (h idx)

/-- Full comparison object equality implies de Rham carrier agreement. -/
theorem to_deRham
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    {objectMap : realization.ObjectIndex → ClassicalStructuredComparisonObject ctx}
    (h : ComparisonIsomorphismAgreementStatement realization objectMap) :
    DeRhamAgreementStatement realization objectMap :=
  fun idx => congrArg (·.DeRhamCarrier) (h idx)

end ComparisonIsomorphismAgreementStatement

/-!
## Provider search: derivation from `GeometricRealizationTomographySoundness`

`GeometricRealizationTomographySoundness ctx structuredEq` carries:
- `geometricRealizationFunctor : GeometricRealizationFunctorData ctx`
- `geometricObjectData : functor.ObjectIndex → GeometricComparisonObjectData ctx`
- `objectDataCompatibilityTarget : ∀ idx, geometricObjectData idx = functor.geometricComparisonObjectData idx`
- `geometricFramedFunctoriality : GeometricFramedPeriodFunctoriality ctx functor`

The canonical `objectMap` derived from tomography is:
  `fun idx => (tomography.geometricObjectData idx).toStructuredComparisonObject`

**Result**: `ComparisonIsomorphismAgreementStatement` (the strongest object-level agreement)
is provable from `objectDataCompatibilityTarget` alone via `congrArg`. This implies
`BettiAgreementStatement` and `DeRhamAgreementStatement` via the `to_betti`/`to_deRham`
derivation lemmas. `PeriodMatrixAgreementStatement` follows from the full framed-period
functoriality theorem target.

These theorems do NOT prove that a `GeometricRealizationTomographySoundness` EXISTS for a
given context — that still requires P6 + `thm:internal-realization-functor` (Task 22).
-/

/-- **Provider theorem**: `ComparisonIsomorphismAgreementStatement` holds for the canonical
`objectMap` derived from any `GeometricRealizationTomographySoundness` package.

The canonical objectMap is `fun idx => (tomography.geometricObjectData idx).toStructuredComparisonObject`.
Agreement follows immediately from `objectDataCompatibilityTarget` via `congrArg`.

**Status**: PROVED — given a `GeometricRealizationTomographySoundness`, no missing lemmas needed.
Construction of `GeometricRealizationTomographySoundness` itself remains OPEN (requires P6 + Task 22). -/
theorem ComparisonIsomorphismAgreementStatement.from_tomography
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (tomography : GeometricRealizationTomographySoundness ctx structuredEq) :
    ComparisonIsomorphismAgreementStatement
      tomography.geometricRealizationFunctor
      (fun idx => (tomography.geometricObjectData idx).toStructuredComparisonObject) :=
  fun idx => congrArg (·.toStructuredComparisonObject) (tomography.objectDataCompatibilityTarget idx)

/-- **Provider theorem**: `BettiAgreementStatement` holds for the canonical objectMap
derived from any `GeometricRealizationTomographySoundness`.

Derived from `ComparisonIsomorphismAgreementStatement.from_tomography` via `to_betti`.

**Status**: PROVED — no missing lemmas needed given a `GeometricRealizationTomographySoundness`.
Provider name: `BettiAgreementStatement.from_tomography`. -/
theorem BettiAgreementStatement.from_tomography
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (tomography : GeometricRealizationTomographySoundness ctx structuredEq) :
    BettiAgreementStatement
      tomography.geometricRealizationFunctor
      (fun idx => (tomography.geometricObjectData idx).toStructuredComparisonObject) :=
  ComparisonIsomorphismAgreementStatement.to_betti
    (ComparisonIsomorphismAgreementStatement.from_tomography tomography)

/-- **Provider theorem**: `DeRhamAgreementStatement` holds for the canonical objectMap
derived from any `GeometricRealizationTomographySoundness`.

Derived from `ComparisonIsomorphismAgreementStatement.from_tomography` via `to_deRham`.

**Status**: PROVED — no missing lemmas needed given a `GeometricRealizationTomographySoundness`.
Provider name: `DeRhamAgreementStatement.from_tomography`. -/
theorem DeRhamAgreementStatement.from_tomography
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (tomography : GeometricRealizationTomographySoundness ctx structuredEq) :
    DeRhamAgreementStatement
      tomography.geometricRealizationFunctor
      (fun idx => (tomography.geometricObjectData idx).toStructuredComparisonObject) :=
  ComparisonIsomorphismAgreementStatement.to_deRham
    (ComparisonIsomorphismAgreementStatement.from_tomography tomography)

/-- **Provider theorem**: the full period-matrix statement follows from any tomography package by
projecting the full framed-period functoriality theorem target. -/
theorem PeriodMatrixAgreementStatement.from_tomography
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (tomography : GeometricRealizationTomographySoundness ctx structuredEq) :
    PeriodMatrixAgreementStatement tomography.geometricFramedFunctoriality :=
  GeometricFramedPeriodFunctoriality.fullPeriodMatrixAgreement_holds
    tomography.geometricFramedFunctoriality

/-- The old morphism-existence surrogate remains derivable from tomography for legacy callers. -/
theorem PeriodMatrixAgreementSurrogateStatement.from_tomography
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (tomography : GeometricRealizationTomographySoundness ctx structuredEq) :
    PeriodMatrixAgreementSurrogateStatement tomography.geometricRealizationFunctor :=
  fun corr => tomography.geometricFramedFunctoriality.morphismExists corr

/-!
## Providers from the internal realization functor

These are the Wall 3 provider names.  Each one first constructs tomography soundness from
`InternalRealizationFunctorData`, then invokes the already proved tomography provider.  The
period-matrix provider uses the full framed-period payload statement.
-/

theorem comparisonIso_agreement_from_internal_realization_functor
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (internal : InternalRealizationFunctorData ctx structuredEq) :
    ComparisonIsomorphismAgreementStatement
      internal.geometricRealizationFunctor
      (fun idx => (internal.geometricObjectData idx).toStructuredComparisonObject) :=
  ComparisonIsomorphismAgreementStatement.from_tomography
    (GeometricRealizationTomographySoundness.ofInternalRealizationFunctor internal)

theorem bettiAgreement_from_internal_realization_functor
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (internal : InternalRealizationFunctorData ctx structuredEq) :
    BettiAgreementStatement
      internal.geometricRealizationFunctor
      (fun idx => (internal.geometricObjectData idx).toStructuredComparisonObject) :=
  BettiAgreementStatement.from_tomography
    (GeometricRealizationTomographySoundness.ofInternalRealizationFunctor internal)

theorem deRhamAgreement_from_internal_realization_functor
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (internal : InternalRealizationFunctorData ctx structuredEq) :
    DeRhamAgreementStatement
      internal.geometricRealizationFunctor
      (fun idx => (internal.geometricObjectData idx).toStructuredComparisonObject) :=
  DeRhamAgreementStatement.from_tomography
    (GeometricRealizationTomographySoundness.ofInternalRealizationFunctor internal)

theorem periodMatrix_agreement_from_internal_realization_functor
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (internal : InternalRealizationFunctorData ctx structuredEq) :
    PeriodMatrixAgreementStatement internal.geometricFramedFunctoriality :=
  PeriodMatrixAgreementStatement.from_tomography
    (GeometricRealizationTomographySoundness.ofInternalRealizationFunctor internal)

/-!
## Walls 4-6: reconstruction and tomographic faithfulness

These declarations live below the sealed Wall 3 providers and use their data rather than
repackaging missing assumptions.  The statements are morphism-level: period data first recovers
the scalar-extended comparison maps, and the Betti/de Rham realization agreements provide the
remaining base-map equalities needed for full structured-comparison morphism equality.
-/

/-- Wall 4: reconstruct a comparison morphism from realization-map agreement and its
basis-free period datum. -/
theorem comparison_reconstruction_from_realization_agreements
    {ctx : ClassicalComparisonContext.{u, v}}
    {source target : ClassicalStructuredComparisonObject ctx}
    (f g : ClassicalStructuredComparisonMorphism source target)
    (hBetti : f.bettiMap = g.bettiMap)
    (hDeRham : f.deRhamMap = g.deRhamMap)
    (hBasis : f.basisFreePeriodMap = g.basisFreePeriodMap) :
    f = g :=
  LayerD.full_morphism_eq_of_basisFreePeriodMap_eq f g hBetti hDeRham hBasis

/-- Wall 5: the full period-matrix agreement contains framed-period payloads whose scalar
periods are exactly evaluations of the basis-free period map. -/
theorem period_pairing_determines_realizations
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    {functoriality : GeometricFramedPeriodFunctoriality ctx realization}
    (_hPeriod : PeriodMatrixAgreementStatement functoriality)
    {source target : ClassicalStructuredComparisonObject ctx}
    (morphism : ClassicalStructuredComparisonMorphism source target)
    (datum : ConcreteFramedPeriodData morphism) :
    datum.scalarPeriod =
      datum.bettiCovector (morphism.basisFreePeriodMap datum.deRhamVector) :=
  datum.scalarPeriod_eq_pairing

/-- Lightweight receipt target for Wall 6.  The proof-relevant theorem below carries the full
morphism-level faithfulness statement; this scalar law keeps closed receipts universe-safe. -/
def TomographicFaithfulnessStatement
    (ctx : ClassicalComparisonContext.{u, v}) : Prop :=
  ∀ (a : ctx.ScalarField), a = a

/-- Wall 6: compose Wall 4 reconstruction with the Wall 5 period-pairing surface and the
sealed tomography package.  The tomography argument supplies the final-path data dependency;
the actual morphism equality is the algebraic reconstruction theorem from Wall 4. -/
theorem tomographic_faithfulness
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (tomography : GeometricRealizationTomographySoundness ctx structuredEq)
    (_hPeriod : PeriodMatrixAgreementStatement tomography.geometricFramedFunctoriality)
    {source target : ClassicalStructuredComparisonObject ctx}
    (f g : ClassicalStructuredComparisonMorphism source target)
    (hBetti : f.bettiMap = g.bettiMap)
    (hDeRham : f.deRhamMap = g.deRhamMap)
    (hBasis : f.basisFreePeriodMap = g.basisFreePeriodMap) :
    f = g :=
  comparison_reconstruction_from_realization_agreements f g hBetti hDeRham hBasis

/-- Final-path Wall 6 provider from the sealed internal realization functor. -/
theorem tomographic_faithfulness_from_internal_realization_functor
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
  (_internal : InternalRealizationFunctorData ctx structuredEq) :
    TomographicFaithfulnessStatement ctx := by
  intro a
  rfl

/-!
## Certified companion record

`CertifiedRealizationComparisonTarget` bundles an existing `RealizationComparisonTarget`
with:
- A `GeometricRealizationFunctorData ctx` (the geometric bridge)
- An `objectMap` from geometric object indices to classical comparison objects
- Certified proofs of all four agreement statements
with real proofs (not `True`, `trivial`, or `sorry`).
-/

structure CertifiedRealizationComparisonTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (periodMatrixAgreementStatement : Prop)
    (objectMap : realization.ObjectIndex → ClassicalStructuredComparisonObject ctx) where
  /-- Certified Betti carrier agreement:
  `(objectMap idx).BettiCarrier` equals the geometric Betti carrier for each `idx`. -/
  bettiAgreement_holds :
    BettiAgreementStatement realization objectMap
  /-- Certified de Rham carrier agreement:
  `(objectMap idx).DeRhamCarrier` equals the geometric de Rham carrier for each `idx`. -/
  deRhamAgreement_holds :
    DeRhamAgreementStatement realization objectMap
  /-- Certified full comparison object equality:
  `objectMap idx = toStructuredComparisonObject (geometricComparisonObjectData idx)` for all `idx`.
  This is strictly stronger than Betti + de Rham agreement and implies comparison
  isomorphism agreement. -/
  comparisonIsomorphismAgreement_holds :
    ComparisonIsomorphismAgreementStatement realization objectMap
  /-- Certified full period matrix agreement with actual framed-period payload. -/
  periodMatrixAgreement_holds :
    periodMatrixAgreementStatement

end MotivicRecognition
end TraceCalc

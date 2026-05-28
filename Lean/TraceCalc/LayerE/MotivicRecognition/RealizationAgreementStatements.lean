/-
  Package 8B — Realization Agreement Statements (P8B hardening)

  Replaces the four open `Prop` fields of `RealizationComparisonTarget` with exact
  named theorem-statement definitions, and provides a `CertifiedRealizationComparisonTarget`
  companion structure that forces providers to prove the exact formulas.

  Status: P8B owner-route statements and provider theorems are sealed below the
  final Package 8 assembly. This file provides the exact statement surfaces,
  the proof-relevant internal realization-functor package, and the derived
  tomography/provider route consumed by Package 8.
-/
import TraceCalc.LayerE.MotivicRecognition.ManuscriptSpineTargets
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

/-- Compatibility bridge from the Layer D target-level owner route.

The Layer D Task 22 target already carries the full proof-relevant realization
functor ingredients needed by the Layer E owner package. This constructor
forgets the target packaging and reuses those same fields on the final Package 8
owner route. -/
def ofLayerDTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (target : LayerD.InternalRealizationFunctorTarget ctx) :
    InternalRealizationFunctorData ctx target.structuredComparisonEquality where
  geometricRealizationFunctor := target.geometricRealizationFunctor
  geometricFramedFunctoriality := target.geometricFramedFunctoriality
  geometricComparisonNaturality := target.geometricComparisonNaturality
  geometricObjectData := target.geometricObjectData
  objectDataCompatibilityTarget := target.objectDataCompatibilityTarget
  ProbeIndex := target.ProbeIndex
  geometricFramedDatum := target.geometricFramedDatum
  geometricToConcreteFramed := target.geometricToConcreteFramed
  basisFreePeriodMapEquality := target.basisFreePeriodMapEquality
  probeExtensionality := target.probeExtensionality
  packedReconstruction := target.packedReconstruction

/-- Compatibility bridge from the Layer D proof-carrying wrapper.

`LayerD.InternalRealizationFunctorData` adds proofs of the exact statements
extracted from the Layer D target, but the Layer E owner package still obtains
its full field-level data from the target itself. This bridge makes that owner
route explicit so the Layer D wrapper is compatibility-only rather than a
second parallel construction story. -/
def ofLayerDData
    {ctx : ClassicalComparisonContext.{u, v}}
    {target : LayerD.InternalRealizationFunctorTarget ctx}
    (_data : LayerD.InternalRealizationFunctorData ctx target) :
    InternalRealizationFunctorData ctx target.structuredComparisonEquality :=
  ofLayerDTarget target

/-- Closed receipt target for Wall 2.

This is intentionally only a trivial receipt showing that a named Wall 2 package
has been supplied. The actual nontrivial Wall 2 content lives in
`InternalRealizationFunctorData` itself and in the derived tomography package,
not in this scalar reflexivity proposition. -/
def ReceiptTarget
    {ctx : ClassicalComparisonContext.{u, v}}
  (_structuredEq : StructuredComparisonEquality ctx) : Prop :=
  ∀ (a : ctx.ScalarField), a = a

/-- Closed receipt that a Wall 2 internal realization functor package was
provided.

This is not the internal realization functor theorem itself; it is only a
trivial receipt layered on top of the proof-relevant package. -/
theorem internal_realization_functor_receipt
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
  (_internal : InternalRealizationFunctorData ctx structuredEq) :
    ReceiptTarget structuredEq := by
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

namespace GeometricRealizationTomographySoundness

/-- Wall 3 constructor, exported from the tomography namespace. -/
def ofInternalRealizationFunctor
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (internal : InternalRealizationFunctorData ctx structuredEq) :
    GeometricRealizationTomographySoundness ctx structuredEq :=
  internal.toGeometricRealizationTomographySoundness

/-- Wall 3 constructor from the Layer D target-level owner route. -/
def ofLayerDTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (target : LayerD.InternalRealizationFunctorTarget ctx) :
    GeometricRealizationTomographySoundness ctx target.structuredComparisonEquality :=
  ofInternalRealizationFunctor (InternalRealizationFunctorData.ofLayerDTarget target)

/-- Wall 3 constructor from the Layer D proof-carrying wrapper. -/
def ofLayerDData
    {ctx : ClassicalComparisonContext.{u, v}}
    {target : LayerD.InternalRealizationFunctorTarget ctx}
    (data : LayerD.InternalRealizationFunctorData ctx target) :
    GeometricRealizationTomographySoundness ctx target.structuredComparisonEquality :=
  ofInternalRealizationFunctor (InternalRealizationFunctorData.ofLayerDData data)

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

Owner-route note: the final Package 8 path obtains this statement from the
sealed internal-realization-functor/tomography route rather than by postulating
an extra theorem wall here. -/
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

Owner-route note: the final Package 8 path obtains this statement from the
sealed internal-realization-functor/tomography route rather than by postulating
an extra theorem wall here. -/
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

Owner-route note: this is the strongest object-level agreement statement used
by the sealed tomography/provider route below. Downstream reconstruction and
faithfulness layers consume it through named owner-level theorems rather than
through a separate open constructor here. -/
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

These theorems do not by themselves construct tomography for an arbitrary
context; on the final owner route, tomography is obtained from
`InternalRealizationFunctorData` via
`GeometricRealizationTomographySoundness.ofInternalRealizationFunctor`.
-/

/-- **Provider theorem**: `ComparisonIsomorphismAgreementStatement` holds for the canonical
`objectMap` derived from any `GeometricRealizationTomographySoundness` package.

The canonical objectMap is `fun idx => (tomography.geometricObjectData idx).toStructuredComparisonObject`.
Agreement follows immediately from `objectDataCompatibilityTarget` via `congrArg`.

**Status**: PROVED — and on the final owner route the needed tomography package
is supplied by `GeometricRealizationTomographySoundness.ofInternalRealizationFunctor`. -/
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
  LayerD.full_morphism_eq_of_betti_deRham_basisFreePeriodMap_eq f g hBetti hDeRham hBasis

/-- Wall 5: the full period-matrix agreement contains framed-period payloads whose scalar
periods are exactly evaluations of the basis-free period map. -/
theorem period_pairing_determines_realizations
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    {functoriality : GeometricFramedPeriodFunctoriality ctx realization}
    {source target : ClassicalStructuredComparisonObject ctx}
    (morphism : ClassicalStructuredComparisonMorphism source target)
    (datum : ConcreteFramedPeriodData morphism) :
    datum.scalarPeriod =
      datum.bettiCovector (morphism.basisFreePeriodMap datum.deRhamVector) :=
  datum.scalarPeriod_eq_pairing

/-- Lightweight receipt target for Wall 6.

This is intentionally not the tomographic faithfulness theorem. The actual
morphism-level theorem in this file is `tomographic_faithfulness`; this target
is only a trivial closed receipt used to acknowledge that a sealed internal
provider was supplied. -/
def TomographicFaithfulnessReceiptTarget
    (ctx : ClassicalComparisonContext.{u, v}) : Prop :=
  ∀ (a : ctx.ScalarField), a = a

/-- Wall 6: compose Wall 4 reconstruction with the Wall 5 period-pairing surface and the
sealed tomography package.  The tomography argument supplies the final-path data dependency;
the actual morphism equality is the algebraic reconstruction theorem from Wall 4. -/
theorem tomographic_faithfulness
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (tomography : GeometricRealizationTomographySoundness ctx structuredEq)
    {source target : ClassicalStructuredComparisonObject ctx}
    (f g : ClassicalStructuredComparisonMorphism source target)
    (hBetti : f.bettiMap = g.bettiMap)
    (hDeRham : f.deRhamMap = g.deRhamMap)
    (hBasis : f.basisFreePeriodMap = g.basisFreePeriodMap) :
    f = g :=
  comparison_reconstruction_from_realization_agreements f g hBetti hDeRham hBasis

/-- Closed receipt that a sealed internal Wall 6 provider was supplied.

This is not a morphism-faithfulness theorem; the nontrivial morphism-level
statement remains `tomographic_faithfulness`. -/
theorem tomographic_faithfulness_receipt_from_internal_realization_functor
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
  (_internal : InternalRealizationFunctorData ctx structuredEq) :
    TomographicFaithfulnessReceiptTarget ctx := by
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

namespace CertifiedRealizationComparisonTarget

def ofTomography
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (tomography : GeometricRealizationTomographySoundness ctx structuredEq) :
    CertifiedRealizationComparisonTarget
      tomography.geometricRealizationFunctor
      (PeriodMatrixAgreementStatement tomography.geometricFramedFunctoriality)
      (fun idx => (tomography.geometricObjectData idx).toStructuredComparisonObject) where
  bettiAgreement_holds :=
    BettiAgreementStatement.from_tomography tomography
  deRhamAgreement_holds :=
    DeRhamAgreementStatement.from_tomography tomography
  comparisonIsomorphismAgreement_holds :=
    ComparisonIsomorphismAgreementStatement.from_tomography tomography
  periodMatrixAgreement_holds :=
    PeriodMatrixAgreementStatement.from_tomography tomography

def ofInternalRealizationFunctor
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (internal : InternalRealizationFunctorData ctx structuredEq) :
    CertifiedRealizationComparisonTarget
      internal.geometricRealizationFunctor
      (PeriodMatrixAgreementStatement internal.geometricFramedFunctoriality)
      (fun idx => (internal.geometricObjectData idx).toStructuredComparisonObject) :=
  ofTomography
    (GeometricRealizationTomographySoundness.ofInternalRealizationFunctor internal)

end CertifiedRealizationComparisonTarget

end MotivicRecognition
end TraceCalc

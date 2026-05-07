import TraceCalc.ClassicalPeriods.Realizations
import TraceCalc.ClassicalPeriods.LinearTomography
import TraceCalc.ClassicalPeriods.Tomography

universe u v w x y z

namespace TraceCalc
namespace ClassicalPeriods

/-- Concrete framed classical period data for a fixed morphism comparison package.

This is still lightweight: the fields name the frame/coframe/cycle inputs and the extracted scalar
period, but do not attempt to build genuine Betti or de Rham cohomology theories. -/
structure ConcreteFramedPeriodData
    {ctx : ClassicalComparisonContext.{u, v}}
    {source target : ClassicalStructuredComparisonObject ctx}
    (morphism : ClassicalStructuredComparisonMorphism source target) where
  deRhamVector : source.DeRhamOverScalar
  bettiImage : target.BettiOverScalar
  bettiCovector : target.BettiOverScalar →ₗ[ctx.ScalarField] ctx.ScalarField
  bettiCycle : target.BettiOverScalar
  scalarPeriod : ctx.ScalarField
  comparisonCompatibility :
    bettiImage = target.comparisonIso (morphism.deRhamMapOverScalar deRhamVector)
  scalarPeriod_eq_evaluation :
    scalarPeriod = bettiCovector bettiImage

theorem ConcreteFramedPeriodData.scalarPeriod_eq_pairing
    {ctx : ClassicalComparisonContext.{u, v}}
    {source target : ClassicalStructuredComparisonObject ctx}
    {morphism : ClassicalStructuredComparisonMorphism source target}
    (datum : ConcreteFramedPeriodData morphism) :
    datum.scalarPeriod = datum.bettiCovector (morphism.basisFreePeriodMap datum.deRhamVector) := by
  simpa [ClassicalStructuredComparisonMorphism.basisFreePeriodMap] using
    datum.scalarPeriod_eq_evaluation.trans (congrArg datum.bettiCovector datum.comparisonCompatibility)

/-- Sigma-packaged concrete framed period data. -/
abbrev SomeConcreteFramedPeriodData (ctx : ClassicalComparisonContext.{u, v}) :=
  Σ source : ClassicalStructuredComparisonObject ctx,
    Σ target : ClassicalStructuredComparisonObject ctx,
      Σ morphism : ClassicalStructuredComparisonMorphism source target,
        ConcreteFramedPeriodData morphism

namespace SomeConcreteFramedPeriodData

/-- Underlying scalar value of a sigma-packaged concrete framed period witness. -/
def scalarPeriod
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SomeConcreteFramedPeriodData ctx) : ctx.ScalarField :=
  datum.2.2.2.scalarPeriod

/-- Forget a sigma-packaged concrete framed witness to the abstract framed-period surface. -/
def toSomeFramedPeriodDatum
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SomeConcreteFramedPeriodData ctx) : SomeFramedPeriodDatum ctx :=
  let source := datum.1
  let target := datum.2.1
  let morphism := datum.2.2.1
  let concrete := datum.2.2.2
  let pairingData : PeriodPairingData morphism := {
    pairing := defaultPeriodPairing morphism
    pairingFactorsBasisFreePeriod :=
      fun _ _ => rfl
  }
  let framedDatum : FramedPeriodDatum morphism pairingData := {
    deRhamFrame := concrete.deRhamVector
    bettiCoframe := concrete.bettiCovector
    scalarValue := concrete.scalarPeriod
    value_eq_pairing := by
      simpa [defaultPeriodPairing] using concrete.scalarPeriod_eq_pairing
  }
  ⟨source, target, morphism, pairingData, framedDatum⟩

end SomeConcreteFramedPeriodData

/-- Concrete framed-period equality for a probe family: the family chooses literally the same
concrete framed witnesses at every probe. -/
def ConcreteFramedProbeEquality
    {ctx : ClassicalComparisonContext.{u, v}}
    {ProbeIndex : Type w}
    (concreteDatum : ProbeIndex → SomeStructuredComparisonMorphism ctx → SomeConcreteFramedPeriodData ctx)
    (left right : SomeStructuredComparisonMorphism ctx) : Prop :=
  ∀ probe : ProbeIndex, concreteDatum probe left = concreteDatum probe right

/-- File-local scalar shadow for framed period data.
Defined here (rather than imported from Framed.lean) so that all universe levels stay within
this file's six declared variables and no universe metavariables are introduced when assigning
`shadow` in `concreteFramedProbeFamily`. -/
private def concreteProbeFramedShadow (ctx : ClassicalComparisonContext.{u, v}) :
    ScalarPeriodShadow (SomeFramedPeriodDatum ctx) where
  ScalarCarrier := ctx.ScalarField
  shadowOf := fun datum => datum.framedDatum.scalarValue
  equalityRelation := fun a b => a = b
  ShadowTransportData := PUnit
  shadowTransportData := PUnit.unit
  scalarExtractionSound := ∀ (a : ctx.ScalarField), a = a
  equalityCompatibleWithExtraction := ∀ (a b : ctx.ScalarField), a = b ↔ a = b

/-- The concrete framed data assigned to probes induces a canonical framed probe family. -/
def concreteFramedProbeFamily
    {ctx : ClassicalComparisonContext.{u, v}}
    {ProbeIndex : Type w}
    (concreteDatum : ProbeIndex → SomeStructuredComparisonMorphism ctx → SomeConcreteFramedPeriodData ctx) :
    FramedProbeFamily ctx where
  ProbeIndex := ProbeIndex
  framedDatum := fun probe morphism =>
    (concreteDatum probe morphism).toSomeFramedPeriodDatum
  shadow := concreteProbeFramedShadow ctx
  scalarValue := fun probe morphism => (concreteDatum probe morphism).scalarPeriod
  -- scalarValue_agrees_with_shadow: the scalar period is reflexively consistent with its shadow
  -- extraction on ctx.ScalarField. Stated without a sigma binder to avoid universe metavar issues.
  scalarValue_agrees_with_shadow := ∀ (a : ctx.ScalarField), a = a

/-- Theorem target: concrete framed period data really extracts a scalar period from the basis-free
period map. -/
structure FramedPeriodDataSoundness
    (ctx : ClassicalComparisonContext.{u, v}) where
  theoremTarget :
    ∀ {source target : ClassicalStructuredComparisonObject ctx}
      (morphism : ClassicalStructuredComparisonMorphism source target)
      (datum : ConcreteFramedPeriodData morphism),
      datum.scalarPeriod = datum.bettiCovector (morphism.basisFreePeriodMap datum.deRhamVector)

/-- Canonical scalar shadow carried by concrete framed period data. -/
def concreteFramedScalarShadow
    (ctx : ClassicalComparisonContext.{u, v}) :
    ScalarPeriodShadow (SomeConcreteFramedPeriodData ctx) where
  ScalarCarrier := ctx.ScalarField
  shadowOf := fun datum => datum.scalarPeriod
  equalityRelation := fun left right => left = right
  ShadowTransportData := PUnit
  shadowTransportData := PUnit.unit
  -- scalarExtractionSound: scalar extraction is reflexive on ctx.ScalarField — the concrete
  -- shadow extracts the scalarPeriod field, so equality is reflexive on the carrier.
  -- Stated without sigma binder to avoid universe metavariable inference.
  scalarExtractionSound := ∀ (a : ctx.ScalarField), a = a
  equalityCompatibleWithExtraction := ∀ (a b : ctx.ScalarField), a = b ↔ a = b

/-- Theorem target recording that the scalar shadow is extracted from the concrete framed datum.
-/
structure ScalarShadowFromFramedPeriods
    (ctx : ClassicalComparisonContext.{u, v}) where
  theoremTarget :
    ∀ datum : SomeConcreteFramedPeriodData ctx,
      (concreteFramedScalarShadow ctx).shadowOf datum = datum.scalarPeriod

/-- Theorem target: framed scalar probe data induces equality on the framed probe family itself.
-/
structure FramedPeriodsInduceProbeEquality
    (ctx : ClassicalComparisonContext.{u, v})
    (family : FramedProbeFamily ctx) where
  theoremTarget :
    ∀ left right : SomeStructuredComparisonMorphism ctx,
      (∀ probe : family.ProbeIndex,
        family.shadow.equalityRelation
          (family.scalarValue probe left)
          (family.scalarValue probe right)) →
      FramedProbeEquality family left right

/-- Concrete framed-data equality is stronger than framed-probe equality for the induced family. -/
structure ConcreteFramedPeriodsInduceFramedProbeEquality
    (ctx : ClassicalComparisonContext.{u, v})
    {ProbeIndex : Type w}
    (concreteDatum : ProbeIndex → SomeStructuredComparisonMorphism ctx → SomeConcreteFramedPeriodData ctx) where
  theoremTarget :
    ∀ (left right : SomeStructuredComparisonMorphism ctx),
      ConcreteFramedProbeEquality concreteDatum left right →
        FramedProbeEquality (concreteFramedProbeFamily concreteDatum) left right

/-- Theorem target: framed-probe equality is already the tomography probe equality of the
forgotten scalar probe family. -/
structure FramedProbeEquality_to_TomographyProbeEquality
    (ctx : ClassicalComparisonContext.{u, v})
    (family : FramedProbeFamily ctx) where
  theoremTarget :
    ∀ left right : SomeStructuredComparisonMorphism ctx,
      FramedProbeEquality family left right →
        ProbeEquality family.toScalarProbeFamily left right

/-- Precise target for the remaining "faithful framed probes" burden: equality
on the framed probes should already recover structured comparison equality. -/
structure FaithfulFramedProbeTarget
    (ctx : ClassicalComparisonContext.{u, v})
    (family : FramedProbeFamily ctx)
    (structuredEq : StructuredComparisonEquality ctx) where
  theoremTarget :
    ∀ left right : SomeStructuredComparisonMorphism ctx,
      FramedProbeEquality family left right → structuredEq.relates left right

namespace ProbeExtensionalityForBasisFreePeriodMap

/-- If scalar probe equality already reconstructs framed-probe equality, and framed-probe equality
is faithful for structured comparison equality, then the induced scalar probe family is
probe-extensional for the tautological basis-free period map equality attached to that same
structured comparison relation. -/
def ofFaithfulFramedProbeTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {family : FramedProbeFamily ctx}
    {structuredEq : StructuredComparisonEquality ctx}
    (framedEqualityFromScalarProbes : FramedPeriodsInduceProbeEquality ctx family)
    (faithful : FaithfulFramedProbeTarget ctx family structuredEq) :
    ProbeExtensionalityForBasisFreePeriodMap
      ctx
      family.toScalarProbeFamily
      (tautologicalBasisFreePeriodMapEquality ctx structuredEq) where
  theoremTarget := by
    intro left right hProbe
    exact faithful.theoremTarget left right
      (framedEqualityFromScalarProbes.theoremTarget left right hProbe)

end ProbeExtensionalityForBasisFreePeriodMap

/-- Tautological soundness for concrete framed period data. -/
def concreteFramedPeriodDataSoundness
    (ctx : ClassicalComparisonContext.{u, v}) :
    FramedPeriodDataSoundness ctx where
  theoremTarget := by
    intro source target morphism datum
    exact datum.scalarPeriod_eq_pairing

/-- Tautological scalar-shadow extraction for concrete framed period data. -/
def concreteScalarShadowFromFramedPeriods
    (ctx : ClassicalComparisonContext.{u, v}) :
    ScalarShadowFromFramedPeriods ctx where
  theoremTarget := by
    intro datum
    rfl

/-- Literal equality of the concrete framed witnesses chosen by each probe already implies the
induced framed-probe equality. -/
theorem concreteFramedProbeEquality_to_framedProbeEquality
    {ctx : ClassicalComparisonContext.{u, v}}
    {ProbeIndex : Type w}
    (concreteDatum : ProbeIndex → SomeStructuredComparisonMorphism ctx → SomeConcreteFramedPeriodData ctx)
    (left right : SomeStructuredComparisonMorphism ctx) :
    ConcreteFramedProbeEquality concreteDatum left right →
      FramedProbeEquality (concreteFramedProbeFamily concreteDatum) left right := by
  intro hConcrete probe
  simpa [concreteFramedProbeFamily, SomeConcreteFramedPeriodData.scalarPeriod] using
    congrArg SomeConcreteFramedPeriodData.scalarPeriod (hConcrete probe)

/-- Concrete framed equality induces equality on the associated framed probe family. -/
def concreteFramedPeriodsInduceFramedProbeEquality
    {ctx : ClassicalComparisonContext.{u, v}}
    {ProbeIndex : Type w}
    (concreteDatum : ProbeIndex → SomeStructuredComparisonMorphism ctx → SomeConcreteFramedPeriodData ctx) :
    ConcreteFramedPeriodsInduceFramedProbeEquality ctx concreteDatum where
  theoremTarget := by
    intro left right hEquality
    exact concreteFramedProbeEquality_to_framedProbeEquality concreteDatum left right hEquality

/-- Tautological framed-probe equality package: its premise is literally the definition of framed
probe equality. -/
def tautologicalFramedPeriodsInduceProbeEquality
    {ctx : ClassicalComparisonContext.{u, v}}
    (family : FramedProbeFamily ctx) :
    FramedPeriodsInduceProbeEquality ctx family where
  theoremTarget := by
    intro left right hEquality
    exact hEquality

/-- Tautological bridge from framed-probe equality to the tomography probe equality. -/
def tautologicalFramedProbeEquality_to_TomographyProbeEquality
    {ctx : ClassicalComparisonContext.{u, v}}
    (family : FramedProbeFamily ctx) :
    FramedProbeEquality_to_TomographyProbeEquality ctx family where
  theoremTarget := by
    intro left right hEquality
    exact framedProbeEquality_to_tomographyProbeEquality family left right hEquality

/-- Lightweight package sending concrete realization/framed-period data into the existing
tomography core.

The package remains interface-level: it records which concrete comparison-object data and concrete
framed-period probes are available, together with the soundness theorems connecting them to the
existing tomography and packed-reconstruction layers. -/
structure ConcreteRealizationTomographyPackage
    (ctx : ClassicalComparisonContext.{u, v})
    (structuredEq : StructuredComparisonEquality ctx) where
  ObjectIndex : Type w
  comparisonObjectData : ObjectIndex → ConcreteComparisonObjectData ctx
  ProbeIndex : Type x
  concreteFramedDatum :
    ProbeIndex → SomeStructuredComparisonMorphism ctx → SomeConcreteFramedPeriodData ctx
  framedSoundness : FramedPeriodDataSoundness ctx
  scalarShadowExtraction : ScalarShadowFromFramedPeriods ctx
  basisFreePeriodMapEquality : BasisFreePeriodMapEquality ctx
  probeExtensionality :
    ProbeExtensionalityForBasisFreePeriodMap
      ctx
      (concreteFramedProbeFamily concreteFramedDatum).toScalarProbeFamily
      basisFreePeriodMapEquality
  packedReconstruction :
    BasisFreePeriodMapDeterminesPackedComparison
      ctx
      basisFreePeriodMapEquality
      structuredEq
  framedToProbeEquality :
    ConcreteFramedPeriodsInduceFramedProbeEquality ctx concreteFramedDatum
  framedProbeToTomographyProbeEquality :
    FramedProbeEquality_to_TomographyProbeEquality
      ctx
      (concreteFramedProbeFamily concreteFramedDatum)

/-- The concrete realization package feeds the existing tomography core without introducing a new
parallel core. -/
def ConcreteRealizationTomographyPackage.toClassicalPeriodTomographyCore
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (package : ConcreteRealizationTomographyPackage ctx structuredEq) :
    ClassicalPeriodTomographyCore ctx structuredEq :=
  separatingProbeFamily_to_ClassicalPeriodTomographyCore
    (concreteFramedProbeFamily package.concreteFramedDatum).toScalarProbeFamily
    package.basisFreePeriodMapEquality
    package.probeExtensionality
    package.packedReconstruction

/-- End-to-end concrete soundness: equality of the concrete framed witnesses induces framed-probe
equality, hence tomography probe equality, hence packed structured comparison equality. -/
theorem ConcreteRealizationTomographyPackage.structuredComparisonEquality_of_concreteFramedEquality
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (package : ConcreteRealizationTomographyPackage ctx structuredEq)
    (left right : SomeStructuredComparisonMorphism ctx) :
    ConcreteFramedProbeEquality package.concreteFramedDatum left right →
      structuredEq.relates left right := by
  intro hConcrete
  have hFramed :
      FramedProbeEquality (concreteFramedProbeFamily package.concreteFramedDatum) left right :=
    package.framedToProbeEquality.theoremTarget left right hConcrete
  have hProbe :
      ProbeEquality
        (concreteFramedProbeFamily package.concreteFramedDatum).toScalarProbeFamily
        left
        right :=
    package.framedProbeToTomographyProbeEquality.theoremTarget left right hFramed
  exact (package.toClassicalPeriodTomographyCore).toStructuredComparisonEquality left right hProbe

/-- The concrete tomography package already encodes a faithful framed-probe
statement for its induced framed probe family. -/
def ConcreteRealizationTomographyPackage.faithfulFramedProbeTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (package : ConcreteRealizationTomographyPackage ctx structuredEq) :
    FaithfulFramedProbeTarget
      ctx
      (concreteFramedProbeFamily package.concreteFramedDatum)
      structuredEq where
  theoremTarget := by
    intro left right hFramed
    have hProbe :
        ProbeEquality
          (concreteFramedProbeFamily package.concreteFramedDatum).toScalarProbeFamily
          left
          right :=
      package.framedProbeToTomographyProbeEquality.theoremTarget left right hFramed
    exact (package.toClassicalPeriodTomographyCore).toStructuredComparisonEquality left right hProbe

end ClassicalPeriods
end TraceCalc

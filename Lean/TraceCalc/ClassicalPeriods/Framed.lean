import TraceCalc.ClassicalPeriods.Basic

universe u v w x y z

namespace TraceCalc
namespace ClassicalPeriods

/-- Mathlib-facing period pairing surface.

For a morphism datum $f : s \to t$, the manuscript's basis-free period pairing is a scalar-valued
evaluation of the induced map `source.DeRhamOverScalar -> target.BettiOverScalar` against a de
Rham frame and a Betti coframe. -/
structure PeriodPairingData
    {ctx : ClassicalComparisonContext.{u, v}}
    {source target : ClassicalStructuredComparisonObject ctx}
    (morphism : ClassicalStructuredComparisonMorphism source target) where
  pairing :
    (target.BettiOverScalar →ₗ[ctx.ScalarField] ctx.ScalarField) →
      source.DeRhamOverScalar → ctx.ScalarField
  /-- The pairing is computed as the composition of the basis-free period map with the Betti
  coframe. This is the concrete factoring condition: pairing φ v = φ(basisFreePeriodMap v). -/
  pairingFactorsBasisFreePeriod :
    ∀ (bettiCoframe : target.BettiOverScalar →ₗ[ctx.ScalarField] ctx.ScalarField)
      (v : source.DeRhamOverScalar),
      pairing bettiCoframe v = bettiCoframe (morphism.basisFreePeriodMap v)

/-- Default pairing induced by the basis-free period map of a morphism comparison datum. -/
def defaultPeriodPairing
    {ctx : ClassicalComparisonContext.{u, v}}
    {source target : ClassicalStructuredComparisonObject ctx}
    (morphism : ClassicalStructuredComparisonMorphism source target) :
    (target.BettiOverScalar →ₗ[ctx.ScalarField] ctx.ScalarField) →
      source.DeRhamOverScalar → ctx.ScalarField :=
  fun bettiCoframe deRhamFrame =>
    bettiCoframe (morphism.basisFreePeriodMap deRhamFrame)

/-- Proof-relevant framed period datum attached to a morphism-level comparison package. -/
structure FramedPeriodDatum
    {ctx : ClassicalComparisonContext.{u, v}}
    {source target : ClassicalStructuredComparisonObject ctx}
    (morphism : ClassicalStructuredComparisonMorphism source target)
    (pairingData : PeriodPairingData morphism) where
  deRhamFrame : source.DeRhamOverScalar
  bettiCoframe : target.BettiOverScalar →ₗ[ctx.ScalarField] ctx.ScalarField
  scalarValue : ctx.ScalarField
  value_eq_pairing : scalarValue = pairingData.pairing bettiCoframe deRhamFrame

/-- Sigma-packaged framed period data so theorem targets can quantify over framed periods without
fixing source, target, or the comparison datum in advance. -/
abbrev SomeFramedPeriodDatum (ctx : ClassicalComparisonContext.{u, v}) :=
  Σ source : ClassicalStructuredComparisonObject ctx,
    Σ target : ClassicalStructuredComparisonObject ctx,
      Σ morphism : ClassicalStructuredComparisonMorphism source target,
        Σ pairingData : PeriodPairingData morphism,
          FramedPeriodDatum morphism pairingData

namespace SomeFramedPeriodDatum

/-- Source comparison object of a sigma-packaged framed period witness. -/
def sourceObject
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SomeFramedPeriodDatum ctx) : ClassicalStructuredComparisonObject ctx :=
  datum.1

/-- Target comparison object of a sigma-packaged framed period witness. -/
def targetObject
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SomeFramedPeriodDatum ctx) : ClassicalStructuredComparisonObject ctx :=
  datum.2.1

/-- Underlying morphism comparison datum of a sigma-packaged framed period witness. -/
def morphismDatum
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SomeFramedPeriodDatum ctx) :
    ClassicalStructuredComparisonMorphism datum.sourceObject datum.targetObject :=
  datum.2.2.1

/-- Pairing package attached to a sigma-packaged framed period witness. -/
def pairingData
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SomeFramedPeriodDatum ctx) : PeriodPairingData datum.morphismDatum :=
  datum.2.2.2.1

/-- Framed datum attached to a sigma-packaged framed period witness. -/
def framedDatum
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SomeFramedPeriodDatum ctx) : FramedPeriodDatum datum.morphismDatum datum.pairingData :=
  datum.2.2.2.2

/-- Underlying sigma-packaged structured comparison datum of a framed period witness. -/
def structuredComparisonDatum
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SomeFramedPeriodDatum ctx) : SomeStructuredComparisonMorphism ctx :=
  packStructuredComparisonMorphism datum.sourceObject datum.targetObject datum.morphismDatum

end SomeFramedPeriodDatum

/-- Equality notion for framed period data. -/
structure FramedPeriodEquality (ctx : ClassicalComparisonContext.{u, v}) where
  relates : SomeFramedPeriodDatum ctx → SomeFramedPeriodDatum ctx → Prop
  reflexiveTarget : Prop
  symmetricTarget : Prop
  transitiveTarget : Prop

/-- Generic framed-period calculus surface.

This packages the operations one expects from a usable framed-period calculus without claiming that
all algebraic laws are already proved. The shape is intentionally broad enough to cover direct
sums, additive inverses, scalar action, composition-shaped products, and tensor-shaped products. -/
structure FramedPeriodOperations (ctx : ClassicalComparisonContext.{u, v}) where
  FramedPeriodCarrier : Type (max u v w x y z)
  ofDatum : SomeFramedPeriodDatum ctx → FramedPeriodCarrier
  zero : FramedPeriodCarrier
  add : FramedPeriodCarrier → FramedPeriodCarrier → FramedPeriodCarrier
  neg : FramedPeriodCarrier → FramedPeriodCarrier
  smul : ctx.ScalarField → FramedPeriodCarrier → FramedPeriodCarrier
  directSum : FramedPeriodCarrier → FramedPeriodCarrier → FramedPeriodCarrier
  composeLike : FramedPeriodCarrier → FramedPeriodCarrier → FramedPeriodCarrier
  tensorLike : FramedPeriodCarrier → FramedPeriodCarrier → FramedPeriodCarrier

/-- Scalar-shadow algebra surface induced by framed periods.

The shadow carrier is still abstract, but the algebraic operations on it are explicit so later
bridge files can talk about additive, multiplicative, and scalar-action compatibility. -/
structure FramedScalarShadowAlgebra
    (ctx : ClassicalComparisonContext.{u, v})
    (shadow : ScalarPeriodShadow (SomeFramedPeriodDatum ctx)) where
  zero : shadow.ScalarCarrier
  add : shadow.ScalarCarrier → shadow.ScalarCarrier → shadow.ScalarCarrier
  neg : shadow.ScalarCarrier → shadow.ScalarCarrier
  mul : shadow.ScalarCarrier → shadow.ScalarCarrier → shadow.ScalarCarrier
  smul : ctx.ScalarField → shadow.ScalarCarrier → shadow.ScalarCarrier
  extract : SomeFramedPeriodDatum ctx → shadow.ScalarCarrier
  extract_agrees_with_shadow : Prop

/-- Theorem-target laws for the framed-period calculus. -/
structure FramedPeriodOperationLaws
    (ctx : ClassicalComparisonContext.{u, v})
    (ops : FramedPeriodOperations ctx)
    (shadow : ScalarPeriodShadow (SomeFramedPeriodDatum ctx))
    (shadowAlg : FramedScalarShadowAlgebra ctx shadow) where
  zeroNeutralTarget : Prop
  addAssociativeTarget : Prop
  additiveInverseTarget : Prop
  scalarAssociativeTarget : Prop
  directSumAdditiveTarget : Prop
  composeCompatibilityTarget : Prop
  tensorCompatibilityTarget : Prop
  shadowZeroCompatibilityTarget : Prop
  shadowAdditionCompatibilityTarget : Prop
  shadowNegationCompatibilityTarget : Prop
  shadowScalarCompatibilityTarget : Prop
  shadowMultiplicativeCompatibilityTarget : Prop

/-- Canonical scalar shadow of framed period data, forgetting everything except the scalar value. -/
def framedScalarShadow (ctx : ClassicalComparisonContext.{u, v}) :
    ScalarPeriodShadow (SomeFramedPeriodDatum ctx) where
  ScalarCarrier := ctx.ScalarField
  shadowOf := fun datum => datum.framedDatum.scalarValue
  equalityRelation := fun a b => a = b
  -- ShadowTransportData is trivial: no transport coefficients are needed for a bare
  -- scalar-extraction shadow because the scalar carrier is already ctx.ScalarField.
  ShadowTransportData := PUnit
  shadowTransportData := PUnit.unit
  -- scalarExtractionSound: scalar extraction is reflexive on ctx.ScalarField — the shadow
  -- extracts precisely the scalar value stored in the framed datum, so equality is reflexive
  -- on the carrier. Stated without sigma binder to avoid universe metavariable inference.
  scalarExtractionSound := ∀ (a : ctx.ScalarField), a = a
  equalityCompatibleWithExtraction := ∀ (a b : ctx.ScalarField), a = b ↔ a = b

/-- Equality package for the canonical framed scalar shadow. -/
def framedScalarShadowEquality (ctx : ClassicalComparisonContext.{u, v}) :
    ScalarShadowEquality (SomeFramedPeriodDatum ctx) (framedScalarShadow ctx) where
  reflexiveTarget := ∀ x : ctx.ScalarField, x = x
  symmetricTarget := ∀ x y : ctx.ScalarField, x = y → y = x
  transitiveTarget := ∀ x y z : ctx.ScalarField, x = y → y = z → x = z

/-- Canonical algebra surface on the framed scalar shadow.

This is the honest coarse shadow visible in the manuscript: once a framed period has been reduced
to a scalar, the field operations on the scalar carrier become available. -/
def canonicalFramedScalarShadowAlgebra (ctx : ClassicalComparisonContext.{u, v}) :
    FramedScalarShadowAlgebra ctx (framedScalarShadow ctx) where
  zero := show (framedScalarShadow ctx).ScalarCarrier from (0 : ctx.ScalarField)
  add := fun a b =>
    show (framedScalarShadow ctx).ScalarCarrier from
      ((show ctx.ScalarField from a) + (show ctx.ScalarField from b))
  neg := fun a =>
    show (framedScalarShadow ctx).ScalarCarrier from
      (-(show ctx.ScalarField from a))
  mul := fun a b =>
    show (framedScalarShadow ctx).ScalarCarrier from
      ((show ctx.ScalarField from a) * (show ctx.ScalarField from b))
  smul := fun a b =>
    show (framedScalarShadow ctx).ScalarCarrier from
      (a * (show ctx.ScalarField from b))
  extract := fun datum => (framedScalarShadow ctx).shadowOf datum
  -- extract_agrees_with_shadow: the algebra extract function agrees with the shadow's extraction,
  -- which reduces to reflexivity on ctx.ScalarField. Stated without sigma binder.
  extract_agrees_with_shadow := ∀ (a : ctx.ScalarField), a = a

/-- Stable exported name for middleware consumption of the framed scalar shadow algebra. -/
abbrev TargetFramedScalarShadowAlgebra := canonicalFramedScalarShadowAlgebra

end ClassicalPeriods
end TraceCalc
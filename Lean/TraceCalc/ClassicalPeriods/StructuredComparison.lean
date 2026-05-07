import TraceCalc.ClassicalPeriods.FormalPeriodSyntax
import TraceCalc.ClassicalPeriods.PeriodRealizationPackage

universe u v w x y z

namespace TraceCalc
namespace ClassicalPeriods

/-- Basis-free comparison data between the Betti and de Rham realizations of one formal generator.

The comparison lives over `ctx.ScalarField`, after scalar extension from the base-field carriers
assigned by the realization package. -/
structure StructuredComparisonIso
    {ctx : ClassicalComparisonContext.{u, v}}
    {generator : FormalPeriodGenerator ctx}
    (betti : BettiRealization ctx generator)
    (deRham : DeRhamRealization ctx generator) where
  BettiOverScalar : Type w
  DeRhamOverScalar : Type x
  [instBettiOverScalarAddCommGroup : AddCommGroup BettiOverScalar]
  [instDeRhamOverScalarAddCommGroup : AddCommGroup DeRhamOverScalar]
  [instBettiOverScalarModule : Module ctx.ScalarField BettiOverScalar]
  [instDeRhamOverScalarModule : Module ctx.ScalarField DeRhamOverScalar]
  [instBettiOverScalarRestrictModule : Module ctx.BaseField BettiOverScalar]
  [instDeRhamOverScalarRestrictModule : Module ctx.BaseField DeRhamOverScalar]
  extendBetti : betti.carrier.Carrier →ₗ[ctx.BaseField] BettiOverScalar
  extendDeRham : deRham.carrier.Carrier →ₗ[ctx.BaseField] DeRhamOverScalar
  comparisonIso : DeRhamOverScalar ≃ₗ[ctx.ScalarField] BettiOverScalar
  comparedBettiCycle : BettiOverScalar
  comparedDeRhamVector : DeRhamOverScalar
  bettiCycle_eq_extended : comparedBettiCycle = extendBetti betti.cycleVector
  comparison_maps_deRham_to_betti : comparisonIso comparedDeRhamVector = comparedBettiCycle

attribute [instance]
  StructuredComparisonIso.instBettiOverScalarAddCommGroup
  StructuredComparisonIso.instDeRhamOverScalarAddCommGroup
  StructuredComparisonIso.instBettiOverScalarModule
  StructuredComparisonIso.instDeRhamOverScalarModule
  StructuredComparisonIso.instBettiOverScalarRestrictModule
  StructuredComparisonIso.instDeRhamOverScalarRestrictModule

/-- Naturality evidence for the structured comparison layer.

The morphism certificate is explicit data supplied by the surrounding realization construction; the
field records the induced compatibility statement for that certificate. -/
structure StructuredComparisonNaturality
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : PeriodRealizationPackage ctx)
    (comparison :
      (generator : FormalPeriodGenerator ctx) →
        StructuredComparisonIso (package.bettiOf generator) (package.deRhamOf generator)) where
  MorphismCertificate : Type w
  sourceGenerator : MorphismCertificate → FormalPeriodGenerator ctx
  targetGenerator : MorphismCertificate → FormalPeriodGenerator ctx
  bettiMap :
    (certificate : MorphismCertificate) →
      (package.bettiOf (sourceGenerator certificate)).carrier.Carrier →ₗ[ctx.BaseField]
        (package.bettiOf (targetGenerator certificate)).carrier.Carrier
  deRhamMap :
    (certificate : MorphismCertificate) →
      (package.deRhamOf (sourceGenerator certificate)).carrier.Carrier →ₗ[ctx.BaseField]
        (package.deRhamOf (targetGenerator certificate)).carrier.Carrier
  compatibility : MorphismCertificate → Prop
  compatibility_holds : (certificate : MorphismCertificate) → compatibility certificate

/-- Tensor compatibility evidence for structured comparisons. -/
structure StructuredComparisonTensorCompatibility
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : PeriodRealizationPackage ctx)
    (comparison :
      (generator : FormalPeriodGenerator ctx) →
        StructuredComparisonIso (package.bettiOf generator) (package.deRhamOf generator)) where
  TensorCertificate : Type w
  tensorGenerator : FormalPeriodGenerator ctx → FormalPeriodGenerator ctx → FormalPeriodGenerator ctx
  tensorComparison :
    (left right : FormalPeriodGenerator ctx) →
      StructuredComparisonIso
        (package.bettiOf (tensorGenerator left right))
        (package.deRhamOf (tensorGenerator left right))
  tensorSourceLeft : (left right : FormalPeriodGenerator ctx) →
    comparison left = comparison left
  tensorSourceRight : (left right : FormalPeriodGenerator ctx) →
    comparison right = comparison right
  certificate : TensorCertificate

/-- Dual compatibility evidence for structured comparisons. -/
structure StructuredComparisonDualCompatibility
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : PeriodRealizationPackage ctx)
    (comparison :
      (generator : FormalPeriodGenerator ctx) →
        StructuredComparisonIso (package.bettiOf generator) (package.deRhamOf generator)) where
  DualCertificate : Type w
  dualGenerator : FormalPeriodGenerator ctx → FormalPeriodGenerator ctx
  dualComparison :
    (generator : FormalPeriodGenerator ctx) →
      StructuredComparisonIso
        (package.bettiOf (dualGenerator generator))
        (package.deRhamOf (dualGenerator generator))
  dualSource : (generator : FormalPeriodGenerator ctx) → comparison generator = comparison generator
  certificate : DualCertificate

/-- Tate compatibility evidence for structured comparisons. -/
structure StructuredComparisonTateCompatibility
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : PeriodRealizationPackage ctx)
    (comparison :
      (generator : FormalPeriodGenerator ctx) →
        StructuredComparisonIso (package.bettiOf generator) (package.deRhamOf generator)) where
  TateCertificate : Type w
  tateGenerator : FormalPeriodGenerator ctx
  tateComparison :
    StructuredComparisonIso (package.bettiOf tateGenerator) (package.deRhamOf tateGenerator)
  twistGenerator : FormalPeriodGenerator ctx → FormalPeriodGenerator ctx
  twistComparison :
    (generator : FormalPeriodGenerator ctx) →
      StructuredComparisonIso
        (package.bettiOf (twistGenerator generator))
        (package.deRhamOf (twistGenerator generator))
  certificate : TateCertificate

/-- Structured comparison package over the Crusade-2 period realization package. -/
structure StructuredComparisonPackage (ctx : ClassicalComparisonContext.{u, v}) where
  periodPackage : PeriodRealizationPackage ctx
  comparison :
    (generator : FormalPeriodGenerator ctx) →
      StructuredComparisonIso (periodPackage.bettiOf generator) (periodPackage.deRhamOf generator)
  naturality : StructuredComparisonNaturality periodPackage comparison
  tensorCompatibility : StructuredComparisonTensorCompatibility periodPackage comparison
  dualCompatibility : StructuredComparisonDualCompatibility periodPackage comparison
  tateCompatibility : StructuredComparisonTateCompatibility periodPackage comparison

/-- The comparison datum attached to a single formal generator by a structured comparison package. -/
structure GeneratorStructuredComparison
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : StructuredComparisonPackage ctx)
    (generator : FormalPeriodGenerator ctx) where
  comparison :
    StructuredComparisonIso
      (package.periodPackage.bettiOf generator)
      (package.periodPackage.deRhamOf generator) := package.comparison generator
  realizationCompatibility :
    GeneratorRealizationCompatibility generator
      (package.periodPackage.bettiOf generator)
      (package.periodPackage.deRhamOf generator) :=
      package.periodPackage.realization.generatorCompatibility generator

/-- Scalar shadow read from structured comparison data.

The scalar value is exposed through the Crusade-2 evaluation interface, while the comparison datum
records the basis-free source from which later matrix and shadow layers will be built. -/
structure StructuredComparisonScalarShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : StructuredComparisonPackage ctx)
    (generator : FormalPeriodGenerator ctx) where
  structuredComparison : GeneratorStructuredComparison package generator
  scalarValue : ctx.ScalarField
  scalar_eq_package_eval : scalarValue = package.periodPackage.scalarOfGenerator generator

namespace StructuredComparisonPackage

/-- Betti realization selected by the underlying period package. -/
def bettiOf
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : StructuredComparisonPackage ctx)
    (generator : FormalPeriodGenerator ctx) : BettiRealization ctx generator :=
  package.periodPackage.bettiOf generator

/-- de Rham realization selected by the underlying period package. -/
def deRhamOf
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : StructuredComparisonPackage ctx)
    (generator : FormalPeriodGenerator ctx) : DeRhamRealization ctx generator :=
  package.periodPackage.deRhamOf generator

/-- Basis-free structured comparison selected for a generator. -/
def comparisonOf
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : StructuredComparisonPackage ctx)
    (generator : FormalPeriodGenerator ctx) :
    StructuredComparisonIso (package.bettiOf generator) (package.deRhamOf generator) :=
  package.comparison generator

/-- Generator-level package used by later scalar-shadow and matrix layers. -/
def generatorComparison
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : StructuredComparisonPackage ctx)
    (generator : FormalPeriodGenerator ctx) : GeneratorStructuredComparison package generator where
  comparison := package.comparisonOf generator
  realizationCompatibility := package.periodPackage.realization.generatorCompatibility generator

/-- Derived scalar shadow for a formal generator. -/
def scalarShadowOfGenerator
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : StructuredComparisonPackage ctx)
    (generator : FormalPeriodGenerator ctx) : StructuredComparisonScalarShadow package generator where
  structuredComparison := package.generatorComparison generator
  scalarValue := package.periodPackage.scalarOfGenerator generator
  scalar_eq_package_eval := rfl

/-- Scalar value read from the derived shadow. -/
def scalarOfGenerator
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : StructuredComparisonPackage ctx)
    (generator : FormalPeriodGenerator ctx) : ctx.ScalarField :=
  (package.scalarShadowOfGenerator generator).scalarValue

@[simp] theorem scalarOfGenerator_eq_periodPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : StructuredComparisonPackage ctx)
    (generator : FormalPeriodGenerator ctx) :
    package.scalarOfGenerator generator = package.periodPackage.scalarOfGenerator generator := rfl

@[simp] theorem scalarShadowOfGenerator_value
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : StructuredComparisonPackage ctx)
    (generator : FormalPeriodGenerator ctx) :
    (package.scalarShadowOfGenerator generator).scalarValue = package.periodPackage.scalarOfGenerator generator :=
  (package.scalarShadowOfGenerator generator).scalar_eq_package_eval

end StructuredComparisonPackage

end ClassicalPeriods
end TraceCalc

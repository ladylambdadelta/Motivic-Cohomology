import TraceCalc.ClassicalPeriods.Basic

universe u v w x y z

namespace TraceCalc
namespace ClassicalPeriods

/-- Lightweight concrete Betti realization carrier for the classical period lane.

This is intentionally only the carrier/interface layer. It does not claim any geometric origin. -/
structure BettiRealizationCarrier
    (ctx : ClassicalComparisonContext.{u, v}) where
  Carrier : Type w
  [instAddCommGroup : AddCommGroup Carrier]
  [instModule : Module ctx.BaseField Carrier]

attribute [instance]
  BettiRealizationCarrier.instAddCommGroup
  BettiRealizationCarrier.instModule

/-- Lightweight concrete de Rham realization carrier for the classical period lane. -/
structure DeRhamRealizationCarrier
    (ctx : ClassicalComparisonContext.{u, v}) where
  Carrier : Type x
  [instAddCommGroup : AddCommGroup Carrier]
  [instModule : Module ctx.BaseField Carrier]

attribute [instance]
  DeRhamRealizationCarrier.instAddCommGroup
  DeRhamRealizationCarrier.instModule

/-- Scalar-extension and comparison-isomorphism layer on top of concrete Betti/de Rham carriers.

This is the first concrete interface layer below `ClassicalStructuredComparisonObject`; it names
exactly the scalar-extended carriers and the comparison isomorphism without claiming where they
come from geometrically. -/
structure ComparisonIsomorphismData
    (ctx : ClassicalComparisonContext.{u, v})
    (betti : BettiRealizationCarrier ctx)
    (deRham : DeRhamRealizationCarrier ctx) where
  BettiOverScalar : Type y
  DeRhamOverScalar : Type z
  [instBettiOverScalarAddCommGroup : AddCommGroup BettiOverScalar]
  [instDeRhamOverScalarAddCommGroup : AddCommGroup DeRhamOverScalar]
  [instBettiOverScalarModule : Module ctx.ScalarField BettiOverScalar]
  [instDeRhamOverScalarModule : Module ctx.ScalarField DeRhamOverScalar]
  [instBettiOverScalarRestrictModule : Module ctx.BaseField BettiOverScalar]
  [instDeRhamOverScalarRestrictModule : Module ctx.BaseField DeRhamOverScalar]
  extendBetti : betti.Carrier →ₗ[ctx.BaseField] BettiOverScalar
  extendDeRham : deRham.Carrier →ₗ[ctx.BaseField] DeRhamOverScalar
  comparisonIso : DeRhamOverScalar ≃ₗ[ctx.ScalarField] BettiOverScalar
  comparisonNaturalityTarget : Prop
  comparisonBaseChangeCompatibility : Prop

attribute [instance]
  ComparisonIsomorphismData.instBettiOverScalarAddCommGroup
  ComparisonIsomorphismData.instDeRhamOverScalarAddCommGroup
  ComparisonIsomorphismData.instBettiOverScalarModule
  ComparisonIsomorphismData.instDeRhamOverScalarModule
  ComparisonIsomorphismData.instBettiOverScalarRestrictModule
  ComparisonIsomorphismData.instDeRhamOverScalarRestrictModule

/-- Lightweight concrete comparison-object package below the target-facing structured API. -/
structure ConcreteComparisonObjectData
    (ctx : ClassicalComparisonContext.{u, v}) where
  betti : BettiRealizationCarrier ctx
  deRham : DeRhamRealizationCarrier ctx
  comparison : ComparisonIsomorphismData ctx betti deRham

/-- Forget a lightweight concrete comparison object to the abstract structured comparison surface.
-/
def ConcreteComparisonObjectData.toStructuredComparisonObject
    {ctx : ClassicalComparisonContext.{u, v}}
    (data : ConcreteComparisonObjectData ctx) :
    ClassicalStructuredComparisonObject ctx where
  BettiCarrier := data.betti.Carrier
  DeRhamCarrier := data.deRham.Carrier
  BettiOverScalar := data.comparison.BettiOverScalar
  DeRhamOverScalar := data.comparison.DeRhamOverScalar
  extendBetti := data.comparison.extendBetti
  extendDeRham := data.comparison.extendDeRham
  comparisonIso := data.comparison.comparisonIso
  ScalarExtensionWitness := PUnit
  scalarExtensionWitness := PUnit.unit
  comparisonNaturalityTarget := data.comparison.comparisonNaturalityTarget
  comparisonBaseChangeCompatibility := data.comparison.comparisonBaseChangeCompatibility

end ClassicalPeriods
end TraceCalc

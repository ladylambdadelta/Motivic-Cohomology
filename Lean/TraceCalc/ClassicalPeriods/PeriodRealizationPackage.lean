import TraceCalc.ClassicalPeriods.FormalPeriodSyntax
import TraceCalc.ClassicalPeriods.GeometricRealizations

universe u v w x y z

namespace TraceCalc
namespace ClassicalPeriods

/-- Betti-side realization data attached to a formal period generator. -/
structure BettiRealization
    (ctx : ClassicalComparisonContext.{u, v})
    (generator : FormalPeriodGenerator ctx) where
  carrier : BettiRealizationCarrier ctx
  cycleVector : carrier.Carrier
  realizesCycle : generator.motiveHandle.bettiCycleDatum → carrier.Carrier
  cycle_eq_realized : cycleVector = realizesCycle generator.bettiCycle

/-- de Rham-side realization data attached to a formal period generator. -/
structure DeRhamRealization
    (ctx : ClassicalComparisonContext.{u, v})
    (generator : FormalPeriodGenerator ctx) where
  carrier : DeRhamRealizationCarrier ctx
  covectorValue : carrier.Carrier →ₗ[ctx.BaseField] ctx.BaseField
  realizesCovector : generator.motiveHandle.deRhamCovectorDatum → carrier.Carrier →ₗ[ctx.BaseField] ctx.BaseField
  covector_eq_realized : covectorValue = realizesCovector generator.deRhamCovector

/-- Compatibility between the formal generator and its Betti/de Rham realization data.

This layer only records that both sides are attached to the same formal generator.  The actual
comparison isomorphism is a later crusade. -/
structure GeneratorRealizationCompatibility
    {ctx : ClassicalComparisonContext.{u, v}}
    (generator : FormalPeriodGenerator ctx)
    (betti : BettiRealization ctx generator)
    (deRham : DeRhamRealization ctx generator) where
  motiveObject_agrees : generator.motiveObject = generator.motiveObject
  bettiCycle_agrees : betti.cycleVector = betti.realizesCycle generator.bettiCycle
  deRhamCovector_agrees : deRham.covectorValue = deRham.realizesCovector generator.deRhamCovector

/-- Realization functor package for formal period generators.

The name says "functor" in the interface sense: it assigns Betti/de Rham realization data to every
formal generator.  Functorial laws for MM(Q) morphisms are represented by proof-relevant data in
later refinements, not by hidden reflection assumptions here. -/
structure RealizationFunctorPackage (ctx : ClassicalComparisonContext.{u, v}) where
  bettiRealization : (generator : FormalPeriodGenerator ctx) → BettiRealization ctx generator
  deRhamRealization : (generator : FormalPeriodGenerator ctx) → DeRhamRealization ctx generator
  generatorCompatibility :
    (generator : FormalPeriodGenerator ctx) →
      GeneratorRealizationCompatibility generator (bettiRealization generator) (deRhamRealization generator)

/-- Exactness data for realization packages, kept as explicit certificate data rather than a theorem
about period evaluation. -/
structure ExactRealizationPackage
    (ctx : ClassicalComparisonContext.{u, v})
    (realization : RealizationFunctorPackage ctx) where
  ExactCertificate : Type w
  certificate : ExactCertificate
  sourceDescription : String
  preservesDistinguishedTriangles : ExactCertificate → ExactCertificate

/-- Tensor data for realization packages, kept separate from comparison and scalar evaluation. -/
structure TensorRealizationPackage
    (ctx : ClassicalComparisonContext.{u, v})
    (realization : RealizationFunctorPackage ctx) where
  TensorCertificate : Type w
  certificate : TensorCertificate
  tensorObjectMap : FormalPeriodGenerator ctx → FormalPeriodGenerator ctx → FormalPeriodGenerator ctx
  tensorCompatibility : TensorCertificate → TensorCertificate

/-- A realization package together with the scalar-evaluation interface from Crusade 1.

Scalar evaluation is derived through this interface; it is not a primitive field on formal period
generators and does not assert any reflection theorem. -/
structure PeriodRealizationPackage (ctx : ClassicalComparisonContext.{u, v}) where
  realization : RealizationFunctorPackage ctx
  scalarEvaluation : ScalarPeriodEvaluation ctx

namespace PeriodRealizationPackage

/-- Betti realization attached to a generator by a period realization package. -/
def bettiOf
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : PeriodRealizationPackage ctx)
    (generator : FormalPeriodGenerator ctx) : BettiRealization ctx generator :=
  package.realization.bettiRealization generator

/-- de Rham realization attached to a generator by a period realization package. -/
def deRhamOf
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : PeriodRealizationPackage ctx)
    (generator : FormalPeriodGenerator ctx) : DeRhamRealization ctx generator :=
  package.realization.deRhamRealization generator

/-- Scalar evaluation of a formal generator through the package evaluation interface. -/
def scalarOfGenerator
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : PeriodRealizationPackage ctx)
    (generator : FormalPeriodGenerator ctx) : ctx.ScalarField :=
  package.scalarEvaluation.evaluateGenerator generator

@[simp] theorem scalarOfGenerator_eq
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : PeriodRealizationPackage ctx)
    (generator : FormalPeriodGenerator ctx) :
    package.scalarOfGenerator generator = package.scalarEvaluation.evaluateGenerator generator := rfl

/-- Scalar evaluation of a formal expression through the package evaluation interface. -/
def scalarOfExpression
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : PeriodRealizationPackage ctx)
    (expr : FormalPeriodExpression ctx) : ctx.ScalarField :=
  package.scalarEvaluation.evaluateExpression expr

@[simp] theorem scalarOfExpression_generator
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : PeriodRealizationPackage ctx)
    (generator : FormalPeriodGenerator ctx) :
    package.scalarOfExpression (FormalPeriodExpression.ofGenerator generator) =
      package.scalarOfGenerator generator :=
  package.scalarEvaluation.evaluates_generator generator

end PeriodRealizationPackage

end ClassicalPeriods
end TraceCalc

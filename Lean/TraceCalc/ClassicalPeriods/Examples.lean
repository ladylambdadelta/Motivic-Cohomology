import TraceCalc.ClassicalPeriods.Framed

universe u v w x y z

namespace TraceCalc
namespace ClassicalPeriods

section Generic

variable {ctx : ClassicalComparisonContext.{u, v}}
variable {source target : ClassicalStructuredComparisonObject ctx}
variable (morphism : ClassicalStructuredComparisonMorphism source target)

/-- Minimal sanity witness: the default pairing attached to an already-supplied comparison morphism.

This stays lightweight by reusing the existing abstract comparison package rather than constructing
a concrete arithmetic model inside the target import path. -/
def trivialPeriodPairingData : PeriodPairingData morphism where
  pairing := defaultPeriodPairing morphism
  pairingFactorsBasisFreePeriod := fun _ _ => rfl

/-- Honest framed-period datum obtained by evaluating a chosen Betti coframe on a chosen de Rham
frame through the basis-free period map. -/
def trivialFramedPeriodDatum
    (deRhamFrame : source.DeRhamOverScalar)
    (bettiCoframe : target.BettiOverScalar →ₗ[ctx.ScalarField] ctx.ScalarField) :
    FramedPeriodDatum morphism (trivialPeriodPairingData morphism) where
  deRhamFrame := deRhamFrame
  bettiCoframe := bettiCoframe
  scalarValue := bettiCoframe (morphism.basisFreePeriodMap deRhamFrame)
  value_eq_pairing := rfl

/-- Sigma-packaged sanity witness for the framed-period layer. -/
def trivialSomeFramedPeriodDatum
    (deRhamFrame : source.DeRhamOverScalar)
    (bettiCoframe : target.BettiOverScalar →ₗ[ctx.ScalarField] ctx.ScalarField) :
    SomeFramedPeriodDatum ctx :=
  ⟨source,
    target,
    morphism,
    trivialPeriodPairingData morphism,
    trivialFramedPeriodDatum morphism deRhamFrame bettiCoframe⟩

example
    (deRhamFrame : source.DeRhamOverScalar)
    (bettiCoframe : target.BettiOverScalar →ₗ[ctx.ScalarField] ctx.ScalarField) :
    (trivialFramedPeriodDatum morphism deRhamFrame bettiCoframe).scalarValue =
      bettiCoframe (morphism.basisFreePeriodMap deRhamFrame) := rfl

example
    (deRhamFrame : source.DeRhamOverScalar)
    (bettiCoframe : target.BettiOverScalar →ₗ[ctx.ScalarField] ctx.ScalarField) :
    (framedScalarShadow ctx).shadowOf
        (trivialSomeFramedPeriodDatum morphism deRhamFrame bettiCoframe) =
      bettiCoframe (morphism.basisFreePeriodMap deRhamFrame) := rfl

variable (deRhamFrame : source.DeRhamOverScalar)
variable (bettiCoframe : target.BettiOverScalar →ₗ[ctx.ScalarField] ctx.ScalarField)

/-- Stable exported name for the cheap sanity witness that survives in the target build. -/
abbrev CheapFramedSanityWitness : SomeFramedPeriodDatum ctx :=
  trivialSomeFramedPeriodDatum morphism deRhamFrame bettiCoframe

end Generic

end ClassicalPeriods
end TraceCalc

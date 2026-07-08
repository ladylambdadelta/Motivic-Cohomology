import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.IdentitySupport.Core.Owner

/-!
# Identity support relations for quotient trace composition

This file uses Q-linear cancellation to turn identity-support relations into
singleton identity laws.

Global identity laws for arbitrary quotient morphisms belong to the typed hom
layer, since identities are indexed by source and target objects.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The singleton candidate for a ledgered transport. -/
def LedgeredTraceTransport.singletonCandidate
    (coefficient : Rat)
    (transport : LedgeredTraceTransport)
    (ledger : TraceCorQRelationLedger) :
    TraceCorQQuotientCandidate :=
  TraceCorQQuotient.singletonCandidate
    coefficient
    transport.transport
    ledger

/-- Left identity, expanded by adding the right singleton before cancellation. -/
def LedgeredTraceTransport.leftIdentityCancellationCandidate
    (transport : LedgeredTraceTransport) :
    TraceCorQQuotientCandidate :=
  TraceCorQQuotientInput.ofFormalSumLedger
    (TraceCorQFormalSum.singleton
      1
      ((LedgeredTraceTransport.id transport.source).comp transport).transport ++
        (-1, transport.transport) ::
          (1, transport.transport) ::
            [])
    (TraceCorQRelationLedger.singleton
      (LedgeredTraceTransport.leftIdentityRelationGenerator transport))

/-- Right identity, expanded by adding the right singleton before cancellation. -/
def LedgeredTraceTransport.rightIdentityCancellationCandidate
    (transport : LedgeredTraceTransport) :
    TraceCorQQuotientCandidate :=
  TraceCorQQuotientInput.ofFormalSumLedger
    (TraceCorQFormalSum.singleton
      1
      (transport.comp (LedgeredTraceTransport.id transport.target)).transport ++
        (-1, transport.transport) ::
          (1, transport.transport) ::
            [])
    (TraceCorQRelationLedger.singleton
      (LedgeredTraceTransport.rightIdentityRelationGenerator transport))

/-- Left identity singleton equals its cancellation expansion. -/
theorem LedgeredTraceTransport.leftIdentitySingleton_eq_cancellation
    (transport : LedgeredTraceTransport) :
    TraceCorQQuotient.ofCandidate
      (LedgeredTraceTransport.singletonCandidate
        1
        ((LedgeredTraceTransport.id transport.source).comp transport)
        TraceCorQRelationLedger.empty) =
      TraceCorQQuotient.ofCandidate
        (LedgeredTraceTransport.leftIdentityCancellationCandidate transport) :=
  Eq.trans
    (show
      TraceCorQQuotient.ofCandidate
          (LedgeredTraceTransport.singletonCandidate
            1
            ((LedgeredTraceTransport.id transport.source).comp transport)
            TraceCorQRelationLedger.empty) =
        TraceCorQQuotient.ofCandidate
          (LedgeredTraceTransport.singletonCandidate
            1
            ((LedgeredTraceTransport.id transport.source).comp transport)
            (TraceCorQRelationLedger.singleton
              (LedgeredTraceTransport.leftIdentityRelationGenerator transport))) from
      TraceCorQQuotient.sound_sameFormalSum
        (TraceCorQRelationLedger.singleton
          (LedgeredTraceTransport.leftIdentityRelationGenerator transport))
        rfl)
    (Eq.symm
      (show
        TraceCorQQuotient.ofCandidate
            (LedgeredTraceTransport.leftIdentityCancellationCandidate transport) =
          TraceCorQQuotient.ofCandidate
            (LedgeredTraceTransport.singletonCandidate
              1
              ((LedgeredTraceTransport.id transport.source).comp transport)
              (TraceCorQRelationLedger.singleton
                (LedgeredTraceTransport.leftIdentityRelationGenerator transport))) from
        TraceCorQQuotient.sound_cancelAdjacentOpposite
          (TraceCorQRelationLedger.singleton
            (LedgeredTraceTransport.leftIdentityRelationGenerator transport))
          (TraceCorQFormalSum.singleton
            1
            ((LedgeredTraceTransport.id transport.source).comp transport).transport)
          TraceCorQFormalSum.zero
          (-1)
          transport.transport))

/-- Right identity singleton equals its cancellation expansion. -/
theorem LedgeredTraceTransport.rightIdentitySingleton_eq_cancellation
    (transport : LedgeredTraceTransport) :
    TraceCorQQuotient.ofCandidate
      (LedgeredTraceTransport.singletonCandidate
        1
        (transport.comp (LedgeredTraceTransport.id transport.target))
        TraceCorQRelationLedger.empty) =
      TraceCorQQuotient.ofCandidate
        (LedgeredTraceTransport.rightIdentityCancellationCandidate transport) :=
  Eq.trans
    (show
      TraceCorQQuotient.ofCandidate
          (LedgeredTraceTransport.singletonCandidate
            1
            (transport.comp (LedgeredTraceTransport.id transport.target))
            TraceCorQRelationLedger.empty) =
        TraceCorQQuotient.ofCandidate
          (LedgeredTraceTransport.singletonCandidate
            1
            (transport.comp (LedgeredTraceTransport.id transport.target))
            (TraceCorQRelationLedger.singleton
              (LedgeredTraceTransport.rightIdentityRelationGenerator transport))) from
      TraceCorQQuotient.sound_sameFormalSum
        (TraceCorQRelationLedger.singleton
          (LedgeredTraceTransport.rightIdentityRelationGenerator transport))
        rfl)
    (Eq.symm
      (show
        TraceCorQQuotient.ofCandidate
            (LedgeredTraceTransport.rightIdentityCancellationCandidate transport) =
          TraceCorQQuotient.ofCandidate
            (LedgeredTraceTransport.singletonCandidate
              1
              (transport.comp (LedgeredTraceTransport.id transport.target))
              (TraceCorQRelationLedger.singleton
                (LedgeredTraceTransport.rightIdentityRelationGenerator transport))) from
        TraceCorQQuotient.sound_cancelAdjacentOpposite
          (TraceCorQRelationLedger.singleton
            (LedgeredTraceTransport.rightIdentityRelationGenerator transport))
          (TraceCorQFormalSum.singleton
            1
            (transport.comp (LedgeredTraceTransport.id transport.target)).transport)
          TraceCorQFormalSum.zero
          (-1)
          transport.transport))

/-- Left identity holds for a coefficient-one singleton transport. -/
theorem LedgeredTraceTransport.leftIdentitySingletonQuotient_eq
    (transport : LedgeredTraceTransport) :
    TraceCorQQuotient.ofCandidate
      (LedgeredTraceTransport.singletonCandidate
        1
        ((LedgeredTraceTransport.id transport.source).comp transport)
        TraceCorQRelationLedger.empty) =
      TraceCorQQuotient.ofCandidate
        (LedgeredTraceTransport.singletonCandidate
          1
          transport
          TraceCorQRelationLedger.empty) :=
  Eq.trans
    (LedgeredTraceTransport.leftIdentitySingleton_eq_cancellation transport)
    (Eq.trans
      (Eq.symm
        (TraceCorQQuotient.add_ofCandidate
          (LedgeredTraceTransport.leftIdentitySupportCandidate transport)
          (LedgeredTraceTransport.singletonCandidate
            1
            transport
            TraceCorQRelationLedger.empty)))
      (Eq.trans
        (congrArg
          (fun supportClass =>
            TraceCorQQuotient.add
              supportClass
              (TraceCorQQuotient.ofCandidate
                (LedgeredTraceTransport.singletonCandidate
                  1
                  transport
                  TraceCorQRelationLedger.empty)))
          (LedgeredTraceTransport.leftIdentitySupportQuotient_eq_zero
            transport))
        (TraceCorQQuotient.zero_add
          (TraceCorQQuotient.ofCandidate
            (LedgeredTraceTransport.singletonCandidate
              1
              transport
              TraceCorQRelationLedger.empty)))))

/-- Right identity holds for a coefficient-one singleton transport. -/
theorem LedgeredTraceTransport.rightIdentitySingletonQuotient_eq
    (transport : LedgeredTraceTransport) :
    TraceCorQQuotient.ofCandidate
      (LedgeredTraceTransport.singletonCandidate
        1
        (transport.comp (LedgeredTraceTransport.id transport.target))
        TraceCorQRelationLedger.empty) =
      TraceCorQQuotient.ofCandidate
        (LedgeredTraceTransport.singletonCandidate
          1
          transport
          TraceCorQRelationLedger.empty) :=
  Eq.trans
    (LedgeredTraceTransport.rightIdentitySingleton_eq_cancellation transport)
    (Eq.trans
      (Eq.symm
        (TraceCorQQuotient.add_ofCandidate
          (LedgeredTraceTransport.rightIdentitySupportCandidate transport)
          (LedgeredTraceTransport.singletonCandidate
            1
            transport
            TraceCorQRelationLedger.empty)))
      (Eq.trans
        (congrArg
          (fun supportClass =>
            TraceCorQQuotient.add
              supportClass
              (TraceCorQQuotient.ofCandidate
                (LedgeredTraceTransport.singletonCandidate
                  1
                  transport
                  TraceCorQRelationLedger.empty)))
          (LedgeredTraceTransport.rightIdentitySupportQuotient_eq_zero
            transport))
        (TraceCorQQuotient.zero_add
          (TraceCorQQuotient.ofCandidate
            (LedgeredTraceTransport.singletonCandidate
              1
              transport
              TraceCorQRelationLedger.empty)))))

/-- Left identity holds for a weighted singleton transport. -/
theorem LedgeredTraceTransport.leftIdentityWeightedSingletonQuotient_eq
    (coefficient : Rat)
    (transport : LedgeredTraceTransport) :
    TraceCorQQuotient.singleton
      coefficient
      ((LedgeredTraceTransport.id transport.source).comp transport).transport =
      TraceCorQQuotient.singleton
        coefficient
        transport.transport :=
  Eq.trans
    (Eq.symm
      (Eq.trans
        (TraceCorQQuotient.smul_singleton
          coefficient
          1
          ((LedgeredTraceTransport.id transport.source).comp transport).transport)
        (congrArg
          (fun scaledCoefficient =>
            TraceCorQQuotient.singleton
              scaledCoefficient
              ((LedgeredTraceTransport.id transport.source).comp
                transport).transport)
          (mul_one coefficient))))
    (Eq.trans
      (congrArg
        (TraceCorQQuotient.smul coefficient)
        (LedgeredTraceTransport.leftIdentitySingletonQuotient_eq
          transport))
      (Eq.trans
        (TraceCorQQuotient.smul_singleton
          coefficient
          1
          transport.transport)
        (congrArg
          (fun scaledCoefficient =>
            TraceCorQQuotient.singleton
              scaledCoefficient
              transport.transport)
          (mul_one coefficient))))

/-- Right identity holds for a weighted singleton transport. -/
theorem LedgeredTraceTransport.rightIdentityWeightedSingletonQuotient_eq
    (coefficient : Rat)
    (transport : LedgeredTraceTransport) :
    TraceCorQQuotient.singleton
      coefficient
      (transport.comp (LedgeredTraceTransport.id transport.target)).transport =
      TraceCorQQuotient.singleton
        coefficient
        transport.transport :=
  Eq.trans
    (Eq.symm
      (Eq.trans
        (TraceCorQQuotient.smul_singleton
          coefficient
          1
          (transport.comp (LedgeredTraceTransport.id transport.target)).transport)
        (congrArg
          (fun scaledCoefficient =>
            TraceCorQQuotient.singleton
              scaledCoefficient
              (transport.comp
                (LedgeredTraceTransport.id transport.target)).transport)
          (mul_one coefficient))))
    (Eq.trans
      (congrArg
        (TraceCorQQuotient.smul coefficient)
        (LedgeredTraceTransport.rightIdentitySingletonQuotient_eq
          transport))
      (Eq.trans
        (TraceCorQQuotient.smul_singleton
          coefficient
          1
          transport.transport)
        (congrArg
          (fun scaledCoefficient =>
            TraceCorQQuotient.singleton
              scaledCoefficient
              transport.transport)
          (mul_one coefficient))))

/-- Regard a trace-correspondence generator as a ledgered transport. -/
def TraceCorQGenerator.toIdentityLedgeredTransport
    (generator : TraceCorQGenerator) :
    LedgeredTraceTransport :=
  LedgeredTraceTransport.ofTransportLedger
    generator
    TraceCorQRelationLedger.empty

/-- Left identity holds for a weighted singleton generator. -/
theorem TraceCorQGenerator.leftIdentityWeightedSingletonQuotient_eq
    (coefficient : Rat)
    (generator : TraceCorQGenerator) :
    TraceCorQQuotient.singleton
      coefficient
      (TraceCorQGenerator.comp
        (TraceCorQGenerator.id generator.source)
        generator) =
      TraceCorQQuotient.singleton
        coefficient
        generator :=
  LedgeredTraceTransport.leftIdentityWeightedSingletonQuotient_eq
    coefficient
    generator.toIdentityLedgeredTransport

/-- Right identity holds for a weighted singleton generator. -/
theorem TraceCorQGenerator.rightIdentityWeightedSingletonQuotient_eq
    (coefficient : Rat)
    (generator : TraceCorQGenerator) :
    TraceCorQQuotient.singleton
      coefficient
      (TraceCorQGenerator.comp
        generator
        (TraceCorQGenerator.id generator.target)) =
      TraceCorQQuotient.singleton
        coefficient
        generator :=
  LedgeredTraceTransport.rightIdentityWeightedSingletonQuotient_eq
    coefficient
    generator.toIdentityLedgeredTransport

end AnalyticMotives
end LFunctions
end Boundary

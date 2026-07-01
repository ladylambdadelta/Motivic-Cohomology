import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.LedgeredTransports.CoherenceRelations.Owner

/-!
# Coherence relation ledgers for ledgered transports

This file packages associativity and identity relation generators into finite
relation ledgers.

These ledgers are still pre-quotient data.  They record the generators that
will later be imposed by a quotient construction.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The singleton associativity relation ledger for three ledgered transports. -/
def LedgeredTraceTransport.associativityRelationLedger
    (first second third : LedgeredTraceTransport) :
    TraceCorQRelationLedger :=
  TraceCorQRelationLedger.singleton
    (LedgeredTraceTransport.associativityRelationGenerator
      first second third)

/-- The associativity relation ledger is the expected singleton. -/
theorem LedgeredTraceTransport.associativityRelationLedger_eq_singleton
    (first second third : LedgeredTraceTransport) :
    LedgeredTraceTransport.associativityRelationLedger
      first second third =
      [LedgeredTraceTransport.associativityRelationGenerator
        first second third] :=
  rfl

/-- The singleton left-identity relation ledger for a ledgered transport. -/
def LedgeredTraceTransport.leftIdentityRelationLedger
    (transport : LedgeredTraceTransport) :
    TraceCorQRelationLedger :=
  TraceCorQRelationLedger.singleton
    (LedgeredTraceTransport.leftIdentityRelationGenerator transport)

/-- The left-identity relation ledger is the expected singleton. -/
theorem LedgeredTraceTransport.leftIdentityRelationLedger_eq_singleton
    (transport : LedgeredTraceTransport) :
    LedgeredTraceTransport.leftIdentityRelationLedger transport =
      [LedgeredTraceTransport.leftIdentityRelationGenerator transport] :=
  rfl

/-- The singleton right-identity relation ledger for a ledgered transport. -/
def LedgeredTraceTransport.rightIdentityRelationLedger
    (transport : LedgeredTraceTransport) :
    TraceCorQRelationLedger :=
  TraceCorQRelationLedger.singleton
    (LedgeredTraceTransport.rightIdentityRelationGenerator transport)

/-- The right-identity relation ledger is the expected singleton. -/
theorem LedgeredTraceTransport.rightIdentityRelationLedger_eq_singleton
    (transport : LedgeredTraceTransport) :
    LedgeredTraceTransport.rightIdentityRelationLedger transport =
      [LedgeredTraceTransport.rightIdentityRelationGenerator transport] :=
  rfl

/-- The finite category-shape coherence ledger for three ledgered transports. -/
def LedgeredTraceTransport.categoryShapeRelationLedger
    (first second third : LedgeredTraceTransport) :
    TraceCorQRelationLedger :=
  TraceCorQRelationLedger.append
    (LedgeredTraceTransport.associativityRelationLedger
      first second third)
    (TraceCorQRelationLedger.append
      (LedgeredTraceTransport.leftIdentityRelationLedger first)
      (LedgeredTraceTransport.rightIdentityRelationLedger third))

/-- The category-shape ledger is associativity followed by left and right identities. -/
theorem LedgeredTraceTransport.categoryShapeRelationLedger_eq :
    (first second third : LedgeredTraceTransport) →
    LedgeredTraceTransport.categoryShapeRelationLedger
      first second third =
      LedgeredTraceTransport.associativityRelationGenerator
        first second third ::
        LedgeredTraceTransport.leftIdentityRelationGenerator first ::
          LedgeredTraceTransport.rightIdentityRelationGenerator third ::
            []
  | first, second, third => rfl

end AnalyticMotives
end LFunctions
end Boundary

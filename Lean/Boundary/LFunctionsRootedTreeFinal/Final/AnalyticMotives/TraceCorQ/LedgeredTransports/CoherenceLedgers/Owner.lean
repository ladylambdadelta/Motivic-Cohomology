import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.LedgeredTransports.CoherenceRelations.Owner

/-!
# Coherence relation ledgers for ledgered transports

This file packages associativity and identity relation generators into finite
relation ledgers.

These ledgers are pre-quotient data.  They record the generators consumed by
the quotient relation.
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

/-- The associativity relation ledger carries the associativity relation imported payload. -/
theorem LedgeredTraceTransport.associativityRelationLedger_importedRectangleCount
    (first second third : LedgeredTraceTransport) :
    (LedgeredTraceTransport.associativityRelationLedger
      first
      second
      third).importedRectangleCount =
      (LedgeredTraceTransport.associativityRelationGenerator
        first
        second
        third).importedRectangleCount +
        0 :=
  rfl

/-- The associativity relation ledger carries the associativity relation bookkeeping payload. -/
theorem LedgeredTraceTransport.associativityRelationLedger_traceBookkeepingCount
    (first second third : LedgeredTraceTransport) :
    (LedgeredTraceTransport.associativityRelationLedger
      first
      second
      third).traceBookkeepingCount =
      (LedgeredTraceTransport.associativityRelationGenerator
        first
        second
        third).traceBookkeepingCount +
        0 :=
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

/-- The left-identity relation ledger carries the left-identity relation imported payload. -/
theorem LedgeredTraceTransport.leftIdentityRelationLedger_importedRectangleCount
    (transport : LedgeredTraceTransport) :
    (LedgeredTraceTransport.leftIdentityRelationLedger
      transport).importedRectangleCount =
      (LedgeredTraceTransport.leftIdentityRelationGenerator
        transport).importedRectangleCount +
        0 :=
  rfl

/-- The left-identity relation ledger carries the left-identity relation bookkeeping payload. -/
theorem LedgeredTraceTransport.leftIdentityRelationLedger_traceBookkeepingCount
    (transport : LedgeredTraceTransport) :
    (LedgeredTraceTransport.leftIdentityRelationLedger
      transport).traceBookkeepingCount =
      (LedgeredTraceTransport.leftIdentityRelationGenerator
        transport).traceBookkeepingCount +
        0 :=
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

/-- The right-identity relation ledger carries the right-identity relation imported payload. -/
theorem LedgeredTraceTransport.rightIdentityRelationLedger_importedRectangleCount
    (transport : LedgeredTraceTransport) :
    (LedgeredTraceTransport.rightIdentityRelationLedger
      transport).importedRectangleCount =
      (LedgeredTraceTransport.rightIdentityRelationGenerator
        transport).importedRectangleCount +
        0 :=
  rfl

/-- The right-identity relation ledger carries the right-identity relation bookkeeping payload. -/
theorem LedgeredTraceTransport.rightIdentityRelationLedger_traceBookkeepingCount
    (transport : LedgeredTraceTransport) :
    (LedgeredTraceTransport.rightIdentityRelationLedger
      transport).traceBookkeepingCount =
      (LedgeredTraceTransport.rightIdentityRelationGenerator
        transport).traceBookkeepingCount +
        0 :=
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

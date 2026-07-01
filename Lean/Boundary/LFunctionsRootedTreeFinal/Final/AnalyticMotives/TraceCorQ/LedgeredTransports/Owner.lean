import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.RelationLedgers.Owner

/-!
# Ledger-supported trace transports

This file owns trace transports equipped with finite ledgers of available
relation generators.

Ledgered transports are still pre-quotient data.  Composition concatenates the
underlying rewrite paths and appends the relation ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A trace transport together with its available relation ledger. -/
abbrev LedgeredTraceTransport :=
  TraceTransport × TraceCorQRelationLedger

/-- The raw transport underlying a ledgered trace transport. -/
def LedgeredTraceTransport.transport
    (ledgered : LedgeredTraceTransport) :
    TraceTransport :=
  ledgered.1

/-- The relation ledger attached to a ledgered trace transport. -/
def LedgeredTraceTransport.ledger
    (ledgered : LedgeredTraceTransport) :
    TraceCorQRelationLedger :=
  ledgered.2

/-- Build a ledgered trace transport from a raw transport and a relation ledger. -/
def LedgeredTraceTransport.ofTransportLedger
    (transport : TraceTransport) (ledger : TraceCorQRelationLedger) :
    LedgeredTraceTransport :=
  (transport, ledger)

/-- The ledgered identity transport uses the raw identity transport and empty ledger. -/
def LedgeredTraceTransport.id
    (object : TraceTransportObject) :
    LedgeredTraceTransport :=
  (TraceTransport.id object, TraceCorQRelationLedger.empty)

/-- The source presentation of a ledgered trace transport. -/
def LedgeredTraceTransport.source
    (ledgered : LedgeredTraceTransport) :
    TraceTransportObject :=
  ledgered.transport.source

/-- The target presentation of a ledgered trace transport. -/
def LedgeredTraceTransport.target
    (ledgered : LedgeredTraceTransport) :
    TraceTransportObject :=
  ledgered.transport.target

/-- The rewrite path carried by a ledgered trace transport. -/
def LedgeredTraceTransport.path
    (ledgered : LedgeredTraceTransport) :
    TraceRewritePath :=
  ledgered.transport.path

/-- Compose ledgered trace transports by composing transports and appending ledgers. -/
def LedgeredTraceTransport.comp
    (first second : LedgeredTraceTransport) :
    LedgeredTraceTransport :=
  (first.transport.comp second.transport,
    TraceCorQRelationLedger.append first.ledger second.ledger)

/-- The raw transport of a composed ledgered transport is the raw composed transport. -/
theorem LedgeredTraceTransport.comp_transport
    (first second : LedgeredTraceTransport) :
    (first.comp second).transport =
      first.transport.comp second.transport :=
  rfl

/-- The ledger of a composed ledgered transport is the appended ledger. -/
theorem LedgeredTraceTransport.comp_ledger
    (first second : LedgeredTraceTransport) :
    (first.comp second).ledger =
      TraceCorQRelationLedger.append first.ledger second.ledger :=
  rfl

/-- The source of a composed ledgered transport is the source of the first transport. -/
theorem LedgeredTraceTransport.comp_source
    (first second : LedgeredTraceTransport) :
    (first.comp second).source =
      first.source :=
  rfl

/-- The target of a composed ledgered transport is the target of the second transport. -/
theorem LedgeredTraceTransport.comp_target
    (first second : LedgeredTraceTransport) :
    (first.comp second).target =
      second.target :=
  rfl

/-- The path of a composed ledgered transport is the concatenated path. -/
theorem LedgeredTraceTransport.comp_path
    (first second : LedgeredTraceTransport) :
    (first.comp second).path =
      first.path.comp second.path :=
  rfl

/--
The associativity coherence cell between the two raw path parenthesizations of
three ledgered transports.
-/
def LedgeredTraceTransport.compAssociativityCoherence
    (first second third : LedgeredTraceTransport) :
    TraceCoherenceCell :=
  TraceCoherenceCell.associativity
    ((first.comp second).comp third).path
    (first.comp (second.comp third)).path

/-- The ledger component of triple composition associates. -/
theorem LedgeredTraceTransport.comp_ledger_assoc
    (first second third : LedgeredTraceTransport) :
    ((first.comp second).comp third).ledger =
      (first.comp (second.comp third)).ledger :=
  TraceCorQRelationLedger.append_assoc
    first.ledger
    second.ledger
    third.ledger

/-- The associativity coherence cell has associativity kind. -/
theorem LedgeredTraceTransport.compAssociativityCoherence_kind
    (first second third : LedgeredTraceTransport) :
    (LedgeredTraceTransport.compAssociativityCoherence
      first second third).kind =
      TraceCoherenceKind.associativity :=
  rfl

/-- The source of the associativity coherence is the left-parenthesized path. -/
theorem LedgeredTraceTransport.compAssociativityCoherence_source
    (first second third : LedgeredTraceTransport) :
    (LedgeredTraceTransport.compAssociativityCoherence
      first second third).source =
      ((first.comp second).comp third).path :=
  rfl

/-- The target of the associativity coherence is the right-parenthesized path. -/
theorem LedgeredTraceTransport.compAssociativityCoherence_target
    (first second third : LedgeredTraceTransport) :
    (LedgeredTraceTransport.compAssociativityCoherence
      first second third).target =
      (first.comp (second.comp third)).path :=
  rfl

/-- The raw transport of a ledgered identity is the raw identity transport. -/
theorem LedgeredTraceTransport.id_transport
    (object : TraceTransportObject) :
    (LedgeredTraceTransport.id object).transport =
      TraceTransport.id object :=
  rfl

/-- The ledger of a ledgered identity is empty. -/
theorem LedgeredTraceTransport.id_ledger
    (object : TraceTransportObject) :
    (LedgeredTraceTransport.id object).ledger =
      TraceCorQRelationLedger.empty :=
  rfl

/-- The source of a ledgered identity is its object. -/
theorem LedgeredTraceTransport.id_source
    (object : TraceTransportObject) :
    (LedgeredTraceTransport.id object).source =
      object :=
  rfl

/-- The target of a ledgered identity is its object. -/
theorem LedgeredTraceTransport.id_target
    (object : TraceTransportObject) :
    (LedgeredTraceTransport.id object).target =
      object :=
  rfl

/-- The path of a ledgered identity is the identity path on the object's source. -/
theorem LedgeredTraceTransport.id_path
    (object : TraceTransportObject) :
    (LedgeredTraceTransport.id object).path =
      TraceRewritePath.id object.source :=
  rfl

/-- The left-identity coherence cell for composing an identity before a ledgered transport. -/
def LedgeredTraceTransport.leftIdentityCoherence
    (transport : LedgeredTraceTransport) :
    TraceCoherenceCell :=
  TraceCoherenceCell.leftIdentity
    ((LedgeredTraceTransport.id transport.source).comp transport).path
    transport.path

/-- The right-identity coherence cell for composing a ledgered transport before an identity. -/
def LedgeredTraceTransport.rightIdentityCoherence
    (transport : LedgeredTraceTransport) :
    TraceCoherenceCell :=
  TraceCoherenceCell.rightIdentity
    (transport.comp (LedgeredTraceTransport.id transport.target)).path
    transport.path

/-- The ledger of a left-identity composition is the original ledger. -/
theorem LedgeredTraceTransport.leftIdentity_ledger
    (transport : LedgeredTraceTransport) :
    ((LedgeredTraceTransport.id transport.source).comp transport).ledger =
      transport.ledger :=
  TraceCorQRelationLedger.empty_append transport.ledger

/-- The ledger of a right-identity composition is the original ledger. -/
theorem LedgeredTraceTransport.rightIdentity_ledger
    (transport : LedgeredTraceTransport) :
    (transport.comp (LedgeredTraceTransport.id transport.target)).ledger =
      transport.ledger :=
  TraceCorQRelationLedger.append_empty transport.ledger

/-- The left-identity coherence cell has left-identity kind. -/
theorem LedgeredTraceTransport.leftIdentityCoherence_kind
    (transport : LedgeredTraceTransport) :
    (LedgeredTraceTransport.leftIdentityCoherence transport).kind =
      TraceCoherenceKind.leftIdentity :=
  rfl

/-- The source of the left-identity coherence is the composed identity-left path. -/
theorem LedgeredTraceTransport.leftIdentityCoherence_source
    (transport : LedgeredTraceTransport) :
    (LedgeredTraceTransport.leftIdentityCoherence transport).source =
      ((LedgeredTraceTransport.id transport.source).comp transport).path :=
  rfl

/-- The target of the left-identity coherence is the original transport path. -/
theorem LedgeredTraceTransport.leftIdentityCoherence_target
    (transport : LedgeredTraceTransport) :
    (LedgeredTraceTransport.leftIdentityCoherence transport).target =
      transport.path :=
  rfl

/-- The right-identity coherence cell has right-identity kind. -/
theorem LedgeredTraceTransport.rightIdentityCoherence_kind
    (transport : LedgeredTraceTransport) :
    (LedgeredTraceTransport.rightIdentityCoherence transport).kind =
      TraceCoherenceKind.rightIdentity :=
  rfl

/-- The source of the right-identity coherence is the composed identity-right path. -/
theorem LedgeredTraceTransport.rightIdentityCoherence_source
    (transport : LedgeredTraceTransport) :
    (LedgeredTraceTransport.rightIdentityCoherence transport).source =
      (transport.comp (LedgeredTraceTransport.id transport.target)).path :=
  rfl

/-- The target of the right-identity coherence is the original transport path. -/
theorem LedgeredTraceTransport.rightIdentityCoherence_target
    (transport : LedgeredTraceTransport) :
    (LedgeredTraceTransport.rightIdentityCoherence transport).target =
      transport.path :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

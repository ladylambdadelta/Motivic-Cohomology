import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Relations.Owner

/-!
# Relation ledgers for Q-linear trace correspondences

This file owns finite ledgers of trace-correspondence relation generators.

A ledger is pre-quotient data: it records which certified coherences are
available to generate relations.  It does not identify morphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A finite ledger of trace-correspondence relation generators. -/
abbrev TraceCorQRelationLedger :=
  List TraceCorQRelationGenerator

/-- The empty relation ledger. -/
def TraceCorQRelationLedger.empty : TraceCorQRelationLedger :=
  []

/-- A singleton relation ledger. -/
def TraceCorQRelationLedger.singleton
    (relation : TraceCorQRelationGenerator) :
    TraceCorQRelationLedger :=
  [relation]

/-- Append two relation ledgers. -/
def TraceCorQRelationLedger.append
    (first second : TraceCorQRelationLedger) :
    TraceCorQRelationLedger :=
  first ++ second

/-- Appending the empty ledger on the left leaves a ledger unchanged. -/
theorem TraceCorQRelationLedger.empty_append
    (ledger : TraceCorQRelationLedger) :
    TraceCorQRelationLedger.append
      TraceCorQRelationLedger.empty
      ledger =
      ledger :=
  rfl

/-- Appending a singleton ledger on the left conses its relation onto the ledger. -/
theorem TraceCorQRelationLedger.singleton_append
    (relation : TraceCorQRelationGenerator)
    (ledger : TraceCorQRelationLedger) :
    TraceCorQRelationLedger.append
      (TraceCorQRelationLedger.singleton relation)
      ledger =
      relation :: ledger :=
  rfl

/-- Appending the empty ledger on the right leaves a ledger unchanged. -/
theorem TraceCorQRelationLedger.append_empty
    (ledger : TraceCorQRelationLedger) :
    TraceCorQRelationLedger.append
      ledger
      TraceCorQRelationLedger.empty =
      ledger :=
  List.append_nil ledger

/-- Ledger append is associative. -/
theorem TraceCorQRelationLedger.append_assoc
    (first second third : TraceCorQRelationLedger) :
    TraceCorQRelationLedger.append
      (TraceCorQRelationLedger.append first second)
      third =
      TraceCorQRelationLedger.append
        first
        (TraceCorQRelationLedger.append second third) :=
  List.append_assoc first second third

end AnalyticMotives
end LFunctions
end Boundary

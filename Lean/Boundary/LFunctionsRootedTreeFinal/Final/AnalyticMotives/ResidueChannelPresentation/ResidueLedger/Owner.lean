import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceExpression.QLinear.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Stage.Owner

/-!
# Residue ledgers

This file owns residue ledgers: the signed, Q-linear bookkeeping of residues
created by contour deformation.

Residue ledgers are the analytic source of the boundary terms consumed by
relations in the trace category.  They are the contour-calculus bookkeeping
interface for residue-theorem input imported from `Final`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- One syntactic residue-ledger entry, indexed by the boundary face. -/
abbrev ResidueLedgerEntry :=
  TraceFaceIndex × QTraceExpression

/-- A finite syntactic residue ledger. -/
abbrev ResidueLedger :=
  List ResidueLedgerEntry

/-- The empty residue ledger. -/
def ResidueLedger.empty : ResidueLedger :=
  []

/-- Add one residue-ledger entry at the front of a ledger. -/
def ResidueLedger.cons
    (entry : ResidueLedgerEntry) (ledger : ResidueLedger) : ResidueLedger :=
  entry :: ledger

/-- The empty residue ledger is the empty list. -/
theorem ResidueLedger.empty_eq_nil :
    ResidueLedger.empty = [] :=
  rfl

/-- Ledger cons is list cons. -/
theorem ResidueLedger.cons_eq_cons
    (entry : ResidueLedgerEntry)
    (ledger : ResidueLedger) :
    ResidueLedger.cons entry ledger =
      entry :: ledger :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

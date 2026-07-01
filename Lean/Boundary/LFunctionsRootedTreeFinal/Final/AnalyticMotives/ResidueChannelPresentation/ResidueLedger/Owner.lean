import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceExpression.QLinear.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Stage.Owner

/-!
# Residue ledgers

This file owns residue ledgers: the signed, Q-linear bookkeeping of residues
created by contour deformation.

Residue ledgers are the analytic source of the boundary terms that later become
relations in the trace category.  They should be built from the residue theorem
and contour calculus already present in `Final`.
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

end AnalyticMotives
end LFunctions
end Boundary

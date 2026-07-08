import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.ResidueLedger.Owner

/-!
# Top-root residue ledgers

This file exposes finite residue ledgers for contour-deformation bookkeeping.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes the empty residue ledger. -/
def AnalyticMotivesRoot.residueLedger_empty : ResidueLedger :=
  ResidueLedger.empty

/-- The top root exposes residue-ledger cons. -/
def AnalyticMotivesRoot.residueLedger_cons
    (entry : ResidueLedgerEntry) (ledger : ResidueLedger) :
    ResidueLedger :=
  ResidueLedger.cons entry ledger

/-- The top root exposes the empty residue ledger as the empty list. -/
theorem AnalyticMotivesRoot.residueLedger_empty_eq_nil :
    ResidueLedger.empty = [] :=
  ResidueLedger.empty_eq_nil

/-- The top root exposes residue-ledger cons as list cons. -/
theorem AnalyticMotivesRoot.residueLedger_cons_eq_cons
    (entry : ResidueLedgerEntry)
    (ledger : ResidueLedger) :
    ResidueLedger.cons entry ledger =
      entry :: ledger :=
  ResidueLedger.cons_eq_cons entry ledger

end AnalyticMotives
end LFunctions
end Boundary

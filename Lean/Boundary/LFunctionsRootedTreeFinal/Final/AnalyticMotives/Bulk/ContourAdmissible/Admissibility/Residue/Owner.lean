import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.ResidueLedger.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.Admissibility.Contour.Owner

/-!
# Residue-ledger admissibility data

This file owns the categorical residue ledger selected for a contour system.
Residues remain morphism-level data; scalar traces are downstream realizations.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Residue-ledger data selected for a contour-admissible system. -/
structure ResidueLedgerAdmissibility {X : AnalyticBulkCore}
    {K : CompactificationAdmissibility X}
    {B : BoundaryAdmissibility K}
    (C : ContourSystemAdmissibility B) where
  ledger : AnalyticResidueLedger C.system

namespace ResidueLedgerAdmissibility

/-- The selected residue ledger. -/
def data {X : AnalyticBulkCore}
    {K : CompactificationAdmissibility X}
    {B : BoundaryAdmissibility K}
    {C : ContourSystemAdmissibility B}
    (R : ResidueLedgerAdmissibility C) :
    AnalyticResidueLedger C.system :=
  R.ledger

/-- The residue map at a contour stage and boundary face. -/
def residueAt {X : AnalyticBulkCore}
    {K : CompactificationAdmissibility X}
    {B : BoundaryAdmissibility K}
    {C : ContourSystemAdmissibility B}
    (R : ResidueLedgerAdmissibility C)
    (s : C.system.exhaustion.Stage)
    (i : B.system.FaceIndex) :
    AnalyticResidueMap (C.system.exhaustion.chain s) (B.system.face i) :=
  R.ledger.residueAt s i

end ResidueLedgerAdmissibility

end AnalyticMotives
end LFunctions
end Boundary

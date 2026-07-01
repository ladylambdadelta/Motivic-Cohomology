import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.BoundarySystem.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.ContourSystem.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.ResidueLedger.Maps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.ResidueLedger.Filtration.Owner

/-!
# Residue ledgers for analytic bulks

Residue ledgers are morphism-level boundary data: residues should be maps from
bulk contour chains to boundary-stratum contour chains, compatible with
correspondence pushforward.  Scalar residue sums belong to trace realization,
not to the definition of the bulk object.

Dependency order: residue maps first, then the residue-depth filtration they
generate.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
A residue ledger for a contour system.  For every contour stage and every
boundary face it records a categorical residue map, together with the
residue-depth filtration on faces.
-/
structure AnalyticResidueLedger {X : AnalyticBulkCore}
    {B : AnalyticBoundarySystem X}
    (C : AnalyticContourSystem B) where
  residue :
    (s : C.exhaustion.Stage) →
      (i : B.FaceIndex) →
        AnalyticResidueMap (C.exhaustion.chain s) (B.face i)
  filtration : AnalyticResidueFiltration B

namespace AnalyticResidueLedger

/-- The residue map for a contour stage and boundary face. -/
def residueAt {X : AnalyticBulkCore} {B : AnalyticBoundarySystem X}
    {C : AnalyticContourSystem B}
    (R : AnalyticResidueLedger C)
    (s : C.exhaustion.Stage) (i : B.FaceIndex) :
    AnalyticResidueMap (C.exhaustion.chain s) (B.face i) :=
  R.residue s i

/-- The residue-depth filtration carried by a residue ledger. -/
def filtrationData {X : AnalyticBulkCore} {B : AnalyticBoundarySystem X}
    {C : AnalyticContourSystem B}
    (R : AnalyticResidueLedger C) : AnalyticResidueFiltration B :=
  R.filtration

end AnalyticResidueLedger

end AnalyticMotives
end LFunctions
end Boundary

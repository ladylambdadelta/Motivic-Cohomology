import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.Core.Base.Owner
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Analytic carriers over the arithmetic base

This file owns the carrier layer for analytic bulk objects over the arithmetic
base.  Boundary compactifications, contours, and residue ledgers are attached
only after this carrier layer is fixed.

Foundational source: mathlib's `TopCat` API supplies the topological carrier
side of analytic bulks.  Additional analytic structure belongs here only when
it is defined from the carrier construction.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic carrier attached to an arithmetic base. -/
abbrev AnalyticCarrier (_S : ArithmeticBase) : Type _ :=
  TopCat

/--
The minimal bulk core: an arithmetic shadow together with an analytic carrier.
Boundary systems, contour systems, residue ledgers, descent data, and interval
homotopies are added by downstream owner layers.
-/
structure AnalyticBulkCore where
  base : ArithmeticBase
  carrier : AnalyticCarrier base

end AnalyticMotives
end LFunctions
end Boundary

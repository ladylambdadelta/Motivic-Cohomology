import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.Core.Base.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.Core.Carrier.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.Core.Maps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.Core.Products.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.Core.RHContour.Owner

/-!
# Analytic bulk core

This file owns the object-level analytic bulk core.  It should remain smaller
than the contour-admissible package: compactifications, boundary systems,
contours, residues, descent, and interval data live in sibling owner files.

The intended comparison target is algebraic geometry over `ℚ`, but this file
does not identify analytic bulks with Voevodsky motives.  Analytic contour
correspondences are the next layer.

Research input: the object core should be small.  Compactification, boundary,
contour, residue, descent, and interval data are attached as separate owner
layers so later proofs do not unpack one monolithic structure.

Execution order from this file:

1. arithmetic base;
2. analytic carrier over that base;
3. maps of analytic bulk cores;
4. products needed by correspondence supports;
5. only then boundary and contour systems.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The constructive RH-backed contour core exposed by the analytic bulk layer. -/
abbrev ConstructiveAnalyticBulkCore :=
  RHContourBulkCore

namespace ConstructiveAnalyticBulkCore

/-- The packet underlying a constructive analytic bulk core. -/
def packet (X : ConstructiveAnalyticBulkCore) :
    ZetaAdmissibleFunction :=
  RHContourBulkCore.packet X

/-- The RH contour family underlying a constructive analytic bulk core. -/
def contourFamily (X : ConstructiveAnalyticBulkCore) :
    RHContourFamily :=
  RHContourBulkCore.contourFamily X

/-- The RH analytic package underlying a constructive analytic bulk core. -/
def analyticPackage (X : ConstructiveAnalyticBulkCore) :
    RHContourAnalyticPackage X.packet X.contourFamily :=
  RHContourBulkCore.analyticPackage X

/-- The rectangle at height `T` in a constructive analytic bulk core. -/
def rectangle (X : ConstructiveAnalyticBulkCore) (T : ℝ) :
    RHContourRectangle :=
  RHContourBulkCore.rectangle X T

/-- The contour boundary at height `T` in a constructive analytic bulk core. -/
def boundary (X : ConstructiveAnalyticBulkCore) (T : ℝ) : Set ℂ :=
  RHContourBulkCore.boundary X T

/-- The contour interior at height `T` in a constructive analytic bulk core. -/
def interior (X : ConstructiveAnalyticBulkCore) (T : ℝ) : Set ℂ :=
  RHContourBulkCore.interior X T

/-- The RH singular-point predicate for a constructive analytic bulk core. -/
def singularPoint (X : ConstructiveAnalyticBulkCore) (z : ℂ) : Prop :=
  RHContourBulkCore.singularPoint X z

end ConstructiveAnalyticBulkCore

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.BoundarySystem.Owner

/-!
# Contour chains on analytic bulks

This file owns contour-chain data on analytic bulks with boundary systems.
Exhaustions, deformations, refinements, and residues are downstream.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
A contour chain on a bulk with boundary system.  The chain has its own core and
maps into the compactified bulk, so later residue maps can land on boundary
strata before any numerical trace is taken.
-/
structure AnalyticContourChain {X : AnalyticBulkCore}
    (B : AnalyticBoundarySystem X) where
  domain : AnalyticBulkCore
  compactifiedMap :
    AnalyticBulkCoreHom domain B.compactification.compactified

namespace AnalyticContourChain

/-- The source core of a contour chain. -/
def source {X : AnalyticBulkCore} {B : AnalyticBoundarySystem X}
    (C : AnalyticContourChain B) : AnalyticBulkCore :=
  C.domain

/-- The map from a contour chain into the compactified bulk. -/
def map {X : AnalyticBulkCore} {B : AnalyticBoundarySystem X}
    (C : AnalyticContourChain B) :
    AnalyticBulkCoreHom C.domain B.compactification.compactified :=
  C.compactifiedMap

end AnalyticContourChain

end AnalyticMotives
end LFunctions
end Boundary

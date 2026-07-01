import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.BoundarySystem.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.ContourSystem.Chains.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.ContourSystem.Exhaustions.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.ContourSystem.Deformations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.ContourSystem.Refinements.Owner

/-!
# Contour systems for analytic bulks

Contour systems record admissible contour exhaustions and deformation data on
bulk analytic objects.  Explicit-formula vertical channels become realization
evidence after contour-compatible correspondences have been defined.

Dependency order: contour chains, exhaustions, deformations, then refinements.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
An indexed contour system on a bulk with boundary system.  It packages a
contour exhaustion together with chosen deformation and refinement data between
chains in that exhaustion.
-/
structure AnalyticContourSystem {X : AnalyticBulkCore}
    (B : AnalyticBoundarySystem X) where
  exhaustion : AnalyticContourExhaustion B
  DeformationIndex :
    exhaustion.Stage → exhaustion.Stage → Type
  deformation :
    {s t : exhaustion.Stage} →
      DeformationIndex s t →
        AnalyticContourDeformation (exhaustion.chain s) (exhaustion.chain t)
  RefinementIndex :
    exhaustion.Stage → exhaustion.Stage → Type
  refinement :
    {refined coarse : exhaustion.Stage} →
      RefinementIndex refined coarse →
        AnalyticContourRefinement
          (exhaustion.chain refined) (exhaustion.chain coarse)

namespace AnalyticContourSystem

/-- The exhaustion underlying a contour system. -/
def exhaustionData {X : AnalyticBulkCore} {B : AnalyticBoundarySystem X}
    (C : AnalyticContourSystem B) : AnalyticContourExhaustion B :=
  C.exhaustion

/-- The contour chain selected by a stage of a contour system. -/
def chainAt {X : AnalyticBulkCore} {B : AnalyticBoundarySystem X}
    (C : AnalyticContourSystem B) (s : C.exhaustion.Stage) :
    AnalyticContourChain B :=
  C.exhaustion.chain s

end AnalyticContourSystem

end AnalyticMotives
end LFunctions
end Boundary

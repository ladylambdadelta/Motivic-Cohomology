import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.StableCategory.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Structures.WeightStructure.GeometricWeight.Strata.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Structures.WeightStructure.GeometricWeight.ResidueDepth.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Structures.WeightStructure.GeometricWeight.Candidate.Owner

/-!
# Geometric-contour weights

This file owns the geometric source of weights: compactification strata,
boundary depth, and residue filtration on analytic contour motives.  This layer
is upstream from trace positivity checks.

Dependency order: strata, residue depth, then weight candidate.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Geometric-contour weight data on the stable analytic motive package.  This is
the upstream source of weights before any trace-realization compatibility
check.
-/
structure GeometricContourWeightData where
  stablePackage : StableAnalyticMotivePackage
  weightCandidate :
    GeometricWeightCandidate stablePackage.infinityInterface

namespace GeometricContourWeightData

/-- The stable analytic motive package carrying geometric weights. -/
def stable (W : GeometricContourWeightData) :
    StableAnalyticMotivePackage :=
  W.stablePackage

/-- The geometric weight candidate carried by geometric-contour weight data. -/
def candidate (W : GeometricContourWeightData) :
    GeometricWeightCandidate W.stablePackage.infinityInterface :=
  W.weightCandidate

/-- The stratum selected by a geometric-contour weight index. -/
def stratumAt (W : GeometricContourWeightData)
    (i : W.weightCandidate.StratumIndex) :
    GeometricWeightStratum W.stablePackage.infinityInterface :=
  W.weightCandidate.stratumAt i

/-- The stable object selected by a geometric-contour weight index. -/
def objectAt (W : GeometricContourWeightData)
    (i : W.weightCandidate.StratumIndex) :
    W.stablePackage.infinityInterface.Object :=
  W.weightCandidate.objectAt i

/-- The contour-admissible bulk selected by a geometric-contour weight index. -/
def bulkAt (W : GeometricContourWeightData)
    (i : W.weightCandidate.StratumIndex) :
    ContourAdmissibleBulk :=
  W.weightCandidate.bulkAt i

/-- The boundary face selected by a geometric-contour weight index. -/
def faceAt (W : GeometricContourWeightData)
    (i : W.weightCandidate.StratumIndex) :
    AnalyticBoundaryFace (W.bulkAt i).boundary.compactification :=
  W.weightCandidate.faceAt i

/-- The residue depth selected by a geometric-contour weight index. -/
def depthAt (W : GeometricContourWeightData)
    (i : W.weightCandidate.StratumIndex) :
    Nat :=
  W.weightCandidate.depthAt i

/-- The residue-depth filtration selected by a geometric-contour weight index. -/
def filtrationAt (W : GeometricContourWeightData)
    (i : W.weightCandidate.StratumIndex) :
    AnalyticResidueFiltration (W.bulkAt i).boundary :=
  W.weightCandidate.filtrationAt i

/-- The selected residue depth agrees with the selected residue filtration. -/
theorem depth_eq_filtrationAt (W : GeometricContourWeightData)
    (i : W.weightCandidate.StratumIndex) :
    W.depthAt i =
      (W.filtrationAt i).depth (W.stratumAt i).faceIndex :=
  GeometricWeightCandidate.depth_eq_filtrationAt W.weightCandidate i

/-- Membership in the lower-weight class of geometric-contour weight data. -/
def inLowerWeight (W : GeometricContourWeightData)
    (n : Int) (X : W.stablePackage.infinityInterface.Object) : Type :=
  W.weightCandidate.inLowerWeight n X

/-- Membership in the upper-weight class of geometric-contour weight data. -/
def inUpperWeight (W : GeometricContourWeightData)
    (n : Int) (X : W.stablePackage.infinityInterface.Object) : Type :=
  W.weightCandidate.inUpperWeight n X

end GeometricContourWeightData

end AnalyticMotives
end LFunctions
end Boundary

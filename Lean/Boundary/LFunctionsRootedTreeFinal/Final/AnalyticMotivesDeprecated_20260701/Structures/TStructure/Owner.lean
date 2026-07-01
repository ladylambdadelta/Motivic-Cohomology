import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.StableCategory.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Structures.TStructure.Candidate.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Structures.TStructure.ContourAmplitude.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Structures.TStructure.TruncationCalculus.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Structures.TStructure.Orthogonality.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Structures.TStructure.Assembly.Owner
import Mathlib.CategoryTheory.Triangulated.TStructure.Basic

/-!
# Motivic `t`-structure for analytic motives

The analytic motivic `t`-structure belongs downstream from the stable category
and the contour amplitude calculus.  Aisles, coaisles, truncation functors, and
orthogonality are proved in this lane rather than assumed by the trace facade.

Dependency order: candidate aisles/coaisles, contour amplitude, truncation
calculus, orthogonality, then assembly.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Analytic motivic `t`-structure data on a stable analytic motive package.  This
package owns the candidate aisles/coaisles, truncation calculus, orthogonality,
and assembly data in the analytic lane.
-/
structure AnalyticMotivicTStructureData where
  stablePackage : StableAnalyticMotivePackage
  assembly : AnalyticTStructureAssembly stablePackage

namespace AnalyticMotivicTStructureData

/-- The stable analytic motive package carrying the analytic motivic `t`-structure. -/
def stable (T : AnalyticMotivicTStructureData) :
    StableAnalyticMotivePackage :=
  T.stablePackage

/-- The assembled analytic `t`-structure data. -/
def assembled (T : AnalyticMotivicTStructureData) :
    AnalyticTStructureAssembly T.stablePackage :=
  T.assembly

/-- The candidate aisle/coaisle data in the analytic motivic `t`-structure. -/
def candidate (T : AnalyticMotivicTStructureData) :
    AnalyticTStructureCandidate T.stablePackage :=
  T.assembly.candidate

/-- The truncation calculus in the analytic motivic `t`-structure. -/
def truncation (T : AnalyticMotivicTStructureData) :
    AnalyticTruncationCalculus T.assembly.candidate :=
  T.assembly.truncation

/-- The orthogonality data in the analytic motivic `t`-structure. -/
def orthogonality (T : AnalyticMotivicTStructureData) :
    AnalyticTStructureOrthogonality T.assembly.truncation :=
  T.assembly.orthogonality

/-- The lower truncation object in the analytic motivic `t`-structure. -/
def lower (T : AnalyticMotivicTStructureData)
    (n : Int) (X : T.stablePackage.infinityInterface.Object) :
    T.stablePackage.infinityInterface.Object :=
  T.assembly.lower n X

/-- The upper truncation object in the analytic motivic `t`-structure. -/
def upper (T : AnalyticMotivicTStructureData)
    (n : Int) (X : T.stablePackage.infinityInterface.Object) :
    T.stablePackage.infinityInterface.Object :=
  T.assembly.upper n X

/-- The lower truncation map in the analytic motivic `t`-structure. -/
def lowerToObject (T : AnalyticMotivicTStructureData)
    (n : Int) (X : T.stablePackage.infinityInterface.Object) :
    T.lower n X → X :=
  T.assembly.lowerToObject n X

/-- The upper truncation map in the analytic motivic `t`-structure. -/
def objectToUpper (T : AnalyticMotivicTStructureData)
    (n : Int) (X : T.stablePackage.infinityInterface.Object) :
    X → T.upper n X :=
  T.assembly.objectToUpper n X

/-- Lower truncations lie in the analytic motivic nonpositive aisle. -/
theorem lower_membership (T : AnalyticMotivicTStructureData)
    (n : Int) (X : T.stablePackage.infinityInterface.Object) :
    T.candidate.nonpositive (T.lower n X) :=
  AnalyticTStructureAssembly.lower_membership T.assembly n X

/-- Upper truncations lie in the analytic motivic nonnegative coaisle. -/
theorem upper_membership (T : AnalyticMotivicTStructureData)
    (n : Int) (X : T.stablePackage.infinityInterface.Object) :
    T.candidate.nonnegative (T.upper n X) :=
  AnalyticTStructureAssembly.upper_membership T.assembly n X

/-- Orthogonality eliminates maps from the aisle to shifted coaisle objects. -/
def noMap (T : AnalyticMotivicTStructureData)
    (X Y : T.stablePackage.infinityInterface.Object)
    (hX : T.candidate.nonpositive X)
    (hY : T.candidate.nonnegative Y)
    (f : T.orthogonality.Hom X (T.candidate.shiftDown Y)) :
    Empty :=
  T.assembly.noMap X Y hX hY f

end AnalyticMotivicTStructureData

end AnalyticMotives
end LFunctions
end Boundary

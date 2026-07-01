import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Structures.TStructure.Orthogonality.Owner

/-!
# Assembly of the analytic motivic `t`-structure

This file owns the assembly of the analytic motivic `t`-structure from
candidate data, truncation calculus, and orthogonality.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Assembled analytic motivic `t`-structure data: candidate aisles/coaisles,
truncation calculus, and orthogonality.
-/
structure AnalyticTStructureAssembly
    (P : StableAnalyticMotivePackage) where
  candidate : AnalyticTStructureCandidate P
  truncation : AnalyticTruncationCalculus candidate
  orthogonality : AnalyticTStructureOrthogonality truncation

namespace AnalyticTStructureAssembly

/-- The candidate aisle/coaisle data in an assembled analytic `t`-structure. -/
def candidateData {P : StableAnalyticMotivePackage}
    (A : AnalyticTStructureAssembly P) :
    AnalyticTStructureCandidate P :=
  A.candidate

/-- The truncation calculus in an assembled analytic `t`-structure. -/
def truncationData {P : StableAnalyticMotivePackage}
    (A : AnalyticTStructureAssembly P) :
    AnalyticTruncationCalculus A.candidate :=
  A.truncation

/-- The orthogonality data in an assembled analytic `t`-structure. -/
def orthogonalityData {P : StableAnalyticMotivePackage}
    (A : AnalyticTStructureAssembly P) :
    AnalyticTStructureOrthogonality A.truncation :=
  A.orthogonality

/-- The lower truncation object in an assembled analytic `t`-structure. -/
def lower {P : StableAnalyticMotivePackage}
    (A : AnalyticTStructureAssembly P)
    (n : Int) (X : P.infinityInterface.Object) :
    P.infinityInterface.Object :=
  A.truncation.lower n X

/-- The upper truncation object in an assembled analytic `t`-structure. -/
def upper {P : StableAnalyticMotivePackage}
    (A : AnalyticTStructureAssembly P)
    (n : Int) (X : P.infinityInterface.Object) :
    P.infinityInterface.Object :=
  A.truncation.upper n X

/-- The lower truncation map in an assembled analytic `t`-structure. -/
def lowerToObject {P : StableAnalyticMotivePackage}
    (A : AnalyticTStructureAssembly P)
    (n : Int) (X : P.infinityInterface.Object) :
    A.lower n X → X :=
  A.truncation.lowerToObject n X

/-- The upper truncation map in an assembled analytic `t`-structure. -/
def objectToUpper {P : StableAnalyticMotivePackage}
    (A : AnalyticTStructureAssembly P)
    (n : Int) (X : P.infinityInterface.Object) :
    X → A.upper n X :=
  A.truncation.objectToUpper n X

/-- Lower truncations lie in the assembled candidate nonpositive aisle. -/
theorem lower_membership {P : StableAnalyticMotivePackage}
    (A : AnalyticTStructureAssembly P)
    (n : Int) (X : P.infinityInterface.Object) :
    A.candidate.nonpositive (A.lower n X) :=
  AnalyticTruncationCalculus.lower_membership A.truncation n X

/-- Upper truncations lie in the assembled candidate nonnegative coaisle. -/
theorem upper_membership {P : StableAnalyticMotivePackage}
    (A : AnalyticTStructureAssembly P)
    (n : Int) (X : P.infinityInterface.Object) :
    A.candidate.nonnegative (A.upper n X) :=
  AnalyticTruncationCalculus.upper_membership A.truncation n X

/-- Orthogonality eliminates maps from the assembled aisle to shifted coaisle objects. -/
def noMap {P : StableAnalyticMotivePackage}
    (A : AnalyticTStructureAssembly P)
    (X Y : P.infinityInterface.Object)
    (hX : A.candidate.nonpositive X)
    (hY : A.candidate.nonnegative Y)
    (f : A.orthogonality.Hom X (A.candidate.shiftDown Y)) :
    Empty :=
  A.orthogonality.noMap X Y hX hY f

end AnalyticTStructureAssembly

end AnalyticMotives
end LFunctions
end Boundary

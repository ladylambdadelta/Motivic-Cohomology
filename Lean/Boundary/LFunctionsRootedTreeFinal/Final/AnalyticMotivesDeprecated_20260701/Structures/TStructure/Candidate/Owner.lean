import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.StableCategory.Owner

/-!
# Candidate data for the analytic motivic `t`-structure

This file owns the first layer of the analytic motivic `t`-structure: the
candidate aisles and coaisles before truncation, orthogonality, and extension
closure are assembled in the parent owner.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Candidate aisle and coaisle data for the analytic motivic `t`-structure on a
stable analytic motive package.
-/
structure AnalyticTStructureCandidate
    (P : StableAnalyticMotivePackage) where
  nonpositive : P.infinityInterface.Object → Type
  nonnegative : P.infinityInterface.Object → Type
  shiftDown :
    P.infinityInterface.Object → P.infinityInterface.Object
  shiftUp :
    P.infinityInterface.Object → P.infinityInterface.Object

namespace AnalyticTStructureCandidate

/-- Membership in the candidate nonpositive aisle. -/
def inNonpositive {P : StableAnalyticMotivePackage}
    (T : AnalyticTStructureCandidate P)
    (X : P.infinityInterface.Object) : Type :=
  T.nonpositive X

/-- Membership in the candidate nonnegative coaisle. -/
def inNonnegative {P : StableAnalyticMotivePackage}
    (T : AnalyticTStructureCandidate P)
    (X : P.infinityInterface.Object) : Type :=
  T.nonnegative X

end AnalyticTStructureCandidate

end AnalyticMotives
end LFunctions
end Boundary

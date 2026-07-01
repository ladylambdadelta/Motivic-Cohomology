import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Structures.TStructure.Candidate.Owner

/-!
# Truncation calculus for analytic motives

This file owns the truncation calculus for the candidate analytic motivic
`t`-structure.  Orthogonality and full assembly are downstream.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Truncation calculus for the analytic motivic `t`-structure candidate.  The
truncation objects and comparison maps are part of this lane, not external
assumptions.
-/
structure AnalyticTruncationCalculus
    {P : StableAnalyticMotivePackage}
    (T : AnalyticTStructureCandidate P) where
  truncLE : Int → P.infinityInterface.Object → P.infinityInterface.Object
  truncGE : Int → P.infinityInterface.Object → P.infinityInterface.Object
  lowerMap :
    (n : Int) →
      (X : P.infinityInterface.Object) →
        truncLE n X → X
  upperMap :
    (n : Int) →
      (X : P.infinityInterface.Object) →
        X → truncGE n X
  lowerMembership :
    (n : Int) →
      (X : P.infinityInterface.Object) →
        T.nonpositive (truncLE n X)
  upperMembership :
    (n : Int) →
      (X : P.infinityInterface.Object) →
        T.nonnegative (truncGE n X)

namespace AnalyticTruncationCalculus

/-- The lower truncation object at degree `n`. -/
def lower {P : StableAnalyticMotivePackage}
    {T : AnalyticTStructureCandidate P}
    (C : AnalyticTruncationCalculus T)
    (n : Int) (X : P.infinityInterface.Object) :
    P.infinityInterface.Object :=
  C.truncLE n X

/-- The upper truncation object at degree `n`. -/
def upper {P : StableAnalyticMotivePackage}
    {T : AnalyticTStructureCandidate P}
    (C : AnalyticTruncationCalculus T)
    (n : Int) (X : P.infinityInterface.Object) :
    P.infinityInterface.Object :=
  C.truncGE n X

/-- The lower truncation map into the original object. -/
def lowerToObject {P : StableAnalyticMotivePackage}
    {T : AnalyticTStructureCandidate P}
    (C : AnalyticTruncationCalculus T)
    (n : Int) (X : P.infinityInterface.Object) :
    C.lower n X → X :=
  C.lowerMap n X

/-- The map from the original object to the upper truncation. -/
def objectToUpper {P : StableAnalyticMotivePackage}
    {T : AnalyticTStructureCandidate P}
    (C : AnalyticTruncationCalculus T)
    (n : Int) (X : P.infinityInterface.Object) :
    X → C.upper n X :=
  C.upperMap n X

/-- Lower truncations lie in the candidate nonpositive aisle. -/
theorem lower_membership {P : StableAnalyticMotivePackage}
    {T : AnalyticTStructureCandidate P}
    (C : AnalyticTruncationCalculus T)
    (n : Int) (X : P.infinityInterface.Object) :
    T.nonpositive (C.lower n X) :=
  C.lowerMembership n X

/-- Upper truncations lie in the candidate nonnegative coaisle. -/
theorem upper_membership {P : StableAnalyticMotivePackage}
    {T : AnalyticTStructureCandidate P}
    (C : AnalyticTruncationCalculus T)
    (n : Int) (X : P.infinityInterface.Object) :
    T.nonnegative (C.upper n X) :=
  C.upperMembership n X

end AnalyticTruncationCalculus

end AnalyticMotives
end LFunctions
end Boundary

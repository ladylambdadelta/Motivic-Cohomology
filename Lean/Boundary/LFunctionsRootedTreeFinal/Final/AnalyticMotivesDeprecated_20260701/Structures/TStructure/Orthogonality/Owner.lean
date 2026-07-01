import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Structures.TStructure.TruncationCalculus.Owner

/-!
# Orthogonality for the analytic motivic `t`-structure

This file owns orthogonality between candidate aisles and coaisles after the
truncation calculus has been developed.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Orthogonality data for an analytic truncation calculus.  It owns the morphism
type used for orthogonality in this interface and the vanishing datum between
candidate nonpositive and shifted nonnegative objects.
-/
structure AnalyticTStructureOrthogonality
    {P : StableAnalyticMotivePackage}
    {T : AnalyticTStructureCandidate P}
    (C : AnalyticTruncationCalculus T) where
  Hom : P.infinityInterface.Object → P.infinityInterface.Object → Type
  orthogonal :
    (X Y : P.infinityInterface.Object) →
      T.nonpositive X →
        T.nonnegative Y →
          Hom X (T.shiftDown Y) → Empty

namespace AnalyticTStructureOrthogonality

/-- The morphism type used by analytic `t`-structure orthogonality. -/
def homType {P : StableAnalyticMotivePackage}
    {T : AnalyticTStructureCandidate P}
    {C : AnalyticTruncationCalculus T}
    (O : AnalyticTStructureOrthogonality C)
    (X Y : P.infinityInterface.Object) : Type :=
  O.Hom X Y

/-- Orthogonality eliminates maps from the aisle to shifted coaisle objects. -/
def noMap {P : StableAnalyticMotivePackage}
    {T : AnalyticTStructureCandidate P}
    {C : AnalyticTruncationCalculus T}
    (O : AnalyticTStructureOrthogonality C)
    (X Y : P.infinityInterface.Object)
    (hX : T.nonpositive X)
    (hY : T.nonnegative Y)
    (f : O.Hom X (T.shiftDown Y)) : Empty :=
  O.orthogonal X Y hX hY f

end AnalyticTStructureOrthogonality

end AnalyticMotives
end LFunctions
end Boundary

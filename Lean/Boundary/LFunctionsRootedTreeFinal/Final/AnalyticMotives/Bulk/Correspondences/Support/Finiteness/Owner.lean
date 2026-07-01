import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Support.CycleLike.Owner
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Proper and finite support conditions

This file owns the proper-over-source and finite/admissible-over-target
conditions for analytic correspondence supports.

Foundational sources: mathlib's algebraic-geometry finite and proper morphism
properties provide the algebraic comparison model for support conditions.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Proper-over-source and finite-over-target conditions for a cycle-like analytic
support, imposed on the algebraic-shadow maps induced by the two projections.
-/
structure AnalyticSupportFiniteness {X Y : ContourAdmissibleBulk}
    {P : AnalyticSourceTargetProduct X Y}
    (Z : AnalyticCycleLikeSupport P) where
  properOverSource :
    AlgebraicGeometry.IsProper (AnalyticCycleLikeSupport.mapToSource Z).baseMap
  finiteOverTarget :
    AlgebraicGeometry.IsFinite (AnalyticCycleLikeSupport.mapToTarget Z).baseMap

namespace AnalyticSupportFiniteness

/-- The properness proof for the support map over the source. -/
theorem proper_source {X Y : ContourAdmissibleBulk}
    {P : AnalyticSourceTargetProduct X Y}
    {Z : AnalyticCycleLikeSupport P}
    (F : AnalyticSupportFiniteness Z) :
    AlgebraicGeometry.IsProper (AnalyticCycleLikeSupport.mapToSource Z).baseMap :=
  F.properOverSource

/-- The finiteness proof for the support map over the target. -/
theorem finite_target {X Y : ContourAdmissibleBulk}
    {P : AnalyticSourceTargetProduct X Y}
    {Z : AnalyticCycleLikeSupport P}
    (F : AnalyticSupportFiniteness Z) :
    AlgebraicGeometry.IsFinite (AnalyticCycleLikeSupport.mapToTarget Z).baseMap :=
  F.finiteOverTarget

end AnalyticSupportFiniteness

end AnalyticMotives
end LFunctions
end Boundary

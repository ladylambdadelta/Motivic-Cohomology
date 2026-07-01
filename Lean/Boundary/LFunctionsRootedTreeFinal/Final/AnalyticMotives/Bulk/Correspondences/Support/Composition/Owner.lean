import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Support.Finiteness.Owner

/-!
# Composition of analytic correspondence supports

This file owns composition at the support level.  Contour transport and residue
compatibility are added after support composition has a canonical owner.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Component-level composition data for analytic correspondence supports.  It
records the two input cycle-like supports, the chosen composite support inside
the source-target product, and the finite/proper condition on that composite.

This file sits below `Support.Owner`, so it works with the component support
layers directly and avoids an import cycle with the aggregate support package.
-/
structure AnalyticSupportCompositionData
    (X Y Z : ContourAdmissibleBulk) where
  leftProduct : AnalyticSourceTargetProduct X Y
  rightProduct : AnalyticSourceTargetProduct Y Z
  compositeProduct : AnalyticSourceTargetProduct X Z
  leftSupport : AnalyticCycleLikeSupport leftProduct
  rightSupport : AnalyticCycleLikeSupport rightProduct
  compositeSupport : AnalyticCycleLikeSupport compositeProduct
  compositeFiniteness : AnalyticSupportFiniteness compositeSupport

namespace AnalyticSupportCompositionData

/-- The cycle-like support selected as the composite support. -/
def support {X Y Z : ContourAdmissibleBulk}
    (C : AnalyticSupportCompositionData X Y Z) :
    AnalyticCycleLikeSupport C.compositeProduct :=
  C.compositeSupport

/-- The finite/proper condition on the selected composite support. -/
def finiteness {X Y Z : ContourAdmissibleBulk}
    (C : AnalyticSupportCompositionData X Y Z) :
    AnalyticSupportFiniteness C.compositeSupport :=
  C.compositeFiniteness

end AnalyticSupportCompositionData

end AnalyticMotives
end LFunctions
end Boundary

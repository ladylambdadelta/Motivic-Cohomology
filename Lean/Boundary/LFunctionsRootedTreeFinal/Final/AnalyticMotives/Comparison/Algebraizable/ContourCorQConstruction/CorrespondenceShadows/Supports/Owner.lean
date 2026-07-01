import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.BulkShadows.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Support.Owner

/-!
# Algebraic shadows of correspondence supports

This owner exposes the scheme-level support and projection maps already
carried by finite/proper analytic correspondence supports.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace AnalyticCorrespondenceSupport

/-- The algebraic support scheme of an analytic correspondence support. -/
def algebraicSupport {X Y : ContourAdmissibleBulk}
    (S : AnalyticCorrespondenceSupport X Y) :
    ArithmeticBase :=
  S.supportCore.base

/-- The algebraic product scheme containing the support. -/
def algebraicProduct {X Y : ContourAdmissibleBulk}
    (S : AnalyticCorrespondenceSupport X Y) :
    ArithmeticBase :=
  S.productCore.base

/-- The algebraic map from the support to the source shadow. -/
def algebraicMapToSource {X Y : ContourAdmissibleBulk}
    (S : AnalyticCorrespondenceSupport X Y) :
    S.algebraicSupport ⟶ X.algebraicShadow :=
  (S.mapToSource).baseMap

/-- The algebraic map from the support to the target shadow. -/
def algebraicMapToTarget {X Y : ContourAdmissibleBulk}
    (S : AnalyticCorrespondenceSupport X Y) :
    S.algebraicSupport ⟶ Y.algebraicShadow :=
  (S.mapToTarget).baseMap

/-- The algebraic support map over the source is proper. -/
theorem algebraicMapToSource_proper {X Y : ContourAdmissibleBulk}
    (S : AnalyticCorrespondenceSupport X Y) :
    AlgebraicGeometry.IsProper S.algebraicMapToSource :=
  S.proper_over_source

/-- The algebraic support map over the target is finite. -/
theorem algebraicMapToTarget_finite {X Y : ContourAdmissibleBulk}
    (S : AnalyticCorrespondenceSupport X Y) :
    AlgebraicGeometry.IsFinite S.algebraicMapToTarget :=
  S.finite_over_target

end AnalyticCorrespondenceSupport

end AnalyticMotives
end LFunctions
end Boundary

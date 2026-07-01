import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.CorrespondenceShadows.Supports.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Core.Owner

/-!
# Algebraic shadows of contour correspondences

This owner extracts the finite/proper algebraic correspondence shadow from a
contour-compatible analytic correspondence.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace ContourAnalyticCorrespondence

/-- The algebraic support scheme of a contour-compatible correspondence. -/
def algebraicSupport {X Y : ContourAdmissibleBulk}
    (C : ContourAnalyticCorrespondence X Y) :
    ArithmeticBase :=
  C.support.algebraicSupport

/-- The algebraic map from the correspondence support to the source shadow. -/
def algebraicMapToSource {X Y : ContourAdmissibleBulk}
    (C : ContourAnalyticCorrespondence X Y) :
    C.algebraicSupport ⟶ X.algebraicShadow :=
  C.support.algebraicMapToSource

/-- The algebraic map from the correspondence support to the target shadow. -/
def algebraicMapToTarget {X Y : ContourAdmissibleBulk}
    (C : ContourAnalyticCorrespondence X Y) :
    C.algebraicSupport ⟶ Y.algebraicShadow :=
  C.support.algebraicMapToTarget

/-- The algebraic map to the source shadow is proper. -/
theorem algebraicMapToSource_proper {X Y : ContourAdmissibleBulk}
    (C : ContourAnalyticCorrespondence X Y) :
    AlgebraicGeometry.IsProper C.algebraicMapToSource :=
  C.proper_over_source

/-- The algebraic map to the target shadow is finite. -/
theorem algebraicMapToTarget_finite {X Y : ContourAdmissibleBulk}
    (C : ContourAnalyticCorrespondence X Y) :
    AlgebraicGeometry.IsFinite C.algebraicMapToTarget :=
  C.finite_over_target

end ContourAnalyticCorrespondence

end AnalyticMotives
end LFunctions
end Boundary

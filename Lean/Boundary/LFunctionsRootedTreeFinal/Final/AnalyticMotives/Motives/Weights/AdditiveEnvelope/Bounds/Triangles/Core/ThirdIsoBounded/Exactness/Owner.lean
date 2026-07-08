import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.Core.Exactness.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.Core.ThirdIsoBounded.Owner

/-!
# Exactness of bounded triangles with iso-bounded third representatives

The underlying distinguished triangle of a package with third iso-bounded data
has the usual three zero composites.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The first two morphisms compose to zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded.first_comp_second
    {bound : Nat}
    (package :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded
        bound) :
    package.trianglePackage.triangle.mor₁ ≫
        package.trianglePackage.triangle.mor₂ =
      0 :=
  package.trianglePackage.first_comp_second

/-- The second and third morphisms compose to zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded.second_comp_third
    {bound : Nat}
    (package :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded
        bound) :
    package.trianglePackage.triangle.mor₂ ≫
        package.trianglePackage.triangle.mor₃ =
      0 :=
  package.trianglePackage.second_comp_third

/-- The third morphism followed by the shifted first morphism is zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded.third_comp_shifted_first
    {bound : Nat}
    (package :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded
        bound) :
    package.trianglePackage.triangle.mor₃ ≫
        package.trianglePackage.triangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  package.trianglePackage.third_comp_shifted_first

end AnalyticMotives
end LFunctions
end Boundary

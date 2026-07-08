import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.Core.ThirdIsoBounded.Monotone.Owner

/-!
# Short complexes from bounded triangles with iso-bounded third vertices

The underlying distinguished triangle of such a package canonically determines
the short complex formed by its first two morphisms.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

/-- The short complex carried by the underlying distinguished triangle. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded.shortComplex
    {bound : Nat}
    (package :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded
        bound) :
    ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  shortComplexOfDistTriangle
    package.trianglePackage.triangle
    package.trianglePackage.distinguished

/-- The left vertex of the attached short complex is the first triangle vertex. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded.shortComplex_X₁
    {bound : Nat}
    (package :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded
        bound) :
    package.shortComplex.X₁ =
      package.trianglePackage.triangle.obj₁ :=
  rfl

/-- The middle vertex of the attached short complex is the second triangle vertex. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded.shortComplex_X₂
    {bound : Nat}
    (package :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded
        bound) :
    package.shortComplex.X₂ =
      package.trianglePackage.triangle.obj₂ :=
  rfl

/-- The right vertex of the attached short complex is the third triangle vertex. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded.shortComplex_X₃
    {bound : Nat}
    (package :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded
        bound) :
    package.shortComplex.X₃ =
      package.trianglePackage.triangle.obj₃ :=
  rfl

/-- The first short-complex morphism is the first triangle morphism. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded.shortComplex_f
    {bound : Nat}
    (package :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded
        bound) :
    package.shortComplex.f =
      package.trianglePackage.triangle.mor₁ :=
  rfl

/-- The second short-complex morphism is the second triangle morphism. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded.shortComplex_g
    {bound : Nat}
    (package :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded
        bound) :
    package.shortComplex.g =
      package.trianglePackage.triangle.mor₂ :=
  rfl

/-- The short-complex zero composite is supplied by distinguishedness. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded.shortComplex_zero
    {bound : Nat}
    (package :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded
        bound) :
    package.shortComplex.f ≫ package.shortComplex.g =
      0 :=
  package.shortComplex.zero

/-- Rebounding the weight bound preserves the attached short complex. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded.rebound_shortComplex
    {lower upper : Nat}
    (bound_le : lower ≤ upper)
    (package :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded
        lower) :
    (package.rebound bound_le).shortComplex =
      package.shortComplex :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

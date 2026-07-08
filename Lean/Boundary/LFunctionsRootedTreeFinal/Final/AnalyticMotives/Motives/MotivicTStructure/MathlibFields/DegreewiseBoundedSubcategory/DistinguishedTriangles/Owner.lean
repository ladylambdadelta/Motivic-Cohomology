import Mathlib.CategoryTheory.Triangulated.Functor
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.Shift.Additive.Owner

/-!
# Distinguished triangles in the degreewise bounded stable source

The degreewise bounded stable source uses the same concrete distinguished
triangle predicate as the bounded source: a triangle is distinguished exactly
when its image under inclusion is distinguished in the ambient analytic
comparison source.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- The image of a degreewise-bounded triangle under the inclusion into the
ambient analytic comparison source. -/
def ambientTriangle
    (triangle :
      Triangle TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable) :
    Triangle TraceAnalyticDMgmComparisonSource :=
  Triangle.mk
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .inclusion.map triangle.mor₁)
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .inclusion.map triangle.mor₂)
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .inclusion.map triangle.mor₃)

/-- The explicit ambient triangle agrees with Mathlib's triangle map for the
degreewise bounded inclusion. -/
theorem ambientTriangle_eq_mapTriangle_obj
    (triangle :
      Triangle TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .ambientTriangle triangle =
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .inclusion).mapTriangle.obj triangle :=
  rfl

/-- A degreewise-bounded triangle is distinguished when its image under
inclusion is distinguished in the ambient analytic comparison source. -/
def distinguishedTriangles
    (triangle :
      Triangle TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable) :
    Prop :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .ambientTriangle triangle ∈
    TraceAnalyticDMgmComparisonSource.distinguishedTriangles

/-- Membership in the degreewise bounded distinguished-triangle predicate is
exactly ambient distinguishedness after inclusion. -/
theorem distinguishedTriangles_iff_ambient
    (triangle :
      Triangle TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .distinguishedTriangles triangle ↔
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .ambientTriangle triangle ∈
        TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  Iff.rfl

/-- Ambient distinguishedness after inclusion gives degreewise bounded
distinguishedness. -/
theorem distinguishedTriangles_of_ambient
    (triangle :
      Triangle TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable)
    (ambientDistinguished :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .ambientTriangle triangle ∈
        TraceAnalyticDMgmComparisonSource.distinguishedTriangles) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .distinguishedTriangles triangle :=
  ambientDistinguished

/-- Degreewise bounded distinguished triangles are closed under triangle
isomorphism, because their ambient images are closed under triangle
isomorphism. -/
theorem distinguishedTriangles_isomorphic
    {source target :
      Triangle TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (sourceDistinguished :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .distinguishedTriangles source)
    (triangleIso : target ≅ source) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .distinguishedTriangles target :=
  Pretriangulated.isomorphic_distinguished
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .ambientTriangle source)
    sourceDistinguished
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .ambientTriangle target)
    ((TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .inclusion).mapTriangle.mapIso triangleIso)

/-- Degreewise bounded contractible triangles are distinguished because their
ambient images are the ambient contractible triangles. -/
theorem distinguishedTriangles_contractible
    (object :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .distinguishedTriangles (contractibleTriangle object) :=
  Pretriangulated.contractible_distinguished object.object

/-- The degreewise bounded distinguished-triangle predicate is invariant under
rotation. -/
theorem distinguishedTriangles_rotate
    (triangle :
      Triangle TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .distinguishedTriangles triangle ↔
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .distinguishedTriangles triangle.rotate :=
  Iff.intro
    (fun triangleDistinguished =>
      Pretriangulated.isomorphic_distinguished
        ((TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .ambientTriangle triangle).rotate)
        (Pretriangulated.rot_of_distTriang
          (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
            .ambientTriangle triangle)
          triangleDistinguished)
        (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .ambientTriangle triangle.rotate)
        (((TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .inclusion).mapTriangleRotateIso.app triangle).symm))
    (fun rotatedDistinguished =>
      let rotatedAmbientDistinguished :
          (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
            .ambientTriangle triangle).rotate ∈
            TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
        Pretriangulated.isomorphic_distinguished
          (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
            .ambientTriangle triangle.rotate)
          rotatedDistinguished
          ((TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
            .ambientTriangle triangle).rotate)
          ((TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
            .inclusion).mapTriangleRotateIso.app triangle)
      (Pretriangulated.rotate_distinguished_triangle
        (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .ambientTriangle triangle)).mpr
        rotatedAmbientDistinguished)

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary

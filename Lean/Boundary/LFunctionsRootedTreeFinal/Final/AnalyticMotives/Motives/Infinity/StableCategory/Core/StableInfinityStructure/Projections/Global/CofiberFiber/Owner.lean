import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.StableInfinityStructure.Projections.Global.Owner

/-!
# Cofiber/fiber projections from the actual global stability certificate

This file peels the cofiber/fiber part of the actual stable-infinity
global-stability certificate into individual owner-level projections.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The actual stable-infinity certificate supplies distinguishedness of the
canonical cofiber triangle for each morphism. -/
theorem
    traceAnalyticStableInfinityCategory_actual_global_cofiberTriangle_distinguished
    {source target : TraceAnalyticStableInfinityCategory.HomotopyCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory_cofiberTriangleFor morphism ∈
      traceAnalyticStableInfinityCategory.distinguishedTriangles :=
  (traceAnalyticStableInfinityCategory_actual_global_cofiber_fiber_triangles
    morphism).left

/-- The actual stable-infinity certificate supplies distinguishedness of the
canonical fiber triangle for each morphism. -/
theorem
    traceAnalyticStableInfinityCategory_actual_global_fiberTriangle_distinguished
    {source target : TraceAnalyticStableInfinityCategory.HomotopyCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory_fiberTriangleFor morphism ∈
      traceAnalyticStableInfinityCategory.distinguishedTriangles :=
  (traceAnalyticStableInfinityCategory_actual_global_cofiber_fiber_triangles
    morphism).right.left

/-- The actual stable-infinity certificate identifies the canonical fiber
triangle with the inverse rotation of the canonical cofiber triangle. -/
theorem
    traceAnalyticStableInfinityCategory_actual_global_fiberTriangle_eq_invRotate
    {source target : TraceAnalyticStableInfinityCategory.HomotopyCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory_fiberTriangleFor morphism =
      (traceAnalyticStableInfinityCategory_cofiberTriangleFor
        morphism).invRotate :=
  (traceAnalyticStableInfinityCategory_actual_global_cofiber_fiber_triangles
    morphism).right.right

end AnalyticMotives
end LFunctions
end Boundary

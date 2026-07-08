import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.Construction.Owner

/-!
# Package-level contractible triangles

This owner file identifies the contractible-triangle functor in the assembled
analytic stable-infinity package with Mathlib's contractible-triangle functor
and re-exposes distinguishedness of its values.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The package-level contractible-triangle functor is Mathlib's
contractible-triangle functor. -/
theorem traceAnalyticStableInfinityCategory_contractibleTriangleFunctor_eq :
    traceAnalyticStableInfinityCategory.contractibleTriangleFunctor =
      Pretriangulated.contractibleTriangleFunctor
        StableInfinityOwner.PresentedCategory :=
  rfl

/-- The package-level contractible triangle of an analytic stable motive is
distinguished. -/
theorem
    traceAnalyticStableInfinityCategory_contractibleTriangleFunctor_obj_mem
    (object : StableInfinityOwner.PresentedCategory) :
    traceAnalyticStableInfinityCategory.contractibleTriangleFunctor.obj
        object ∈
      traceAnalyticStableInfinityCategory.distinguishedTriangles :=
  traceAnalyticStableInfinityCategory
    .contractibleTriangleFunctor_obj_distinguished object

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.Construction.Owner

/-!
# Package-level projections for chosen cofiber short complexes

This owner file exposes the two maps of the package-level chosen cofiber
short complex.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The first map of the package-level chosen cofiber short complex is the
original morphism. -/
theorem traceAnalyticStableInfinityCategory_cofiberShortComplex_f
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory.cofiberShortComplex morphism).f =
      morphism :=
  rfl

/-- The second map of the package-level chosen cofiber short complex is the
chosen cofiber cocone map. -/
theorem traceAnalyticStableInfinityCategory_cofiberShortComplex_g
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory.cofiberShortComplex morphism).g =
      traceAnalyticStableInfinityCategory.cofiberCoconeMap morphism :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

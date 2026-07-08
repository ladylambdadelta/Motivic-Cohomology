import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.Fiber.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.Construction.Owner

/-!
# Package-level projections for fiber short complexes

This owner file exposes the two maps of the package-level chosen fiber short
complex.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The package-level short complex attached to the chosen fiber triangle of
a morphism. -/
def traceAnalyticStableInfinityCategory_fiberShortComplex
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    ShortComplex StableInfinityOwner.PresentedCategory :=
  traceAnalyticStableInfinityCategory.fiberShortComplex morphism

/-- The first map of the package-level chosen fiber short complex is the
chosen fiber map. -/
theorem traceAnalyticStableInfinityCategory_fiberShortComplex_f
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory_fiberShortComplex
      morphism).f =
      traceAnalyticStableInfinityCategory.fiberMap morphism :=
  rfl

/-- The second map of the package-level chosen fiber short complex is the
original morphism. -/
theorem traceAnalyticStableInfinityCategory_fiberShortComplex_g
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory_fiberShortComplex
      morphism).g =
      morphism :=
  rfl

/-- The zero field of the package-level chosen fiber short complex is the
package-level fiber-map zero-composition law. -/
theorem traceAnalyticStableInfinityCategory_fiberShortComplex_zero
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory_fiberShortComplex
      morphism).zero =
      traceAnalyticStableInfinityCategory.fiberMap_comp_morphism
        morphism :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Certificate.Comparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Certificate.Global.Owner

/-!
# Global comparison certificate for analytic stable motives

This file adds the square-functorial comparison package to the global
stable-category certificate surface.  The global proposition-valued stability
certificate remains separate from this concrete morphism-valued construction.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Every commutative square in the concrete analytic stable category carries
the induced comparison certificate on chosen cofibers, rotations, fibers, and
short complexes. -/
def traceAnalyticStableInfinityCategory_global_comparison_certificate
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticStableInfinityCategoryComparisonCertificate
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square :=
  traceAnalyticStableInfinityCategory_comparison_certificate
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

end AnalyticMotives
end LFunctions
end Boundary

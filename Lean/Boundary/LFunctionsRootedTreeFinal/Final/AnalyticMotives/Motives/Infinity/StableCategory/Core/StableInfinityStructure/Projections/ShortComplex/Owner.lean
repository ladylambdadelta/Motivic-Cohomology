import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.StableInfinityStructure.Projections.Owner

/-!
# Short-complex projections from the stable-infinity structure certificate

This file exposes the per-morphism short-complex consequences carried by the
actual analytic stable-infinity structure certificate.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The actual stable-infinity certificate supplies the canonical short-complex
map shape for each morphism. -/
theorem traceAnalyticStableInfinityCategory_actual_shortComplex_shape
    {source target :
      TraceAnalyticStableInfinityCategory.HomotopyCategory}
    (morphism : source ⟶ target)
    (leftProbe :
      TraceAnalyticStableInfinityCategory.HomotopyCategoryᵒᵖ)
    (rightProbe :
      TraceAnalyticStableInfinityCategory.HomotopyCategory) :
    traceAnalyticStableInfinityCategory_global_perMorphism_shortComplex_shape
      morphism :=
  (traceAnalyticStableInfinityCategory_actual_shortComplex_certificate
    morphism
    leftProbe
    rightProbe).left

/-- The actual stable-infinity certificate supplies zero composition for the
canonical short complexes attached to each morphism. -/
theorem traceAnalyticStableInfinityCategory_actual_shortComplex_zeroComposition
    {source target :
      TraceAnalyticStableInfinityCategory.HomotopyCategory}
    (morphism : source ⟶ target)
    (leftProbe :
      TraceAnalyticStableInfinityCategory.HomotopyCategoryᵒᵖ)
    (rightProbe :
      TraceAnalyticStableInfinityCategory.HomotopyCategory) :
    traceAnalyticStableInfinityCategory_global_perMorphism_zeroComposition
      morphism :=
  (traceAnalyticStableInfinityCategory_actual_shortComplex_certificate
    morphism
    leftProbe
    rightProbe).right.left

/-- The actual stable-infinity certificate supplies paired covariant and
contravariant Yoneda exactness for the canonical short complexes attached to
each morphism. -/
theorem traceAnalyticStableInfinityCategory_actual_shortComplex_yoneda_exact
    {source target :
      TraceAnalyticStableInfinityCategory.HomotopyCategory}
    (morphism : source ⟶ target)
    (leftProbe :
      TraceAnalyticStableInfinityCategory.HomotopyCategoryᵒᵖ)
    (rightProbe :
      TraceAnalyticStableInfinityCategory.HomotopyCategory) :
    traceAnalyticStableInfinityCategory_global_perMorphism_yoneda_exact
      morphism
      leftProbe
      rightProbe :=
  (traceAnalyticStableInfinityCategory_actual_shortComplex_certificate
    morphism
    leftProbe
    rightProbe).right.right

end AnalyticMotives
end LFunctions
end Boundary

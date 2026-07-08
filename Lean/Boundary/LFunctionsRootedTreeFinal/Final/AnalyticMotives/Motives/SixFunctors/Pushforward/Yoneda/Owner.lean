import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Yoneda.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pushforward.Owner

/-!
# Yoneda comparison for compact-generator pushforward

This file records that lifted compact-generator pushforward is exactly the
Yoneda realization of the underlying compact-generator trace correspondence.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The compact Yoneda preimage of lifted pushforward is the original morphism. -/
theorem TraceSixFunctorPushforward.compactGeneratorObject_yonedaPreimage
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        (TraceSixFunctorPushforward.compactGeneratorObject morphism) =
      morphism :=
  TraceAnalyticGeometricGenerator.yonedaPreimage_representableObjectMap
    morphism

/-- Lifted pushforward is recovered from its compact Yoneda preimage. -/
theorem TraceSixFunctorPushforward.compactGeneratorObject_eq_of_yonedaPreimage
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source.representableObject ⟶ target.representableObject) :
    TraceSixFunctorPushforward.compactGeneratorObject
        (TraceAnalyticGeometricGenerator.yonedaPreimage morphism) =
      morphism :=
  TraceAnalyticGeometricGenerator.representableObjectMap_yonedaPreimage
    morphism

/-- The compact-generator Yoneda equivalence sends a morphism to lifted pushforward. -/
theorem TraceSixFunctorPushforward.yonedaHomEquiv_apply
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.yonedaHomEquiv
        source
        target
        morphism =
      TraceSixFunctorPushforward.compactGeneratorObject morphism :=
  rfl

/-- The inverse compact-generator Yoneda equivalence is the preimage of lifted pushforward maps. -/
theorem TraceSixFunctorPushforward.yonedaHomEquiv_symm_apply
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source.representableObject ⟶ target.representableObject) :
    (TraceAnalyticGeometricGenerator.yonedaHomEquiv
        source
        target).symm morphism =
      TraceAnalyticGeometricGenerator.yonedaPreimage morphism :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

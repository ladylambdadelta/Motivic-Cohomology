import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pushforward.Yoneda.Owner

/-!
# Motive-root Yoneda wrappers for representable pushforward

This file mirrors the lifted representable pushforward/Yoneda comparison facts
under `TraceAnalyticMotive`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root Yoneda preimage of lifted pushforward wrapper. -/
theorem TraceAnalyticMotive.compactGeneratorPushforwardObject_yonedaPreimage
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        (TraceSixFunctorPushforward.compactGeneratorObject morphism) =
      morphism :=
  TraceSixFunctorPushforward.compactGeneratorObject_yonedaPreimage
    morphism

/-- Motive-root lifted pushforward recovery from Yoneda preimage wrapper. -/
theorem TraceAnalyticMotive.compactGeneratorPushforwardObject_eq_of_yonedaPreimage
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source.representableObject ⟶ target.representableObject) :
    TraceSixFunctorPushforward.compactGeneratorObject
        (TraceAnalyticGeometricGenerator.yonedaPreimage morphism) =
      morphism :=
  TraceSixFunctorPushforward.compactGeneratorObject_eq_of_yonedaPreimage
    morphism

/-- Motive-root Yoneda hom equivalence sends a morphism to lifted pushforward. -/
theorem TraceAnalyticMotive.yonedaHomEquiv_apply_compactGeneratorPushforwardObject
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.yonedaHomEquiv
        source
        target
        morphism =
      TraceSixFunctorPushforward.compactGeneratorObject morphism :=
  TraceSixFunctorPushforward.yonedaHomEquiv_apply
    morphism

/-- Motive-root inverse Yoneda hom equivalence is lifted-pushforward preimage. -/
theorem TraceAnalyticMotive.yonedaHomEquiv_symm_apply_compactGeneratorPushforwardObject
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source.representableObject ⟶ target.representableObject) :
    (TraceAnalyticGeometricGenerator.yonedaHomEquiv
        source
        target).symm morphism =
      TraceAnalyticGeometricGenerator.yonedaPreimage morphism :=
  TraceSixFunctorPushforward.yonedaHomEquiv_symm_apply
    morphism

end AnalyticMotives
end LFunctions
end Boundary

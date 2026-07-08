import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorRepresentable.Pushforward.Yoneda.Owner

/-!
# Top-root Yoneda wrappers for representable pushforward

This file mirrors the motive-root lifted representable pushforward/Yoneda
comparison facts under `AnalyticMotivesRoot`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root Yoneda preimage of lifted pushforward wrapper. -/
theorem AnalyticMotivesRoot.compactGeneratorPushforwardObject_yonedaPreimage
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        (TraceSixFunctorPushforward.compactGeneratorObject morphism) =
      morphism :=
  TraceAnalyticMotive.compactGeneratorPushforwardObject_yonedaPreimage
    morphism

/-- Top-root lifted pushforward recovery from Yoneda preimage wrapper. -/
theorem AnalyticMotivesRoot.compactGeneratorPushforwardObject_eq_of_yonedaPreimage
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source.representableObject ⟶ target.representableObject) :
    TraceSixFunctorPushforward.compactGeneratorObject
        (TraceAnalyticGeometricGenerator.yonedaPreimage morphism) =
      morphism :=
  TraceAnalyticMotive.compactGeneratorPushforwardObject_eq_of_yonedaPreimage
    morphism

/-- Top-root Yoneda hom equivalence sends a morphism to lifted pushforward. -/
theorem AnalyticMotivesRoot.yonedaHomEquiv_apply_compactGeneratorPushforwardObject
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.yonedaHomEquiv
        source
        target
        morphism =
      TraceSixFunctorPushforward.compactGeneratorObject morphism :=
  TraceAnalyticMotive.yonedaHomEquiv_apply_compactGeneratorPushforwardObject
    morphism

/-- Top-root inverse Yoneda hom equivalence is lifted-pushforward preimage. -/
theorem AnalyticMotivesRoot.yonedaHomEquiv_symm_apply_compactGeneratorPushforwardObject
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source.representableObject ⟶ target.representableObject) :
    (TraceAnalyticGeometricGenerator.yonedaHomEquiv
        source
        target).symm morphism =
      TraceAnalyticGeometricGenerator.yonedaPreimage morphism :=
  TraceAnalyticMotive.yonedaHomEquiv_symm_apply_compactGeneratorPushforwardObject
    morphism

end AnalyticMotives
end LFunctions
end Boundary

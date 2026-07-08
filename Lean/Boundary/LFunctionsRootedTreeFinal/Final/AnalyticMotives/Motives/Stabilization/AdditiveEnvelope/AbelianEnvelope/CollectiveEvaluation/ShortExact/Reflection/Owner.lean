import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.CollectiveEvaluation.Exact.Reflection.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.EpiMono.Owner

/-!
# Short exactness reflection along collective probe evaluation

This file reflects short exactness in the analytic abelian envelope from the
collective probe exactness theorem together with componentwise mono and epi
checks on the original presheaf-valued maps.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticAdditiveAbelianEnvelope

/-- Collective probe exactness, componentwise monicity of the first map, and
componentwise epicity of the second map assemble to short exactness of the
original analytic abelian-envelope short complex. -/
theorem shortExact_of_collectiveEvaluation_exact_componentwise_mono_epi
    (shortComplex : ShortComplex TraceAnalyticAdditiveAbelianEnvelope)
    (hexact :
      (shortComplex.map
        TraceAnalyticAdditiveAbelianEnvelope.collectiveEvaluation).Exact)
    (hmono :
      ∀ object : Opposite TraceAnalyticAdditiveCategoryObject,
        Mono (shortComplex.f.app object))
    (hepi :
      ∀ object : Opposite TraceAnalyticAdditiveCategoryObject,
        Epi (shortComplex.g.app object)) :
    TraceAnalyticAdditiveAbelianEnvelope.shortExact shortComplex :=
  TraceAnalyticAdditiveAbelianEnvelope.shortExact_of_exact_mono_epi
    (TraceAnalyticAdditiveAbelianEnvelope.exact_of_collectiveEvaluation_exact
      shortComplex
      hexact)
    (TraceAnalyticAdditiveAbelianEnvelope.mono_of_componentwise_mono
      shortComplex.f
      hmono)
    (TraceAnalyticAdditiveAbelianEnvelope.epi_of_componentwise_epi
      shortComplex.g
      hepi)

end TraceAnalyticAdditiveAbelianEnvelope

end AnalyticMotives
end LFunctions
end Boundary

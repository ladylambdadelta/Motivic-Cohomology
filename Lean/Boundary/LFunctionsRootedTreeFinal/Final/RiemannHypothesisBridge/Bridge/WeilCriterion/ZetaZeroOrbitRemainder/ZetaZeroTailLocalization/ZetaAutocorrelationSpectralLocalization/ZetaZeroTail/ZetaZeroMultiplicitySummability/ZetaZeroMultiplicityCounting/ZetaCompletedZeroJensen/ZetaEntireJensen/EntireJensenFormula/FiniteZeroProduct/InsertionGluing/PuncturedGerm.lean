import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.FiniteZeroProduct.ProductCore.Owner

/-!
# Punctured analytic germ helpers

This file owns the generic punctured-germ identity lemmas used by normalized
factor insertion gluing.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Analytic germs that agree on a punctured neighborhood have the same value
at the puncture.

This is the reusable removable-value endpoint: after the factor-cancellation
argument has produced equality away from the center, continuity of the two
analytic germs identifies their filled-in values. -/
theorem analyticAt_eq_at_of_eventuallyEq_punctured
    {f g : ℂ → ℂ}
    {a : ℂ}
    (hf : AnalyticAt ℂ f a)
    (hg : AnalyticAt ℂ g a)
    (hfg : f =ᶠ[𝓝[≠] a] g) :
    f a = g a := by
  have hf_tendsto_nhds :
      Filter.Tendsto f (𝓝 a) (𝓝 (f a)) :=
    hf.continuousAt.tendsto
  have hg_tendsto_nhds :
      Filter.Tendsto g (𝓝 a) (𝓝 (g a)) :=
    hg.continuousAt.tendsto
  have hf_tendsto_punctured :
      Filter.Tendsto f (𝓝[≠] a) (𝓝 (f a)) :=
    hf_tendsto_nhds.mono_left nhdsWithin_le_nhds
  have hg_tendsto_punctured :
      Filter.Tendsto g (𝓝[≠] a) (𝓝 (g a)) :=
    hg_tendsto_nhds.mono_left nhdsWithin_le_nhds
  have hf_tendsto_g_value :
      Filter.Tendsto f (𝓝[≠] a) (𝓝 (g a)) :=
    Filter.Tendsto.congr' hfg.symm hg_tendsto_punctured
  exact
    tendsto_nhds_unique hf_tendsto_punctured hf_tendsto_g_value

/-- Analytic identity theorem in local punctured-germ form.

If two analytic germs agree frequently in the punctured neighborhood of the
center, then they agree eventually in the punctured neighborhood. -/
theorem analyticAt_eventuallyEq_punctured_of_frequentlyEq_punctured
    {f g : ℂ → ℂ}
    {a : ℂ}
    (hf : AnalyticAt ℂ f a)
    (hg : AnalyticAt ℂ g a)
    (hfg : ∃ᶠ w in 𝓝[≠] a, f w = g w) :
    f =ᶠ[𝓝[≠] a] g := by
  have hfg_nhds :
      ∀ᶠ w in 𝓝 a, f w = g w :=
    (AnalyticAt.frequently_eq_iff_eventually_eq hf hg).1 hfg
  exact hfg_nhds.filter_mono nhdsWithin_le_nhds

end
end LFunctions
end Boundary

import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.Owner

/-!
# Exact structure on the abelian analytic envelope

The exact structure used in the analytic motive lane is the ordinary short
exact structure of the abelian presheaf category
`TraceAnalyticAdditiveCategoryObjectᵒᵖ ⥤ ModuleCat Rat`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticAdditiveAbelianEnvelope

/-- A short complex in the analytic abelian envelope is exact in the standard
abelian-category sense. -/
def exact
    (shortComplex : ShortComplex TraceAnalyticAdditiveAbelianEnvelope) :
    Prop :=
  shortComplex.Exact

/-- A short complex in the analytic abelian envelope is short exact in the
standard abelian-category sense. -/
def shortExact
    (shortComplex : ShortComplex TraceAnalyticAdditiveAbelianEnvelope) :
    Prop :=
  shortComplex.ShortExact

/-- Short exactness includes exactness. -/
theorem shortExact_exact
    {shortComplex : ShortComplex TraceAnalyticAdditiveAbelianEnvelope}
    (hshortExact :
      TraceAnalyticAdditiveAbelianEnvelope.shortExact shortComplex) :
    TraceAnalyticAdditiveAbelianEnvelope.exact shortComplex :=
  hshortExact.exact

/-- Short exactness includes monicity of the first map. -/
theorem shortExact_mono_f
    {shortComplex : ShortComplex TraceAnalyticAdditiveAbelianEnvelope}
    (hshortExact :
      TraceAnalyticAdditiveAbelianEnvelope.shortExact shortComplex) :
    Mono shortComplex.f :=
  hshortExact.mono_f

/-- Short exactness includes epicity of the second map. -/
theorem shortExact_epi_g
    {shortComplex : ShortComplex TraceAnalyticAdditiveAbelianEnvelope}
    (hshortExact :
      TraceAnalyticAdditiveAbelianEnvelope.shortExact shortComplex) :
    Epi shortComplex.g :=
  hshortExact.epi_g

/-- In the analytic abelian envelope, exactness together with monicity of the
first map and epicity of the second map packages as short exactness. -/
theorem shortExact_of_exact_mono_epi
    {shortComplex : ShortComplex TraceAnalyticAdditiveAbelianEnvelope}
    (hexact :
      TraceAnalyticAdditiveAbelianEnvelope.exact shortComplex)
    (hmono : Mono shortComplex.f)
    (hepi : Epi shortComplex.g) :
    TraceAnalyticAdditiveAbelianEnvelope.shortExact shortComplex where
  exact := hexact
  mono_f := hmono
  epi_g := hepi

end TraceAnalyticAdditiveAbelianEnvelope

end AnalyticMotives
end LFunctions
end Boundary

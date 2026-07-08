import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.Complexes.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.Exact.Owner

/-!
# Exact structure on abelian-envelope analytic cochain complexes

Exactness of cochain complexes in the analytic abelian envelope is assembled
degreewise from the abelian envelope.  This is the categorical exactness
surface needed by the truncation and cone constructions.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticAbelianCochainComplex

/-- A short complex of analytic abelian cochain complexes is exact in the
ambient abelian category of cochain complexes. -/
def exact
    (shortComplex : ShortComplex TraceAnalyticAbelianCochainComplex) :
    Prop :=
  shortComplex.Exact

/-- A short complex of analytic abelian cochain complexes is short exact in the
ambient abelian category of cochain complexes. -/
def shortExact
    (shortComplex : ShortComplex TraceAnalyticAbelianCochainComplex) :
    Prop :=
  shortComplex.ShortExact

/-- Degreewise exactness assembles to exactness of analytic abelian cochain
complexes. -/
theorem exact_of_degreewise_exact
    (shortComplex : ShortComplex TraceAnalyticAbelianCochainComplex)
    (hdegree :
      ∀ degree : ℤ,
        (shortComplex.map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).Exact) :
    TraceAnalyticAbelianCochainComplex.exact shortComplex :=
  HomologicalComplex.exact_of_degreewise_exact
    shortComplex
    hdegree

/-- Exactness of analytic abelian cochain complexes is equivalent to degreewise
exactness in the abelian envelope. -/
theorem exact_iff_degreewise_exact
    (shortComplex : ShortComplex TraceAnalyticAbelianCochainComplex) :
    TraceAnalyticAbelianCochainComplex.exact shortComplex ↔
      ∀ degree : ℤ,
        (shortComplex.map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).Exact :=
  HomologicalComplex.exact_iff_degreewise_exact
    shortComplex

/-- Degreewise short exactness assembles to short exactness of analytic abelian
cochain complexes. -/
theorem shortExact_of_degreewise_shortExact
    (shortComplex : ShortComplex TraceAnalyticAbelianCochainComplex)
    (hdegree :
      ∀ degree : ℤ,
        (shortComplex.map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).ShortExact) :
    TraceAnalyticAbelianCochainComplex.shortExact shortComplex :=
  HomologicalComplex.shortExact_of_degreewise_shortExact
    shortComplex
    hdegree

/-- Short exactness of analytic abelian cochain complexes is equivalent to
degreewise short exactness in the abelian envelope. -/
theorem shortExact_iff_degreewise_shortExact
    (shortComplex : ShortComplex TraceAnalyticAbelianCochainComplex) :
    TraceAnalyticAbelianCochainComplex.shortExact shortComplex ↔
      ∀ degree : ℤ,
        (shortComplex.map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).ShortExact :=
  HomologicalComplex.shortExact_iff_degreewise_shortExact
    shortComplex

/-- Short exactness includes exactness for analytic abelian cochain complexes. -/
theorem shortExact_exact
    {shortComplex : ShortComplex TraceAnalyticAbelianCochainComplex}
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact shortComplex) :
    TraceAnalyticAbelianCochainComplex.exact shortComplex :=
  hshortExact.exact

/-- In cochain complexes over the analytic abelian envelope, exactness together
with monicity of the first map and epicity of the second map packages as short
exactness. -/
theorem shortExact_of_exact_mono_epi
    {shortComplex : ShortComplex TraceAnalyticAbelianCochainComplex}
    (hexact :
      TraceAnalyticAbelianCochainComplex.exact shortComplex)
    (hmono : Mono shortComplex.f)
    (hepi : Epi shortComplex.g) :
    TraceAnalyticAbelianCochainComplex.shortExact shortComplex where
  exact := hexact
  mono_f := hmono
  epi_g := hepi

/-- Degreewise exactness, monicity, and epicity assemble to short exactness for
cochain complexes over the analytic abelian envelope. -/
theorem shortExact_of_degreewise_exact_mono_epi
    (shortComplex : ShortComplex TraceAnalyticAbelianCochainComplex)
    (hexact :
      ∀ degree : ℤ,
        (shortComplex.map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).Exact)
    (hmono :
      ∀ degree : ℤ,
        Mono
          ((shortComplex.map
            (HomologicalComplex.eval
              TraceAnalyticAdditiveAbelianEnvelope
              (ComplexShape.up ℤ)
              degree)).f))
    (hepi :
      ∀ degree : ℤ,
        Epi
          ((shortComplex.map
            (HomologicalComplex.eval
              TraceAnalyticAdditiveAbelianEnvelope
              (ComplexShape.up ℤ)
              degree)).g)) :
    TraceAnalyticAbelianCochainComplex.shortExact shortComplex :=
  TraceAnalyticAbelianCochainComplex.shortExact_of_degreewise_shortExact
    shortComplex
    (fun degree =>
      TraceAnalyticAdditiveAbelianEnvelope.shortExact_of_exact_mono_epi
        (hexact degree)
        (hmono degree)
        (hepi degree))

end TraceAnalyticAbelianCochainComplex

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.Complexes.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.EpiMono.Owner

/-!
# Degreewise mono and epi criteria for abelian-envelope cochain complexes

Monomorphisms and epimorphisms of cochain maps in the analytic abelian envelope
are assembled degreewise.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticAbelianCochainComplex

/-- A cochain map in the analytic abelian envelope is monic if each degree
component is monic. -/
theorem mono_of_degreewise_mono
    {source target : TraceAnalyticAbelianCochainComplex}
    (hom : source ⟶ target)
    (hdegree : ∀ degree : ℤ, Mono (hom.f degree)) :
    Mono hom :=
  HomologicalComplex.mono_of_mono_f
    hom
    hdegree

/-- A cochain map in the analytic abelian envelope is epic if each degree
component is epic. -/
theorem epi_of_degreewise_epi
    {source target : TraceAnalyticAbelianCochainComplex}
    (hom : source ⟶ target)
    (hdegree : ∀ degree : ℤ, Epi (hom.f degree)) :
    Epi hom :=
  HomologicalComplex.epi_of_epi_f
    hom
    hdegree

end TraceAnalyticAbelianCochainComplex

end AnalyticMotives
end LFunctions
end Boundary

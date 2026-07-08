import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.Owner

/-!
# Componentwise mono and epi criteria in the analytic abelian envelope

The analytic abelian envelope is a presheaf category, so monomorphisms and
epimorphisms of its morphisms are detected componentwise.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticAdditiveAbelianEnvelope

/-- A morphism in the analytic abelian envelope is monic if each presheaf
component is monic. -/
theorem mono_of_componentwise_mono
    {source target : TraceAnalyticAdditiveAbelianEnvelope}
    (hom : source ⟶ target)
    (hcomponent :
      ∀ object : Opposite TraceAnalyticAdditiveCategoryObject,
        Mono (hom.app object)) :
    Mono hom :=
  letI : ∀ object : Opposite TraceAnalyticAdditiveCategoryObject,
      Mono (hom.app object) :=
    hcomponent
  NatTrans.mono_of_mono_app hom

/-- A morphism in the analytic abelian envelope is epic if each presheaf
component is epic. -/
theorem epi_of_componentwise_epi
    {source target : TraceAnalyticAdditiveAbelianEnvelope}
    (hom : source ⟶ target)
    (hcomponent :
      ∀ object : Opposite TraceAnalyticAdditiveCategoryObject,
        Epi (hom.app object)) :
    Epi hom :=
  letI : ∀ object : Opposite TraceAnalyticAdditiveCategoryObject,
      Epi (hom.app object) :=
    hcomponent
  NatTrans.epi_of_epi_app hom

end TraceAnalyticAdditiveAbelianEnvelope

end AnalyticMotives
end LFunctions
end Boundary

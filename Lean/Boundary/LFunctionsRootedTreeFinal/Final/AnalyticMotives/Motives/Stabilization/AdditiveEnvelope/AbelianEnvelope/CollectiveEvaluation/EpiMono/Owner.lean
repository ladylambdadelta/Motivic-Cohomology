import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.CollectiveEvaluation.Projection.Owner

/-!
# Componentwise mono and epi criteria in the collective target

This file proves that monomorphisms and epimorphisms in the product category
of probe values are assembled componentwise.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticAdditiveAbelianEnvelope

/-- A morphism in the collective probe-evaluation target is monic if every
probe coordinate is monic. -/
theorem collectiveTarget_mono_of_componentwise_mono
    {source target :
      TraceAnalyticAdditiveAbelianEnvelope.CollectiveEvaluationTarget}
    (hom : source ⟶ target)
    (hcomponent :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        Mono (hom.app (Discrete.mk probe))) :
    Mono hom :=
  letI : ∀ object : Discrete TraceAnalyticAdditiveCategoryObject,
      Mono (hom.app object) :=
    fun object => hcomponent object.as
  NatTrans.mono_of_mono_app
    hom

/-- A morphism in the collective probe-evaluation target is epic if every
probe coordinate is epic. -/
theorem collectiveTarget_epi_of_componentwise_epi
    {source target :
      TraceAnalyticAdditiveAbelianEnvelope.CollectiveEvaluationTarget}
    (hom : source ⟶ target)
    (hcomponent :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        Epi (hom.app (Discrete.mk probe))) :
    Epi hom :=
  letI : ∀ object : Discrete TraceAnalyticAdditiveCategoryObject,
      Epi (hom.app object) :=
    fun object => hcomponent object.as
  NatTrans.epi_of_epi_app
    hom

end TraceAnalyticAdditiveAbelianEnvelope

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.Owner

/-!
# Collective probe evaluation for the analytic abelian envelope

This file packages all probe evaluations of an abelian-envelope presheaf into a
single faithful functor to the product of Q-module categories.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticAdditiveAbelianEnvelope

/-- The product category of all analytic additive probe values. -/
abbrev CollectiveEvaluationTarget :=
  Discrete TraceAnalyticAdditiveCategoryObject ⥤ ModuleCat Rat

/-- Collective probe evaluation sends a presheaf to the family of its values at
all analytic additive probes. -/
def collectiveEvaluation :
    TraceAnalyticAdditiveAbelianEnvelope ⥤
      TraceAnalyticAdditiveAbelianEnvelope.CollectiveEvaluationTarget where
  obj presheaf :=
    Discrete.functor
      (fun probe : TraceAnalyticAdditiveCategoryObject =>
        presheaf.obj (Opposite.op probe))
  map hom :=
    Discrete.natTrans
      (fun probe : Discrete TraceAnalyticAdditiveCategoryObject =>
        hom.app (Opposite.op probe.as))

/-- Collective probe evaluation preserves zero morphisms, pointwise. -/
instance collectiveEvaluationPreservesZeroMorphisms :
    TraceAnalyticAdditiveAbelianEnvelope
      .collectiveEvaluation.PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- Object projection for collective probe evaluation. -/
theorem collectiveEvaluation_obj
    (presheaf : TraceAnalyticAdditiveAbelianEnvelope)
    (probe : TraceAnalyticAdditiveCategoryObject) :
    (TraceAnalyticAdditiveAbelianEnvelope.collectiveEvaluation.obj
      presheaf).obj (Discrete.mk probe) =
      presheaf.obj (Opposite.op probe) :=
  rfl

/-- Morphism projection for collective probe evaluation. -/
theorem collectiveEvaluation_map
    {source target : TraceAnalyticAdditiveAbelianEnvelope}
    (hom : source ⟶ target)
    (probe : TraceAnalyticAdditiveCategoryObject) :
    (TraceAnalyticAdditiveAbelianEnvelope.collectiveEvaluation.map hom).app
      (Discrete.mk probe) =
      hom.app (Opposite.op probe) :=
  rfl

/-- Collective probe evaluation is faithful: a morphism of presheaves is
determined by all of its probe components. -/
def collectiveEvaluationFaithful :
    TraceAnalyticAdditiveAbelianEnvelope.collectiveEvaluation.Faithful where
  map_injective {X Y} {left right} equality :=
    NatTrans.ext
      (funext
        (fun object =>
          match object with
          | Opposite.op probe =>
              congrFun
                (congrArg NatTrans.app equality)
                (Discrete.mk probe)))

end TraceAnalyticAdditiveAbelianEnvelope

end AnalyticMotives
end LFunctions
end Boundary

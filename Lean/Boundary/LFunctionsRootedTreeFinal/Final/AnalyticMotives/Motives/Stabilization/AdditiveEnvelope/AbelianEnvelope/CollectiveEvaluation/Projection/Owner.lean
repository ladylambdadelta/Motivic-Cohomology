import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.CollectiveEvaluation.Owner

/-!
# Projections from collective probe evaluation

This file exposes the coordinate projection functors from the collective
probe-evaluation target and identifies ordinary probe evaluation as collective
evaluation followed by projection.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticAdditiveAbelianEnvelope

/-- Projection from the collective evaluation target to one analytic additive
probe value. -/
def collectiveEvaluationProjection
    (probe : TraceAnalyticAdditiveCategoryObject) :
    TraceAnalyticAdditiveAbelianEnvelope.CollectiveEvaluationTarget ⥤
      ModuleCat Rat :=
  (CategoryTheory.evaluation
    (Discrete TraceAnalyticAdditiveCategoryObject)
    (ModuleCat Rat)).obj
      (Discrete.mk probe)

/-- Coordinate projection from the collective target preserves zero morphisms,
pointwise. -/
instance collectiveEvaluationProjectionPreservesZeroMorphisms
    (probe : TraceAnalyticAdditiveCategoryObject) :
    (TraceAnalyticAdditiveAbelianEnvelope.collectiveEvaluationProjection
      probe).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- Object projection for one coordinate of the collective target. -/
theorem collectiveEvaluationProjection_obj
    (probe : TraceAnalyticAdditiveCategoryObject)
    (values :
      TraceAnalyticAdditiveAbelianEnvelope.CollectiveEvaluationTarget) :
    (TraceAnalyticAdditiveAbelianEnvelope.collectiveEvaluationProjection
      probe).obj values =
      values.obj (Discrete.mk probe) :=
  rfl

/-- Map projection for one coordinate of the collective target. -/
theorem collectiveEvaluationProjection_map
    (probe : TraceAnalyticAdditiveCategoryObject)
    {source target :
      TraceAnalyticAdditiveAbelianEnvelope.CollectiveEvaluationTarget}
    (hom : source ⟶ target) :
    (TraceAnalyticAdditiveAbelianEnvelope.collectiveEvaluationProjection
      probe).map hom =
      hom.app (Discrete.mk probe) :=
  rfl

/-- Ordinary probe evaluation is collective probe evaluation followed by the
corresponding projection. -/
theorem collectiveEvaluation_comp_projection_eq_evaluation
    (probe : TraceAnalyticAdditiveCategoryObject) :
    TraceAnalyticAdditiveAbelianEnvelope.collectiveEvaluation ⋙
        TraceAnalyticAdditiveAbelianEnvelope.collectiveEvaluationProjection
          probe =
      TraceAnalyticAdditiveAbelianEnvelope.evaluation probe :=
  rfl

end TraceAnalyticAdditiveAbelianEnvelope

end AnalyticMotives
end LFunctions
end Boundary

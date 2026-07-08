import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.CollectiveEvaluation.Exact.Projection.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.CollectiveEvaluation.Exact.Reflection.Owner

/-!
# Coordinate assembly for exactness in the collective target

This file assembles exactness in the collective probe-evaluation target from
exactness after every coordinate projection.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticAdditiveAbelianEnvelope

/-- If every coordinate projection of a short complex in the collective
probe-evaluation target is exact, then the collective short complex itself is
exact. -/
theorem collectiveTarget_exact_of_projection_exact
    (shortComplex :
      ShortComplex
        TraceAnalyticAdditiveAbelianEnvelope.CollectiveEvaluationTarget)
    (hprojection :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        (shortComplex.map
          (TraceAnalyticAdditiveAbelianEnvelope.collectiveEvaluationProjection
            probe)).Exact) :
    shortComplex.Exact :=
  letI : shortComplex.HasHomology :=
    CategoryTheory.ShortComplex.HasHomology.mk'
      (CategoryTheory.ShortComplex.HomologyData.ofAbelian shortComplex)
  (CategoryTheory.ShortComplex.exact_iff_isZero_homology shortComplex).mpr
    (IsZero.iff_id_eq_zero.mpr
      (NatTrans.ext
        (funext
          (fun probe =>
            IsZero.eq_of_src
              ((CategoryTheory.ShortComplex.exact_iff_isZero_homology
                (shortComplex.map
                  (TraceAnalyticAdditiveAbelianEnvelope
                    .collectiveEvaluationProjection probe.as))).mp
                (hprojection probe.as))
              (𝟙
                (shortComplex.homology.obj probe))
              0))))

/-- If every ordinary probe evaluation of an analytic abelian-envelope short
complex is exact, then the original short complex is exact. -/
theorem exact_of_evaluation_exact
    (shortComplex : ShortComplex TraceAnalyticAdditiveAbelianEnvelope)
    (hevaluation :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        (shortComplex.map
          (TraceAnalyticAdditiveAbelianEnvelope.evaluation probe)).Exact) :
    TraceAnalyticAdditiveAbelianEnvelope.exact shortComplex :=
  TraceAnalyticAdditiveAbelianEnvelope.exact_of_collectiveEvaluation_exact
    shortComplex
    (TraceAnalyticAdditiveAbelianEnvelope
      .collectiveTarget_exact_of_projection_exact
        (shortComplex.map
          TraceAnalyticAdditiveAbelianEnvelope.collectiveEvaluation)
        (fun probe =>
          Eq.subst
            (motive := fun functor =>
              (shortComplex.map functor).Exact)
            (Eq.symm
              (TraceAnalyticAdditiveAbelianEnvelope
                .collectiveEvaluation_comp_projection_eq_evaluation probe))
            (hevaluation probe)))

end TraceAnalyticAdditiveAbelianEnvelope

end AnalyticMotives
end LFunctions
end Boundary

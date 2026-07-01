import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.Balancing.Elementary.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.CorrespondenceAlgebraization.FormalSums.ReindexingImages.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.CorrespondenceAlgebraization.FormalSums.WholeImages.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.CorrespondenceAlgebraization.RawHoms.ReindexingImages.Owner

/-!
# Parent images of elementary balancing generators

This file records the parent rational finite-correspondence equality attached
to each elementary balancing generator.
-/

universe u

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

noncomputable section

variable {G : PerfectAnalyticGround.{u}}

namespace AlgebraizedContourFormalSum

/-- Reindexing generators preserve the parent rational correspondence. -/
theorem reindexing_generator_parentRationalCorrespondence
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {S T : ContourCorQFormalSum X Y}
    (R : ContourCorQFormalSumReindexing S T)
    (A : AlgebraizedContourFormalSum sourceBulk targetBulk S) :
    (A.reindex R).parentRationalCorrespondence =
      A.parentRationalCorrespondence :=
  reindex_parentRationalCorrespondence R A

/-- Zero-term balancing generators preserve the parent rational correspondence. -/
theorem zero_term_generator_parentRationalCorrespondence
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {S : ContourCorQFormalSum X Y}
    (A : AlgebraizedContourFormalSum sourceBulk targetBulk S)
    {f : ContourCorQRawHom X Y}
    (B : AlgebraizedContourPrimeSupport sourceBulk targetBulk f) :
    (AlgebraizedContourFormalSum.add
        A (AlgebraizedContourFormalSum.term 0 B)).parentRationalCorrespondence =
      A.parentRationalCorrespondence :=
  add_zero_term_parentRationalCorrespondence A B

/-- Collection balancing generators preserve the parent rational correspondence. -/
theorem collect_terms_generator_parentRationalCorrespondence
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (q r : Rat) {f : ContourCorQRawHom X Y}
    (A : AlgebraizedContourPrimeSupport sourceBulk targetBulk f) :
    (AlgebraizedContourFormalSum.add
        (AlgebraizedContourFormalSum.term q A)
        (AlgebraizedContourFormalSum.term r A)).parentRationalCorrespondence =
      (AlgebraizedContourFormalSum.term (q + r) A).parentRationalCorrespondence :=
  collect_terms_parentRationalCorrespondence q r A

end AlgebraizedContourFormalSum

namespace ContourCorQRawHomAlgebraizationSystem

/--
Every elementary balancing generator preserves the parent rational finite
correspondence attached by a raw-hom algebraization system.
-/
theorem elementaryBalancedRel_parentRationalCorrespondence
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomAlgebraizationSystem sourceBulk targetBulk)
    {S T : ContourCorQFormalSum X Y}
    (h : ContourCorQFormalSum.ElementaryBalancedRel S T) :
    (H.formalSum S).parentRationalCorrespondence =
      (H.formalSum T).parentRationalCorrespondence :=
  match h with
  | ContourCorQFormalSum.ElementaryBalancedRel.reindexing hR =>
      match hR with
      | Nonempty.intro R =>
          H.reindexing_parentRationalCorrespondence R
  | ContourCorQFormalSum.ElementaryBalancedRel.zero_term S f =>
      Eq.trans
        (congrArg
          AlgebraizedContourFormalSum.parentRationalCorrespondence
          (ContourCorQRawHomAlgebraizationSystem.formalSum_add
            H S (ContourCorQFormalSum.term 0 f)))
        (AlgebraizedContourFormalSum.add_zero_term_parentRationalCorrespondence
          (H.formalSum S) (H.at f))
  | ContourCorQFormalSum.ElementaryBalancedRel.collect_terms q r f =>
      Eq.trans
        (congrArg
          AlgebraizedContourFormalSum.parentRationalCorrespondence
          (ContourCorQRawHomAlgebraizationSystem.formalSum_add
            H (ContourCorQFormalSum.term q f) (ContourCorQFormalSum.term r f)))
        (Eq.trans
          (AlgebraizedContourFormalSum.collect_terms_parentRationalCorrespondence
            q r (H.at f))
          (congrArg
            AlgebraizedContourFormalSum.parentRationalCorrespondence
            (Eq.symm
              (ContourCorQRawHomAlgebraizationSystem.formalSum_term H (q + r) f))))

end ContourCorQRawHomAlgebraizationSystem

end

end AnalyticMotives
end LFunctions
end Boundary

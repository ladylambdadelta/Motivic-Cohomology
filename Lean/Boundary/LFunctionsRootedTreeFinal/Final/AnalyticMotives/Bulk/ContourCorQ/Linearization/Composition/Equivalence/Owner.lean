import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.Composition.Reindexing.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.Equivalence.Owner

/-!
# Reindexing equivalence and formal composition

This owner turns the explicit composition reindexing witnesses into
reindexing-equivalence facts for composed formal sums.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace ContourCorQFormalSum

/-- Reindexing equivalence is preserved by formal composition on the left. -/
theorem reindexingRel_comp_left
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQObject}
    {S T : ContourCorQFormalSum X Y}
    (h : ReindexingRel S T)
    (U : ContourCorQFormalSum Y Z) :
    ReindexingRel
      (ContourCorQFormalSum.comp C S U)
      (ContourCorQFormalSum.comp C T U) :=
  match h with
  | Nonempty.intro R =>
      Nonempty.intro
        (ContourCorQFormalSumReindexing.comp_reindex_left C R U)

/-- Reindexing equivalence is preserved by formal composition on the right. -/
theorem reindexingRel_comp_right
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQObject}
    (S : ContourCorQFormalSum X Y)
    {T U : ContourCorQFormalSum Y Z}
    (h : ReindexingRel T U) :
    ReindexingRel
      (ContourCorQFormalSum.comp C S T)
      (ContourCorQFormalSum.comp C S U) :=
  match h with
  | Nonempty.intro R =>
      Nonempty.intro
        (ContourCorQFormalSumReindexing.comp_reindex_right C S R)

end ContourCorQFormalSum

end AnalyticMotives
end LFunctions
end Boundary

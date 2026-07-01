import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.Equivalence.Owner

/-!
# Elementary balancing moves for rational contour sums

This owner records the elementary identifications needed for the free rational
linear span of raw contour correspondences.  Reindexing alone only changes
finite labels; balancing also removes zero terms and combines equal raw
correspondences by adding their coefficients.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace ContourCorQFormalSum

/-- Elementary balancing moves for formal rational contour sums. -/
inductive ElementaryBalancedRel {X Y : ContourCorQObject} :
    ContourCorQFormalSum X Y → ContourCorQFormalSum X Y → Prop
  | reindexing :
      {S T : ContourCorQFormalSum X Y} →
        ReindexingRel S T →
          ElementaryBalancedRel S T
  | zero_term :
      (S : ContourCorQFormalSum X Y) →
        (f : ContourCorQRawHom X Y) →
          ElementaryBalancedRel
            (ContourCorQFormalSum.add S (ContourCorQFormalSum.term 0 f))
            S
  | collect_terms :
      (q r : Rat) →
        (f : ContourCorQRawHom X Y) →
          ElementaryBalancedRel
            (ContourCorQFormalSum.add
              (ContourCorQFormalSum.term q f)
              (ContourCorQFormalSum.term r f))
            (ContourCorQFormalSum.term (q + r) f)

end ContourCorQFormalSum

end AnalyticMotives
end LFunctions
end Boundary

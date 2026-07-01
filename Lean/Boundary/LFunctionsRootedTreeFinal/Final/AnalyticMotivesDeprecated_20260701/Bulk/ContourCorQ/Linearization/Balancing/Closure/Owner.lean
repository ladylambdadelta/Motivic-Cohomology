import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.Balancing.Elementary.Owner

/-!
# Balancing closure for rational contour sums

This owner closes elementary balancing moves under equivalence, addition, and
coefficient scaling.  The resulting relation is the candidate equality for
the true rational linear span of raw contour correspondences.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace ContourCorQFormalSum

/-- Equivalence and operation closure of elementary balancing moves. -/
inductive BalancedRel {X Y : ContourCorQObject} :
    ContourCorQFormalSum X Y → ContourCorQFormalSum X Y → Prop
  | elementary :
      {S T : ContourCorQFormalSum X Y} →
        ElementaryBalancedRel S T →
          BalancedRel S T
  | refl :
      (S : ContourCorQFormalSum X Y) →
        BalancedRel S S
  | symm :
      {S T : ContourCorQFormalSum X Y} →
        BalancedRel S T →
          BalancedRel T S
  | trans :
      {S T U : ContourCorQFormalSum X Y} →
        BalancedRel S T →
          BalancedRel T U →
            BalancedRel S U
  | add :
      {S₁ S₂ T₁ T₂ : ContourCorQFormalSum X Y} →
        BalancedRel S₁ T₁ →
          BalancedRel S₂ T₂ →
            BalancedRel
              (ContourCorQFormalSum.add S₁ S₂)
              (ContourCorQFormalSum.add T₁ T₂)
  | scale :
      (q : Rat) →
        {S T : ContourCorQFormalSum X Y} →
          BalancedRel S T →
            BalancedRel
              (ContourCorQFormalSum.scale q S)
              (ContourCorQFormalSum.scale q T)

/-- Reindexing is one source of balanced equality. -/
def balancedRel_of_reindexing {X Y : ContourCorQObject}
    {S T : ContourCorQFormalSum X Y}
    (h : ReindexingRel S T) :
    BalancedRel S T :=
  BalancedRel.elementary (ElementaryBalancedRel.reindexing h)

/-- The balanced setoid on formal rational contour sums. -/
def balancedSetoid (X Y : ContourCorQObject) :
    Setoid (ContourCorQFormalSum X Y) where
  r := BalancedRel
  iseqv := {
    refl := BalancedRel.refl
    symm := fun h => BalancedRel.symm h
    trans := fun h₁ h₂ => BalancedRel.trans h₁ h₂
  }

end ContourCorQFormalSum

end AnalyticMotives
end LFunctions
end Boundary

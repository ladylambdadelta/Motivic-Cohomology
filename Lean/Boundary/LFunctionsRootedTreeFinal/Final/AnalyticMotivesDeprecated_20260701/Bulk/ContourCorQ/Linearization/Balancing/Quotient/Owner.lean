import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.Balancing.Closure.Owner

/-!
# Balanced quotient homs for `ContourCor_Q`

This owner defines the quotient hom type using the balancing relation, not only
reindexing.  This is the hom surface intended for the rational linear span of
raw contour correspondences.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace ContourCorQFormalSum

/-- Balanced quotient homs for the rational contour-correspondence category. -/
abbrev BalancedQuotientHom (X Y : ContourCorQObject) : Type :=
  Quotient (balancedSetoid X Y)

/-- The balanced quotient class of a finite formal rational contour sum. -/
def balancedClass {X Y : ContourCorQObject}
    (S : ContourCorQFormalSum X Y) :
    BalancedQuotientHom X Y :=
  Quotient.mk (balancedSetoid X Y) S

/-- Reindexing-equivalent sums have the same balanced quotient class. -/
theorem balancedClass_eq_of_reindexing {X Y : ContourCorQObject}
    {S T : ContourCorQFormalSum X Y}
    (h : ReindexingRel S T) :
    balancedClass S = balancedClass T :=
  Quotient.sound (balancedRel_of_reindexing h)

end ContourCorQFormalSum

end AnalyticMotives
end LFunctions
end Boundary

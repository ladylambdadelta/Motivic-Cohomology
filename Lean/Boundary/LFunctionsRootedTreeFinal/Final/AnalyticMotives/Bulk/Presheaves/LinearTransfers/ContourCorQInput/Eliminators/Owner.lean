import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.LinearTransfers.ContourCorQInput.Homs.Owner

/-!
# Eliminators for the `ContourCor_Q` presheaf input

This owner exposes the quotient eliminator for presheaf-input contour homs.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace ContourCorQPresheafHom

/-- Lift a function on formal sums to presheaf-input contour homs. -/
def lift {X Y : ContourCorQPresheafObject}
    {A : Type}
    (φ : ContourCorQFormalSum X Y → A)
    (hφ :
      (S T : ContourCorQFormalSum X Y) →
        ContourCorQFormalSum.BalancedRel S T →
          φ S = φ T) :
    ContourCorQPresheafHom X Y → A :=
  ContourCorQHom.lift φ hφ

/-- The lift of an explicit balanced representative is its formal-sum value. -/
theorem lift_balancedClass {X Y : ContourCorQPresheafObject}
    {A : Type}
    (φ : ContourCorQFormalSum X Y → A)
    (hφ :
      (S T : ContourCorQFormalSum X Y) →
        ContourCorQFormalSum.BalancedRel S T →
          φ S = φ T)
    (S : ContourCorQFormalSum X Y) :
    lift φ hφ (ContourCorQFormalSum.balancedClass S) = φ S :=
  ContourCorQHom.lift_balancedClass φ hφ S

end ContourCorQPresheafHom

end AnalyticMotives
end LFunctions
end Boundary

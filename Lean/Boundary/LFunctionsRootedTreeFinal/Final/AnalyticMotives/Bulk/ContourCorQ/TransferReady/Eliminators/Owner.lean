import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.TransferReady.Homs.Owner

/-!
# Eliminators for transfer-ready homs

This owner gives controlled quotient eliminators for `ContourCorQHom`.  A
downstream construction may define data on transfer-ready homs by defining it
on formal rational sums and proving compatibility with the balanced relation.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace ContourCorQHom

/-- Lift a function on formal sums to transfer-ready homs. -/
def lift {X Y : ContourCorQObject}
    {A : Type}
    (φ : ContourCorQFormalSum X Y → A)
    (hφ :
      (S T : ContourCorQFormalSum X Y) →
        ContourCorQFormalSum.BalancedRel S T →
          φ S = φ T) :
    ContourCorQHom X Y → A :=
  fun F => Quotient.liftOn F φ hφ

/-- The lift of a representative is its formal-sum value. -/
theorem lift_balancedClass {X Y : ContourCorQObject}
    {A : Type}
    (φ : ContourCorQFormalSum X Y → A)
    (hφ :
      (S T : ContourCorQFormalSum X Y) →
        ContourCorQFormalSum.BalancedRel S T →
          φ S = φ T)
    (S : ContourCorQFormalSum X Y) :
    lift φ hφ (ContourCorQFormalSum.balancedClass S) = φ S :=
  rfl

/-- Balanced related formal sums have equal transfer-ready classes. -/
theorem class_eq_of_balancedRel {X Y : ContourCorQObject}
    {S T : ContourCorQFormalSum X Y}
    (h : ContourCorQFormalSum.BalancedRel S T) :
    ContourCorQFormalSum.balancedClass S =
      ContourCorQFormalSum.balancedClass T :=
  Quotient.sound h

end ContourCorQHom

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.Composition.Reindexing.Owner

/-!
# Identity reindexing laws for formal composition

This owner records the formal-sum identity laws for composition as explicit
finite-index reindexings.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace ContourCorQFormalSumReindexing

/-- The formal one-term identity sum is a left identity for formal composition. -/
def comp_identity_left
    (C : ContourCorrespondenceCalculus)
    {X Y : ContourCorQObject}
    (S : ContourCorQFormalSum X Y) :
    ContourCorQFormalSumReindexing
      (ContourCorQFormalSum.comp C
        (ContourCorQFormalSum.single (C.identityAt X))
        S)
      S where
  indexEquiv := {
    toFun := fun p => p.2
    invFun := fun i => (PUnit.unit, i)
    left_inv := fun p =>
      Prod.ext
        (PUnit.ext p.1 PUnit.unit)
        rfl
    right_inv := fun _ => rfl
  }
  coefficient_eq := fun p =>
    one_mul (S.coefficient p.2)
  correspondence_eq := fun p =>
    C.left_identity_eq (S.correspondence p.2)

/-- The formal one-term identity sum is a right identity for formal composition. -/
def comp_identity_right
    (C : ContourCorrespondenceCalculus)
    {X Y : ContourCorQObject}
    (S : ContourCorQFormalSum X Y) :
    ContourCorQFormalSumReindexing
      (ContourCorQFormalSum.comp C
        S
        (ContourCorQFormalSum.single (C.identityAt Y)))
      S where
  indexEquiv := {
    toFun := fun p => p.1
    invFun := fun i => (i, PUnit.unit)
    left_inv := fun p =>
      Prod.ext
        rfl
        (PUnit.ext p.2 PUnit.unit)
    right_inv := fun _ => rfl
  }
  coefficient_eq := fun p =>
    mul_one (S.coefficient p.1)
  correspondence_eq := fun p =>
    C.right_identity_eq (S.correspondence p.1)

end ContourCorQFormalSumReindexing

end AnalyticMotives
end LFunctions
end Boundary

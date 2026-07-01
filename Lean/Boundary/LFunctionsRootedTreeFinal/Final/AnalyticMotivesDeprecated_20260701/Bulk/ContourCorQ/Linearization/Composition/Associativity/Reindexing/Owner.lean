import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.Composition.Reindexing.Owner

/-!
# Associativity reindexing law for formal composition

This owner records associativity of formal composition as an explicit
finite-index reindexing.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace ContourCorQFormalSumReindexing

/-- Formal composition is associative up to explicit finite-index reindexing. -/
def comp_assoc
    (C : ContourCorrespondenceCalculus)
    {W X Y Z : ContourCorQObject}
    (S : ContourCorQFormalSum W X)
    (T : ContourCorQFormalSum X Y)
    (U : ContourCorQFormalSum Y Z) :
    ContourCorQFormalSumReindexing
      (ContourCorQFormalSum.comp C (ContourCorQFormalSum.comp C S T) U)
      (ContourCorQFormalSum.comp C S (ContourCorQFormalSum.comp C T U)) where
  indexEquiv := {
    toFun := fun p => (p.1.1, (p.1.2, p.2))
    invFun := fun p => ((p.1, p.2.1), p.2.2)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
  }
  coefficient_eq := fun p =>
    mul_assoc
      (S.coefficient p.1.1)
      (T.coefficient p.1.2)
      (U.coefficient p.2)
  correspondence_eq := fun p =>
    C.associativity_eq
      (S.correspondence p.1.1)
      (T.correspondence p.1.2)
      (U.correspondence p.2)

end ContourCorQFormalSumReindexing

end AnalyticMotives
end LFunctions
end Boundary

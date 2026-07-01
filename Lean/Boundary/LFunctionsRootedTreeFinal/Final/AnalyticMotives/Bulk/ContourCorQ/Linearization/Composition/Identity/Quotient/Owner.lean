import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.Composition.Identity.Reindexing.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.Composition.Quotient.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.QuotientOperations.Owner

/-!
# Identity laws for quotient composition

This owner descends the formal identity reindexing laws to quotient homs modulo
finite reindexing.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace ContourCorQFormalSum

/-- The quotient identity hom selected by a contour-correspondence calculus. -/
def identityClass
    (C : ContourCorrespondenceCalculus)
    (X : ContourCorQObject) :
    QuotientHom X X :=
  singleClass (C.identityAt X)

/-- Quotient identity reduces to the one-term identity representative. -/
theorem identityClass_eq_singleClass
    (C : ContourCorrespondenceCalculus)
    (X : ContourCorQObject) :
    identityClass C X = singleClass (C.identityAt X) :=
  rfl

/-- The quotient identity is a left identity for quotient composition. -/
theorem compClass_identity_left
    (C : ContourCorrespondenceCalculus)
    {X Y : ContourCorQObject}
    (A : QuotientHom X Y) :
    compClass C (identityClass C X) A = A :=
  Quotient.inductionOn A
    (fun S =>
      Eq.trans
        (compClass_quotientClass
          C
          (ContourCorQFormalSum.single (C.identityAt X))
          S)
        (Quotient.sound
          (Nonempty.intro
            (ContourCorQFormalSumReindexing.comp_identity_left C S))))

/-- The quotient identity is a right identity for quotient composition. -/
theorem compClass_identity_right
    (C : ContourCorrespondenceCalculus)
    {X Y : ContourCorQObject}
    (A : QuotientHom X Y) :
    compClass C A (identityClass C Y) = A :=
  Quotient.inductionOn A
    (fun S =>
      Eq.trans
        (compClass_quotientClass
          C
          S
          (ContourCorQFormalSum.single (C.identityAt Y)))
        (Quotient.sound
          (Nonempty.intro
            (ContourCorQFormalSumReindexing.comp_identity_right C S))))

end ContourCorQFormalSum

end AnalyticMotives
end LFunctions
end Boundary

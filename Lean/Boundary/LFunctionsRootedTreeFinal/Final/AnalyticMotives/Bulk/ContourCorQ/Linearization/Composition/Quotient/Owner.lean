import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.Composition.Equivalence.Owner

/-!
# Composition on reindexing quotient homs

This owner descends formal composition through reindexing equivalence.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace ContourCorQFormalSum

/-- Composition on quotient homs modulo finite reindexing. -/
def compClass
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQObject}
    (A : QuotientHom X Y)
    (B : QuotientHom Y Z) :
    QuotientHom X Z :=
  Quotient.liftOn A
    (fun S =>
      Quotient.liftOn B
        (fun T => quotientClass (ContourCorQFormalSum.comp C S T))
        (fun T U hTU =>
          Quotient.sound
            (reindexingRel_comp_right C S hTU)))
    (fun S T hST =>
      Quotient.inductionOn B
        (fun U =>
          Quotient.sound
            (reindexingRel_comp_left C hST U)))

/-- Quotient composition reduces to formal composition on representatives. -/
theorem compClass_quotientClass
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQObject}
    (S : ContourCorQFormalSum X Y)
    (T : ContourCorQFormalSum Y Z) :
    compClass C (quotientClass S) (quotientClass T) =
      quotientClass (ContourCorQFormalSum.comp C S T) :=
  rfl

end ContourCorQFormalSum

end AnalyticMotives
end LFunctions
end Boundary

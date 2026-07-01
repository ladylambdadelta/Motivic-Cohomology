import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.QuotientOperations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.Balancing.Operations.Owner

/-!
# Projection from reindexing quotient homs to balanced homs

This owner records the canonical map from formal sums modulo finite reindexing
to the balanced rational linear-span quotient.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace ContourCorQFormalSum

/-- The canonical projection from the reindexing quotient to the balanced quotient. -/
def balancedProjection {X Y : ContourCorQObject}
    (A : QuotientHom X Y) :
    BalancedQuotientHom X Y :=
  Quotient.liftOn A
    (fun S => balancedClass S)
    (fun S T h =>
      Quotient.sound (balancedRel_of_reindexing h))

/-- The balanced projection reduces to the balanced class on representatives. -/
theorem balancedProjection_quotientClass {X Y : ContourCorQObject}
    (S : ContourCorQFormalSum X Y) :
    balancedProjection (quotientClass S) = balancedClass S :=
  rfl

/-- The balanced projection sends zero to zero. -/
theorem balancedProjection_zeroClass
    (X Y : ContourCorQObject) :
    balancedProjection (zeroClass X Y) = balancedZeroClass X Y :=
  rfl

/-- The balanced projection sends single terms to single terms. -/
theorem balancedProjection_singleClass {X Y : ContourCorQObject}
    (f : ContourCorQRawHom X Y) :
    balancedProjection (singleClass f) = balancedSingleClass f :=
  rfl

/-- The balanced projection preserves addition. -/
theorem balancedProjection_addClass {X Y : ContourCorQObject}
    (A B : QuotientHom X Y) :
    balancedProjection (addClass A B) =
      balancedAddClass (balancedProjection A) (balancedProjection B) :=
  Quotient.inductionOn A
    (fun S =>
      Quotient.inductionOn B
        (fun T =>
          Eq.trans
            (congrArg
              balancedProjection
              (addClass_quotientClass S T))
            (Eq.symm
              (balancedAddClass_balancedClass S T))))

/-- The balanced projection preserves scalar multiplication. -/
theorem balancedProjection_scaleClass {X Y : ContourCorQObject}
    (q : Rat)
    (A : QuotientHom X Y) :
    balancedProjection (scaleClass q A) =
      balancedScaleClass q (balancedProjection A) :=
  Quotient.inductionOn A
    (fun S =>
      Eq.trans
        (congrArg
          balancedProjection
          (scaleClass_quotientClass q S))
        (Eq.symm
          (balancedScaleClass_balancedClass q S)))

/-- The balanced projection preserves negation. -/
theorem balancedProjection_negClass {X Y : ContourCorQObject}
    (A : QuotientHom X Y) :
    balancedProjection (negClass A) =
      balancedNegClass (balancedProjection A) :=
  balancedProjection_scaleClass (-1) A

/-- The balanced projection preserves subtraction. -/
theorem balancedProjection_subClass {X Y : ContourCorQObject}
    (A B : QuotientHom X Y) :
    balancedProjection (subClass A B) =
      balancedSubClass (balancedProjection A) (balancedProjection B) :=
  Eq.trans
    (balancedProjection_addClass A (negClass B))
    (congrArg
      (fun R =>
        balancedAddClass (balancedProjection A) R)
      (balancedProjection_negClass B))

end ContourCorQFormalSum

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.TransferReady.Homs.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.Balancing.ReindexingQuotient.Owner

/-!
# Reindexing quotient projection to transfer-ready homs

This owner exposes the canonical projection from reindexing quotient homs to
the public transfer-ready hom surface.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace ContourCorQHom

/-- Project a reindexing quotient hom to the transfer-ready balanced hom. -/
def ofReindexingQuotient {X Y : ContourCorQObject}
    (A : ContourCorQFormalSum.QuotientHom X Y) :
    ContourCorQHom X Y :=
  ContourCorQFormalSum.balancedProjection A

/-- Projection from the reindexing quotient reduces on representatives. -/
theorem ofReindexingQuotient_quotientClass {X Y : ContourCorQObject}
    (S : ContourCorQFormalSum X Y) :
    ofReindexingQuotient (ContourCorQFormalSum.quotientClass S) =
      ContourCorQFormalSum.balancedClass S :=
  rfl

/-- Projection sends the reindexing zero class to the public zero hom. -/
theorem ofReindexingQuotient_zeroClass
    (X Y : ContourCorQObject) :
    ofReindexingQuotient (ContourCorQFormalSum.zeroClass X Y) =
      ContourCorQHom.zero X Y :=
  rfl

/-- Projection sends reindexing single classes to public single homs. -/
theorem ofReindexingQuotient_singleClass {X Y : ContourCorQObject}
    (f : ContourCorQRawHom X Y) :
    ofReindexingQuotient (ContourCorQFormalSum.singleClass f) =
      ContourCorQHom.single f :=
  rfl

/-- Projection preserves addition into the public transfer-ready operation. -/
theorem ofReindexingQuotient_addClass {X Y : ContourCorQObject}
    (A B : ContourCorQFormalSum.QuotientHom X Y) :
    ofReindexingQuotient (ContourCorQFormalSum.addClass A B) =
      ContourCorQHom.add
        (ofReindexingQuotient A)
        (ofReindexingQuotient B) :=
  ContourCorQFormalSum.balancedProjection_addClass A B

/-- Projection preserves scalar multiplication into the public transfer-ready operation. -/
theorem ofReindexingQuotient_scaleClass {X Y : ContourCorQObject}
    (q : Rat)
    (A : ContourCorQFormalSum.QuotientHom X Y) :
    ofReindexingQuotient (ContourCorQFormalSum.scaleClass q A) =
      ContourCorQHom.scale q (ofReindexingQuotient A) :=
  ContourCorQFormalSum.balancedProjection_scaleClass q A

/-- Projection preserves negation into the public transfer-ready operation. -/
theorem ofReindexingQuotient_negClass {X Y : ContourCorQObject}
    (A : ContourCorQFormalSum.QuotientHom X Y) :
    ofReindexingQuotient (ContourCorQFormalSum.negClass A) =
      ContourCorQHom.neg (ofReindexingQuotient A) :=
  ContourCorQFormalSum.balancedProjection_negClass A

/-- Projection preserves subtraction into the public transfer-ready operation. -/
theorem ofReindexingQuotient_subClass {X Y : ContourCorQObject}
    (A B : ContourCorQFormalSum.QuotientHom X Y) :
    ofReindexingQuotient (ContourCorQFormalSum.subClass A B) =
      ContourCorQHom.sub
        (ofReindexingQuotient A)
        (ofReindexingQuotient B) :=
  ContourCorQFormalSum.balancedProjection_subClass A B

end ContourCorQHom

end AnalyticMotives
end LFunctions
end Boundary

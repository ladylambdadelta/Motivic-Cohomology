import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.TransferReady.Homs.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.CorrespondenceAlgebraization.RawHoms.RationalImages.Balancing.Owner

/-!
# Quotient images for raw-hom rational image systems

This file descends a broad raw-hom rational image system from formal contour
sums to transfer-ready balanced quotient contour homs.
-/

universe u

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

noncomputable section

variable {G : PerfectAnalyticGround.{u}}

namespace ContourCorQRawHomRationalImageSystem

/-- The broad parent rational image induced on balanced quotient homs. -/
def quotientImage
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomRationalImageSystem sourceBulk targetBulk) :
    ContourCorQHom X Y →
      RationalFiniteCorrespondence sourceBulk.scheme targetBulk.scheme :=
  Quotient.lift
    (fun S : ContourCorQFormalSum X Y =>
      H.formalSumImage S)
    (fun S T h =>
      H.balancedRel_formalSumImage h)

/-- The quotient image of a represented formal sum is its formal-sum image. -/
theorem quotientImage_balancedClass
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomRationalImageSystem sourceBulk targetBulk)
    (S : ContourCorQFormalSum X Y) :
    H.quotientImage (ContourCorQFormalSum.balancedClass S) =
      H.formalSumImage S :=
  rfl

/-- The quotient image of the zero contour hom is zero. -/
theorem quotientImage_zero
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomRationalImageSystem sourceBulk targetBulk) :
    H.quotientImage (ContourCorQHom.zero X Y) = 0 :=
  Eq.trans
    (H.quotientImage_balancedClass (ContourCorQFormalSum.zero X Y))
    (H.formalSumImage_zero)

/-- The quotient image of a weighted raw contour hom is its weighted rational image. -/
theorem quotientImage_term
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomRationalImageSystem sourceBulk targetBulk)
    (q : Rat)
    (f : ContourCorQRawHom X Y) :
    H.quotientImage (ContourCorQHom.term q f) =
      q • H.at f :=
  Eq.trans
    (H.quotientImage_balancedClass (ContourCorQFormalSum.term q f))
    (H.formalSumImage_term q f)

/-- The quotient image of a single raw contour hom is its rational image. -/
theorem quotientImage_single
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomRationalImageSystem sourceBulk targetBulk)
    (f : ContourCorQRawHom X Y) :
    H.quotientImage (ContourCorQHom.single f) =
      H.at f :=
  Eq.trans
    (H.quotientImage_term 1 f)
    (one_smul Rat (H.at f))

end ContourCorQRawHomRationalImageSystem

end

end AnalyticMotives
end LFunctions
end Boundary

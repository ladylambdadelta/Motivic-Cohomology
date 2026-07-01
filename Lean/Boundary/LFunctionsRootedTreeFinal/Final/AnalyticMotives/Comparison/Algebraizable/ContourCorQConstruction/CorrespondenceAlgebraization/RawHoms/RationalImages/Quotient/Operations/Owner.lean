import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.CorrespondenceAlgebraization.RawHoms.RationalImages.Quotient.Owner

/-!
# Operation compatibility for broad quotient images

This file proves that the quotient image induced by a raw-hom rational image
system respects addition and scalar multiplication of transfer-ready contour
homs.
-/

universe u

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

noncomputable section

variable {G : PerfectAnalyticGround.{u}}

namespace ContourCorQRawHomRationalImageSystem

/-- The broad quotient image respects addition. -/
theorem quotientImage_add
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomRationalImageSystem sourceBulk targetBulk)
    (F K : ContourCorQHom X Y) :
    H.quotientImage (ContourCorQHom.add F K) =
      H.quotientImage F + H.quotientImage K :=
  Quotient.inductionOn₂ F K
    (fun S T =>
      Eq.trans
        (H.quotientImage_balancedClass (ContourCorQFormalSum.add S T))
        (H.formalSumImage_add S T))

/-- The broad quotient image respects scalar multiplication. -/
theorem quotientImage_scale
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomRationalImageSystem sourceBulk targetBulk)
    (q : Rat)
    (F : ContourCorQHom X Y) :
    H.quotientImage (ContourCorQHom.scale q F) =
      q • H.quotientImage F :=
  Quotient.inductionOn F
    (fun S =>
      Eq.trans
        (H.quotientImage_balancedClass (ContourCorQFormalSum.scale q S))
        (H.formalSumImage_scale q S))

/-- The broad quotient image respects negation. -/
theorem quotientImage_neg
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomRationalImageSystem sourceBulk targetBulk)
    (F : ContourCorQHom X Y) :
    H.quotientImage (ContourCorQHom.neg F) =
      (-1 : Rat) • H.quotientImage F :=
  H.quotientImage_scale (-1) F

/-- The broad quotient image expands subtraction as addition with a negated image. -/
theorem quotientImage_sub
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomRationalImageSystem sourceBulk targetBulk)
    (F K : ContourCorQHom X Y) :
    H.quotientImage (ContourCorQHom.sub F K) =
      H.quotientImage F + (-1 : Rat) • H.quotientImage K :=
  Eq.trans
    (H.quotientImage_add F (ContourCorQHom.neg K))
    (congrArg
      (fun R =>
        H.quotientImage F + R)
      (H.quotientImage_neg K))

end ContourCorQRawHomRationalImageSystem

end

end AnalyticMotives
end LFunctions
end Boundary

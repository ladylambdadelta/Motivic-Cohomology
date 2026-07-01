import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.CorrespondenceAlgebraization.RawHoms.RationalImages.Owner

/-!
# Formal-sum images for raw-hom rational image systems

This file evaluates rational contour formal sums through a raw-hom rational
image system by summing coefficient-weighted parent images.
-/

universe u

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

noncomputable section

variable {G : PerfectAnalyticGround.{u}}

namespace ContourCorQRawHomRationalImageSystem

/-- The parent term image assigned to one summand of a formal contour sum. -/
def formalSumTerm
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomRationalImageSystem sourceBulk targetBulk)
    (S : ContourCorQFormalSum X Y)
    (i : S.Index) :
    RationalFiniteCorrespondence sourceBulk.scheme targetBulk.scheme :=
  S.coeffAt i • H.at (S.correspondenceAt i)

/-- The parent rational image assigned to a whole formal contour sum. -/
def formalSumImage
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomRationalImageSystem sourceBulk targetBulk)
    (S : ContourCorQFormalSum X Y) :
    RationalFiniteCorrespondence sourceBulk.scheme targetBulk.scheme :=
  letI : Finite S.Index := S.finiteIndex
  letI : Fintype S.Index := Fintype.ofFinite S.Index
  Finset.univ.sum (fun i : S.Index => H.formalSumTerm S i)

/-- The image of the empty formal sum is zero. -/
theorem formalSumImage_zero
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomRationalImageSystem sourceBulk targetBulk) :
    H.formalSumImage (ContourCorQFormalSum.zero X Y) = 0 :=
  Finset.sum_empty

/-- The image of a one-term formal sum is the coefficient-weighted raw image. -/
theorem formalSumImage_term
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomRationalImageSystem sourceBulk targetBulk)
    (q : Rat)
    (f : ContourCorQRawHom X Y) :
    H.formalSumImage (ContourCorQFormalSum.term q f) =
      q • H.at f :=
  Fintype.sum_unique
    (fun i : PUnit =>
      H.formalSumTerm (ContourCorQFormalSum.term q f) i)

/-- The image of a sum of formal sums is the sum of their images. -/
theorem formalSumImage_add
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomRationalImageSystem sourceBulk targetBulk)
    (S T : ContourCorQFormalSum X Y) :
    H.formalSumImage (ContourCorQFormalSum.add S T) =
      H.formalSumImage S + H.formalSumImage T :=
  Fintype.sum_sum_type
    (fun i : S.Index ⊕ T.Index =>
      H.formalSumTerm (ContourCorQFormalSum.add S T) i)

end ContourCorQRawHomRationalImageSystem

end

end AnalyticMotives
end LFunctions
end Boundary

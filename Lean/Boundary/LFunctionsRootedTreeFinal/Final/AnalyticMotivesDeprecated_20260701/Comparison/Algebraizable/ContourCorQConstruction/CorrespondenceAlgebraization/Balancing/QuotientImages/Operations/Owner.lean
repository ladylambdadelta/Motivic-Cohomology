import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.CorrespondenceAlgebraization.Balancing.QuotientImages.Owner

/-!
# Operation compatibility for quotient parent images

This file proves that the parent rational finite-correspondence image of
transfer-ready contour homs respects the quotient hom operations.
-/

universe u

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

noncomputable section

variable {G : PerfectAnalyticGround.{u}}

namespace ContourCorQHom

/-- The parent image of the zero contour hom is zero. -/
theorem parentRationalCorrespondence_zero
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomAlgebraizationSystem sourceBulk targetBulk) :
    parentRationalCorrespondence H (ContourCorQHom.zero X Y) =
      0 :=
  Eq.trans
    (parentRationalCorrespondence_balancedClass
      H (ContourCorQFormalSum.zero X Y))
    (AlgebraizedContourFormalSum.zero_parentRationalCorrespondence
      sourceBulk targetBulk)

/-- The parent image of a weighted raw contour hom is its singleton parent correspondence. -/
theorem parentRationalCorrespondence_term
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomAlgebraizationSystem sourceBulk targetBulk)
    (q : Rat)
    (f : ContourCorQRawHom X Y) :
    parentRationalCorrespondence H (ContourCorQHom.term q f) =
      Finsupp.single (H.at f).parentPrimeGeom q :=
  Eq.trans
    (parentRationalCorrespondence_balancedClass
      H (ContourCorQFormalSum.term q f))
    (Eq.trans
      (congrArg
        AlgebraizedContourFormalSum.parentRationalCorrespondence
        (ContourCorQRawHomAlgebraizationSystem.formalSum_term H q f))
      (AlgebraizedContourFormalSum.term_parentRationalCorrespondence q (H.at f)))

/-- The parent image of a single raw contour hom is its coefficient-one singleton. -/
theorem parentRationalCorrespondence_single
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomAlgebraizationSystem sourceBulk targetBulk)
    (f : ContourCorQRawHom X Y) :
    parentRationalCorrespondence H (ContourCorQHom.single f) =
      Finsupp.single (H.at f).parentPrimeGeom 1 :=
  parentRationalCorrespondence_term H 1 f

/-- The parent image of a quotient sum is the sum of the parent images. -/
theorem parentRationalCorrespondence_add
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomAlgebraizationSystem sourceBulk targetBulk)
    (F K : ContourCorQHom X Y) :
    parentRationalCorrespondence H (ContourCorQHom.add F K) =
      parentRationalCorrespondence H F +
        parentRationalCorrespondence H K :=
  Quotient.inductionOn₂ F K
    (fun S T =>
      Eq.trans
        (parentRationalCorrespondence_balancedClass
          H (ContourCorQFormalSum.add S T))
        (Eq.trans
          (congrArg
            AlgebraizedContourFormalSum.parentRationalCorrespondence
            (ContourCorQRawHomAlgebraizationSystem.formalSum_add H S T))
          (AlgebraizedContourFormalSum.add_parentRationalCorrespondence
            (H.formalSum S) (H.formalSum T))))

/-- The parent image of a quotient scalar multiple is the scalar multiple of the parent image. -/
theorem parentRationalCorrespondence_scale
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomAlgebraizationSystem sourceBulk targetBulk)
    (q : Rat)
    (F : ContourCorQHom X Y) :
    parentRationalCorrespondence H (ContourCorQHom.scale q F) =
      q • parentRationalCorrespondence H F :=
  Quotient.inductionOn F
    (fun S =>
      Eq.trans
        (parentRationalCorrespondence_balancedClass
          H (ContourCorQFormalSum.scale q S))
        (Eq.trans
          (congrArg
            AlgebraizedContourFormalSum.parentRationalCorrespondence
            (ContourCorQRawHomAlgebraizationSystem.formalSum_scale H q S))
          (AlgebraizedContourFormalSum.scale_parentRationalCorrespondence
            q (H.formalSum S))))

/-- The parent image of a quotient negation is the negated parent image. -/
theorem parentRationalCorrespondence_neg
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomAlgebraizationSystem sourceBulk targetBulk)
    (F : ContourCorQHom X Y) :
    parentRationalCorrespondence H (ContourCorQHom.neg F) =
      (-1 : Rat) • parentRationalCorrespondence H F :=
  parentRationalCorrespondence_scale H (-1) F

/-- The parent image of a quotient subtraction is addition with the negated parent image. -/
theorem parentRationalCorrespondence_sub
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomAlgebraizationSystem sourceBulk targetBulk)
    (F K : ContourCorQHom X Y) :
    parentRationalCorrespondence H (ContourCorQHom.sub F K) =
      parentRationalCorrespondence H F +
        (-1 : Rat) • parentRationalCorrespondence H K :=
  Eq.trans
    (parentRationalCorrespondence_add H F (ContourCorQHom.neg K))
    (congrArg
      (fun R =>
        parentRationalCorrespondence H F + R)
      (parentRationalCorrespondence_neg H K))

end ContourCorQHom

end

end AnalyticMotives
end LFunctions
end Boundary

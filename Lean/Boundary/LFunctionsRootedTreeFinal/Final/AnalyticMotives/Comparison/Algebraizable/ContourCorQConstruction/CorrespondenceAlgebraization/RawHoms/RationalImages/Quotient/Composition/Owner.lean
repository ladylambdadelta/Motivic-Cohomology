import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.CorrespondenceAlgebraization.RawHoms.RationalImages.Quotient.Operations.Owner

/-!
# Parent composition for broad quotient images

This file records parent-side bilinearity of `SmCorQ` composition after
applying broad rational quotient images to transfer-ready contour homs.
-/

universe u

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

noncomputable section

variable {G : PerfectAnalyticGround.{u}}

namespace ContourCorQRawHomRationalImageSystem

/-- Parent composition with a zero left broad quotient image is zero. -/
theorem parentComp_zero_left
    {X Y Z : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {middleBulk : SmoothAlgebraization G Y}
    {targetBulk : SmoothAlgebraization G Z}
    (category : SmCorQ (k := G.carrier))
    (HXY : ContourCorQRawHomRationalImageSystem sourceBulk middleBulk)
    (HYZ : ContourCorQRawHomRationalImageSystem middleBulk targetBulk)
    (K : ContourCorQHom Y Z) :
    category.comp
        (HXY.quotientImage (ContourCorQHom.zero X Y))
        (HYZ.quotientImage K) =
      0 :=
  Eq.trans
    (congrArg
      (fun R =>
        category.comp R (HYZ.quotientImage K))
      HXY.quotientImage_zero)
    (SmCorQ.zero_comp category (HYZ.quotientImage K))

/-- Parent composition with a zero right broad quotient image is zero. -/
theorem parentComp_zero_right
    {X Y Z : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {middleBulk : SmoothAlgebraization G Y}
    {targetBulk : SmoothAlgebraization G Z}
    (category : SmCorQ (k := G.carrier))
    (HXY : ContourCorQRawHomRationalImageSystem sourceBulk middleBulk)
    (HYZ : ContourCorQRawHomRationalImageSystem middleBulk targetBulk)
    (F : ContourCorQHom X Y) :
    category.comp
        (HXY.quotientImage F)
        (HYZ.quotientImage (ContourCorQHom.zero Y Z)) =
      0 :=
  Eq.trans
    (congrArg
      (fun R =>
        category.comp (HXY.quotientImage F) R)
      HYZ.quotientImage_zero)
    (SmCorQ.comp_zero category (HXY.quotientImage F))

/-- Parent composition is additive in the left broad quotient image. -/
theorem parentComp_add_left
    {X Y Z : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {middleBulk : SmoothAlgebraization G Y}
    {targetBulk : SmoothAlgebraization G Z}
    (category : SmCorQ (k := G.carrier))
    (HXY : ContourCorQRawHomRationalImageSystem sourceBulk middleBulk)
    (HYZ : ContourCorQRawHomRationalImageSystem middleBulk targetBulk)
    (F₁ F₂ : ContourCorQHom X Y)
    (K : ContourCorQHom Y Z) :
    category.comp
        (HXY.quotientImage (ContourCorQHom.add F₁ F₂))
        (HYZ.quotientImage K) =
      category.comp (HXY.quotientImage F₁) (HYZ.quotientImage K) +
        category.comp (HXY.quotientImage F₂) (HYZ.quotientImage K) :=
  Eq.trans
    (congrArg
      (fun R =>
        category.comp R (HYZ.quotientImage K))
      (HXY.quotientImage_add F₁ F₂))
    (SmCorQ.add_comp
      category
      (HXY.quotientImage F₁)
      (HXY.quotientImage F₂)
      (HYZ.quotientImage K))

/-- Parent composition is additive in the right broad quotient image. -/
theorem parentComp_add_right
    {X Y Z : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {middleBulk : SmoothAlgebraization G Y}
    {targetBulk : SmoothAlgebraization G Z}
    (category : SmCorQ (k := G.carrier))
    (HXY : ContourCorQRawHomRationalImageSystem sourceBulk middleBulk)
    (HYZ : ContourCorQRawHomRationalImageSystem middleBulk targetBulk)
    (F : ContourCorQHom X Y)
    (K₁ K₂ : ContourCorQHom Y Z) :
    category.comp
        (HXY.quotientImage F)
        (HYZ.quotientImage (ContourCorQHom.add K₁ K₂)) =
      category.comp (HXY.quotientImage F) (HYZ.quotientImage K₁) +
        category.comp (HXY.quotientImage F) (HYZ.quotientImage K₂) :=
  Eq.trans
    (congrArg
      (fun R =>
        category.comp (HXY.quotientImage F) R)
      (HYZ.quotientImage_add K₁ K₂))
    (SmCorQ.comp_add
      category
      (HXY.quotientImage F)
      (HYZ.quotientImage K₁)
      (HYZ.quotientImage K₂))

/-- Parent composition is compatible with scaling in the left broad quotient image. -/
theorem parentComp_scale_left
    {X Y Z : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {middleBulk : SmoothAlgebraization G Y}
    {targetBulk : SmoothAlgebraization G Z}
    (category : SmCorQ (k := G.carrier))
    (HXY : ContourCorQRawHomRationalImageSystem sourceBulk middleBulk)
    (HYZ : ContourCorQRawHomRationalImageSystem middleBulk targetBulk)
    (q : Rat)
    (F : ContourCorQHom X Y)
    (K : ContourCorQHom Y Z) :
    category.comp
        (HXY.quotientImage (ContourCorQHom.scale q F))
        (HYZ.quotientImage K) =
      q • category.comp (HXY.quotientImage F) (HYZ.quotientImage K) :=
  Eq.trans
    (congrArg
      (fun R =>
        category.comp R (HYZ.quotientImage K))
      (HXY.quotientImage_scale q F))
    (SmCorQ.smul_comp
      category q
      (HXY.quotientImage F)
      (HYZ.quotientImage K))

/-- Parent composition is compatible with scaling in the right broad quotient image. -/
theorem parentComp_scale_right
    {X Y Z : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {middleBulk : SmoothAlgebraization G Y}
    {targetBulk : SmoothAlgebraization G Z}
    (category : SmCorQ (k := G.carrier))
    (HXY : ContourCorQRawHomRationalImageSystem sourceBulk middleBulk)
    (HYZ : ContourCorQRawHomRationalImageSystem middleBulk targetBulk)
    (q : Rat)
    (F : ContourCorQHom X Y)
    (K : ContourCorQHom Y Z) :
    category.comp
        (HXY.quotientImage F)
        (HYZ.quotientImage (ContourCorQHom.scale q K)) =
      q • category.comp (HXY.quotientImage F) (HYZ.quotientImage K) :=
  Eq.trans
    (congrArg
      (fun R =>
        category.comp (HXY.quotientImage F) R)
      (HYZ.quotientImage_scale q K))
    (SmCorQ.comp_smul
      category q
      (HXY.quotientImage F)
      (HYZ.quotientImage K))

/-- Parent composition is compatible with negation in the left broad quotient image. -/
theorem parentComp_neg_left
    {X Y Z : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {middleBulk : SmoothAlgebraization G Y}
    {targetBulk : SmoothAlgebraization G Z}
    (category : SmCorQ (k := G.carrier))
    (HXY : ContourCorQRawHomRationalImageSystem sourceBulk middleBulk)
    (HYZ : ContourCorQRawHomRationalImageSystem middleBulk targetBulk)
    (F : ContourCorQHom X Y)
    (K : ContourCorQHom Y Z) :
    category.comp
        (HXY.quotientImage (ContourCorQHom.neg F))
        (HYZ.quotientImage K) =
      (-1 : Rat) • category.comp (HXY.quotientImage F) (HYZ.quotientImage K) :=
  parentComp_scale_left category HXY HYZ (-1) F K

/-- Parent composition is compatible with negation in the right broad quotient image. -/
theorem parentComp_neg_right
    {X Y Z : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {middleBulk : SmoothAlgebraization G Y}
    {targetBulk : SmoothAlgebraization G Z}
    (category : SmCorQ (k := G.carrier))
    (HXY : ContourCorQRawHomRationalImageSystem sourceBulk middleBulk)
    (HYZ : ContourCorQRawHomRationalImageSystem middleBulk targetBulk)
    (F : ContourCorQHom X Y)
    (K : ContourCorQHom Y Z) :
    category.comp
        (HXY.quotientImage F)
        (HYZ.quotientImage (ContourCorQHom.neg K)) =
      (-1 : Rat) • category.comp (HXY.quotientImage F) (HYZ.quotientImage K) :=
  parentComp_scale_right category HXY HYZ (-1) F K

/-- Parent composition expands subtraction in the left broad quotient image. -/
theorem parentComp_sub_left
    {X Y Z : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {middleBulk : SmoothAlgebraization G Y}
    {targetBulk : SmoothAlgebraization G Z}
    (category : SmCorQ (k := G.carrier))
    (HXY : ContourCorQRawHomRationalImageSystem sourceBulk middleBulk)
    (HYZ : ContourCorQRawHomRationalImageSystem middleBulk targetBulk)
    (F₁ F₂ : ContourCorQHom X Y)
    (K : ContourCorQHom Y Z) :
    category.comp
        (HXY.quotientImage (ContourCorQHom.sub F₁ F₂))
        (HYZ.quotientImage K) =
      category.comp (HXY.quotientImage F₁) (HYZ.quotientImage K) +
        (-1 : Rat) • category.comp (HXY.quotientImage F₂) (HYZ.quotientImage K) :=
  Eq.trans
    (parentComp_add_left category HXY HYZ F₁ (ContourCorQHom.neg F₂) K)
    (congrArg
      (fun R =>
        category.comp (HXY.quotientImage F₁) (HYZ.quotientImage K) + R)
      (parentComp_neg_left category HXY HYZ F₂ K))

/-- Parent composition expands subtraction in the right broad quotient image. -/
theorem parentComp_sub_right
    {X Y Z : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {middleBulk : SmoothAlgebraization G Y}
    {targetBulk : SmoothAlgebraization G Z}
    (category : SmCorQ (k := G.carrier))
    (HXY : ContourCorQRawHomRationalImageSystem sourceBulk middleBulk)
    (HYZ : ContourCorQRawHomRationalImageSystem middleBulk targetBulk)
    (F : ContourCorQHom X Y)
    (K₁ K₂ : ContourCorQHom Y Z) :
    category.comp
        (HXY.quotientImage F)
        (HYZ.quotientImage (ContourCorQHom.sub K₁ K₂)) =
      category.comp (HXY.quotientImage F) (HYZ.quotientImage K₁) +
        (-1 : Rat) • category.comp (HXY.quotientImage F) (HYZ.quotientImage K₂) :=
  Eq.trans
    (parentComp_add_right category HXY HYZ F K₁ (ContourCorQHom.neg K₂))
    (congrArg
      (fun R =>
        category.comp (HXY.quotientImage F) (HYZ.quotientImage K₁) + R)
      (parentComp_neg_right category HXY HYZ F K₂))

end ContourCorQRawHomRationalImageSystem

end

end AnalyticMotives
end LFunctions
end Boundary

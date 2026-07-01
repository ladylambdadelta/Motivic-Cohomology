import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.CorrespondenceAlgebraization.Balancing.QuotientImages.Operations.Owner

/-!
# Parent composition and quotient parent images

This file records the parent-side bilinearity of composition after applying
the descended parent rational finite-correspondence image to transfer-ready
contour homs.
-/

universe u

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

noncomputable section

variable {G : PerfectAnalyticGround.{u}}

namespace ContourCorQHom

/-- Parent composition with a zero left contour input is zero. -/
theorem parentComp_zero_left
    {X Y Z : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {middleBulk : SmoothAlgebraization G Y}
    {targetBulk : SmoothAlgebraization G Z}
    (category : SmCorQ (k := G.carrier))
    (HXY : ContourCorQRawHomAlgebraizationSystem sourceBulk middleBulk)
    (HYZ : ContourCorQRawHomAlgebraizationSystem middleBulk targetBulk)
    (K : ContourCorQHom Y Z) :
    category.comp
        (parentRationalCorrespondence HXY (ContourCorQHom.zero X Y))
        (parentRationalCorrespondence HYZ K) =
      0 :=
  Eq.trans
    (congrArg
      (fun R =>
        category.comp R (parentRationalCorrespondence HYZ K))
      (parentRationalCorrespondence_zero HXY))
    (SmCorQ.zero_comp category (parentRationalCorrespondence HYZ K))

/-- Parent composition with a zero right contour input is zero. -/
theorem parentComp_zero_right
    {X Y Z : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {middleBulk : SmoothAlgebraization G Y}
    {targetBulk : SmoothAlgebraization G Z}
    (category : SmCorQ (k := G.carrier))
    (HXY : ContourCorQRawHomAlgebraizationSystem sourceBulk middleBulk)
    (HYZ : ContourCorQRawHomAlgebraizationSystem middleBulk targetBulk)
    (F : ContourCorQHom X Y) :
    category.comp
        (parentRationalCorrespondence HXY F)
        (parentRationalCorrespondence HYZ (ContourCorQHom.zero Y Z)) =
      0 :=
  Eq.trans
    (congrArg
      (fun R =>
        category.comp (parentRationalCorrespondence HXY F) R)
      (parentRationalCorrespondence_zero HYZ))
    (SmCorQ.comp_zero category (parentRationalCorrespondence HXY F))

/-- Parent composition is additive in the left contour input after parent imaging. -/
theorem parentComp_add_left
    {X Y Z : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {middleBulk : SmoothAlgebraization G Y}
    {targetBulk : SmoothAlgebraization G Z}
    (category : SmCorQ (k := G.carrier))
    (HXY : ContourCorQRawHomAlgebraizationSystem sourceBulk middleBulk)
    (HYZ : ContourCorQRawHomAlgebraizationSystem middleBulk targetBulk)
    (F₁ F₂ : ContourCorQHom X Y)
    (K : ContourCorQHom Y Z) :
    category.comp
        (parentRationalCorrespondence HXY (ContourCorQHom.add F₁ F₂))
        (parentRationalCorrespondence HYZ K) =
      category.comp
        (parentRationalCorrespondence HXY F₁)
        (parentRationalCorrespondence HYZ K) +
        category.comp
          (parentRationalCorrespondence HXY F₂)
          (parentRationalCorrespondence HYZ K) :=
  Eq.trans
    (congrArg
      (fun R =>
        category.comp R (parentRationalCorrespondence HYZ K))
      (parentRationalCorrespondence_add HXY F₁ F₂))
    (SmCorQ.add_comp
      category
      (parentRationalCorrespondence HXY F₁)
      (parentRationalCorrespondence HXY F₂)
      (parentRationalCorrespondence HYZ K))

/-- Parent composition is additive in the right contour input after parent imaging. -/
theorem parentComp_add_right
    {X Y Z : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {middleBulk : SmoothAlgebraization G Y}
    {targetBulk : SmoothAlgebraization G Z}
    (category : SmCorQ (k := G.carrier))
    (HXY : ContourCorQRawHomAlgebraizationSystem sourceBulk middleBulk)
    (HYZ : ContourCorQRawHomAlgebraizationSystem middleBulk targetBulk)
    (F : ContourCorQHom X Y)
    (K₁ K₂ : ContourCorQHom Y Z) :
    category.comp
        (parentRationalCorrespondence HXY F)
        (parentRationalCorrespondence HYZ (ContourCorQHom.add K₁ K₂)) =
      category.comp
        (parentRationalCorrespondence HXY F)
        (parentRationalCorrespondence HYZ K₁) +
        category.comp
          (parentRationalCorrespondence HXY F)
          (parentRationalCorrespondence HYZ K₂) :=
  Eq.trans
    (congrArg
      (fun R =>
        category.comp (parentRationalCorrespondence HXY F) R)
      (parentRationalCorrespondence_add HYZ K₁ K₂))
    (SmCorQ.comp_add
      category
      (parentRationalCorrespondence HXY F)
      (parentRationalCorrespondence HYZ K₁)
      (parentRationalCorrespondence HYZ K₂))

/-- Parent composition is compatible with scalar multiplication in the left contour input. -/
theorem parentComp_scale_left
    {X Y Z : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {middleBulk : SmoothAlgebraization G Y}
    {targetBulk : SmoothAlgebraization G Z}
    (category : SmCorQ (k := G.carrier))
    (HXY : ContourCorQRawHomAlgebraizationSystem sourceBulk middleBulk)
    (HYZ : ContourCorQRawHomAlgebraizationSystem middleBulk targetBulk)
    (q : Rat)
    (F : ContourCorQHom X Y)
    (K : ContourCorQHom Y Z) :
    category.comp
        (parentRationalCorrespondence HXY (ContourCorQHom.scale q F))
        (parentRationalCorrespondence HYZ K) =
      q • category.comp
        (parentRationalCorrespondence HXY F)
        (parentRationalCorrespondence HYZ K) :=
  Eq.trans
    (congrArg
      (fun R =>
        category.comp R (parentRationalCorrespondence HYZ K))
      (parentRationalCorrespondence_scale HXY q F))
    (SmCorQ.smul_comp
      category q
      (parentRationalCorrespondence HXY F)
      (parentRationalCorrespondence HYZ K))

/-- Parent composition is compatible with scalar multiplication in the right contour input. -/
theorem parentComp_scale_right
    {X Y Z : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {middleBulk : SmoothAlgebraization G Y}
    {targetBulk : SmoothAlgebraization G Z}
    (category : SmCorQ (k := G.carrier))
    (HXY : ContourCorQRawHomAlgebraizationSystem sourceBulk middleBulk)
    (HYZ : ContourCorQRawHomAlgebraizationSystem middleBulk targetBulk)
    (q : Rat)
    (F : ContourCorQHom X Y)
    (K : ContourCorQHom Y Z) :
    category.comp
        (parentRationalCorrespondence HXY F)
        (parentRationalCorrespondence HYZ (ContourCorQHom.scale q K)) =
      q • category.comp
        (parentRationalCorrespondence HXY F)
        (parentRationalCorrespondence HYZ K) :=
  Eq.trans
    (congrArg
      (fun R =>
        category.comp (parentRationalCorrespondence HXY F) R)
      (parentRationalCorrespondence_scale HYZ q K))
    (SmCorQ.comp_smul
      category q
      (parentRationalCorrespondence HXY F)
      (parentRationalCorrespondence HYZ K))

/-- Parent composition is compatible with negation in the left contour input. -/
theorem parentComp_neg_left
    {X Y Z : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {middleBulk : SmoothAlgebraization G Y}
    {targetBulk : SmoothAlgebraization G Z}
    (category : SmCorQ (k := G.carrier))
    (HXY : ContourCorQRawHomAlgebraizationSystem sourceBulk middleBulk)
    (HYZ : ContourCorQRawHomAlgebraizationSystem middleBulk targetBulk)
    (F : ContourCorQHom X Y)
    (K : ContourCorQHom Y Z) :
    category.comp
        (parentRationalCorrespondence HXY (ContourCorQHom.neg F))
        (parentRationalCorrespondence HYZ K) =
      (-1 : Rat) • category.comp
        (parentRationalCorrespondence HXY F)
        (parentRationalCorrespondence HYZ K) :=
  parentComp_scale_left category HXY HYZ (-1) F K

/-- Parent composition is compatible with negation in the right contour input. -/
theorem parentComp_neg_right
    {X Y Z : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {middleBulk : SmoothAlgebraization G Y}
    {targetBulk : SmoothAlgebraization G Z}
    (category : SmCorQ (k := G.carrier))
    (HXY : ContourCorQRawHomAlgebraizationSystem sourceBulk middleBulk)
    (HYZ : ContourCorQRawHomAlgebraizationSystem middleBulk targetBulk)
    (F : ContourCorQHom X Y)
    (K : ContourCorQHom Y Z) :
    category.comp
        (parentRationalCorrespondence HXY F)
        (parentRationalCorrespondence HYZ (ContourCorQHom.neg K)) =
      (-1 : Rat) • category.comp
        (parentRationalCorrespondence HXY F)
        (parentRationalCorrespondence HYZ K) :=
  parentComp_scale_right category HXY HYZ (-1) F K

/-- Parent composition expands subtraction in the left contour input. -/
theorem parentComp_sub_left
    {X Y Z : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {middleBulk : SmoothAlgebraization G Y}
    {targetBulk : SmoothAlgebraization G Z}
    (category : SmCorQ (k := G.carrier))
    (HXY : ContourCorQRawHomAlgebraizationSystem sourceBulk middleBulk)
    (HYZ : ContourCorQRawHomAlgebraizationSystem middleBulk targetBulk)
    (F₁ F₂ : ContourCorQHom X Y)
    (K : ContourCorQHom Y Z) :
    category.comp
        (parentRationalCorrespondence HXY (ContourCorQHom.sub F₁ F₂))
        (parentRationalCorrespondence HYZ K) =
      category.comp
        (parentRationalCorrespondence HXY F₁)
        (parentRationalCorrespondence HYZ K) +
        (-1 : Rat) • category.comp
          (parentRationalCorrespondence HXY F₂)
          (parentRationalCorrespondence HYZ K) :=
  Eq.trans
    (parentComp_add_left category HXY HYZ F₁ (ContourCorQHom.neg F₂) K)
    (congrArg
      (fun R =>
        category.comp
          (parentRationalCorrespondence HXY F₁)
          (parentRationalCorrespondence HYZ K) + R)
      (parentComp_neg_left category HXY HYZ F₂ K))

/-- Parent composition expands subtraction in the right contour input. -/
theorem parentComp_sub_right
    {X Y Z : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {middleBulk : SmoothAlgebraization G Y}
    {targetBulk : SmoothAlgebraization G Z}
    (category : SmCorQ (k := G.carrier))
    (HXY : ContourCorQRawHomAlgebraizationSystem sourceBulk middleBulk)
    (HYZ : ContourCorQRawHomAlgebraizationSystem middleBulk targetBulk)
    (F : ContourCorQHom X Y)
    (K₁ K₂ : ContourCorQHom Y Z) :
    category.comp
        (parentRationalCorrespondence HXY F)
        (parentRationalCorrespondence HYZ (ContourCorQHom.sub K₁ K₂)) =
      category.comp
        (parentRationalCorrespondence HXY F)
        (parentRationalCorrespondence HYZ K₁) +
        (-1 : Rat) • category.comp
          (parentRationalCorrespondence HXY F)
          (parentRationalCorrespondence HYZ K₂) :=
  Eq.trans
    (parentComp_add_right category HXY HYZ F K₁ (ContourCorQHom.neg K₂))
    (congrArg
      (fun R =>
        category.comp
          (parentRationalCorrespondence HXY F)
          (parentRationalCorrespondence HYZ K₁) + R)
      (parentComp_neg_right category HXY HYZ F K₂))

end ContourCorQHom

end

end AnalyticMotives
end LFunctions
end Boundary

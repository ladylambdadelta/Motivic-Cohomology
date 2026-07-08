import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Preadditive.Maps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.VerdierQuotient.Fractions.Owner

/-!
# Fraction calculus for comparison-source morphisms

The comparison source is the analytic stable Verdier quotient.  This file
exposes the Verdier left-fraction representation theorem using comparison
source names, so motivic t-structure arguments can reason about arbitrary
stable morphisms through their concrete analytic roofs.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The comparison-source quotient functor is a localization at the concrete
analytic Verdier inverted morphisms. -/
instance TraceAnalyticDMgmComparisonSource.quotientFunctor_isLocalization_stableNull :
    TraceAnalyticDMgmComparisonSource.quotientFunctor.IsLocalization
      TraceAnalyticStableNullSubcategory.invertedMorphisms :=
  TraceAnalyticDMgmComparisonSource.isLocalization

/-- Every comparison-source morphism between quotient-represented additive
homotopy objects is represented by an analytic Verdier left fraction. -/
theorem TraceAnalyticDMgmComparisonSource.exists_leftFraction
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (hom :
      TraceAnalyticDMgmComparisonSource.objectOf source ⟶
        TraceAnalyticDMgmComparisonSource.objectOf target) :
    ∃ fraction :
      TraceAnalyticStableNullSubcategory.invertedMorphisms.LeftFraction
        source
        target,
      hom =
        fraction.map
          TraceAnalyticDMgmComparisonSource.quotientFunctor
          (CategoryTheory.Localization.inverts
            TraceAnalyticDMgmComparisonSource.quotientFunctor
            TraceAnalyticStableNullSubcategory.invertedMorphisms) :=
  TraceAnalyticStableMotiveCategory.exists_leftFraction hom

/-- A comparison-source left fraction becomes its numerator after
postcomposing with the localized denominator. -/
theorem TraceAnalyticDMgmComparisonSource.leftFraction_map_comp_denominator
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (fraction :
      TraceAnalyticStableNullSubcategory.invertedMorphisms.LeftFraction
        source
        target) :
    fraction.map
        TraceAnalyticDMgmComparisonSource.quotientFunctor
        (CategoryTheory.Localization.inverts
          TraceAnalyticDMgmComparisonSource.quotientFunctor
          TraceAnalyticStableNullSubcategory.invertedMorphisms) ≫
      TraceAnalyticDMgmComparisonSource.quotientFunctor.map fraction.s =
        TraceAnalyticDMgmComparisonSource.quotientFunctor.map fraction.f :=
  TraceAnalyticStableMotiveCategory.leftFraction_map_comp_denominator
    fraction

/-- If the localized numerator of a comparison-source left fraction is zero,
then the represented roof morphism is zero. -/
theorem TraceAnalyticDMgmComparisonSource.leftFraction_map_eq_zero_of_numerator_zero
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (fraction :
      TraceAnalyticStableNullSubcategory.invertedMorphisms.LeftFraction
        source
        target)
    (numerator_zero :
      TraceAnalyticDMgmComparisonSource.quotientFunctor.map fraction.f =
        (0 :
          TraceAnalyticDMgmComparisonSource.quotientFunctor.obj source ⟶
            TraceAnalyticDMgmComparisonSource.quotientFunctor.obj
              fraction.Y')) :
    fraction.map
        TraceAnalyticDMgmComparisonSource.quotientFunctor
        (CategoryTheory.Localization.inverts
          TraceAnalyticDMgmComparisonSource.quotientFunctor
          TraceAnalyticStableNullSubcategory.invertedMorphisms) =
      0 :=
  letI :
      IsIso
        (TraceAnalyticDMgmComparisonSource.quotientFunctor.map
          fraction.s) :=
    CategoryTheory.Localization.inverts
      TraceAnalyticDMgmComparisonSource.quotientFunctor
      TraceAnalyticStableNullSubcategory.invertedMorphisms
      fraction.s
      fraction.hs
  let denominator_hom_inv :
      TraceAnalyticDMgmComparisonSource.quotientFunctor.map fraction.s ≫
          inv
            (TraceAnalyticDMgmComparisonSource.quotientFunctor.map
              fraction.s) =
        𝟙
          (TraceAnalyticDMgmComparisonSource.quotientFunctor.obj target) :=
    IsIso.hom_inv_id
      (TraceAnalyticDMgmComparisonSource.quotientFunctor.map fraction.s)
  let roofMap :
      TraceAnalyticDMgmComparisonSource.quotientFunctor.obj source ⟶
        TraceAnalyticDMgmComparisonSource.quotientFunctor.obj target :=
    fraction.map
      TraceAnalyticDMgmComparisonSource.quotientFunctor
      (CategoryTheory.Localization.inverts
        TraceAnalyticDMgmComparisonSource.quotientFunctor
        TraceAnalyticStableNullSubcategory.invertedMorphisms)
  let roof_comp_denominator :
      roofMap ≫
          TraceAnalyticDMgmComparisonSource.quotientFunctor.map fraction.s =
        TraceAnalyticDMgmComparisonSource.quotientFunctor.map fraction.f :=
    TraceAnalyticDMgmComparisonSource.leftFraction_map_comp_denominator
      fraction
  let roof_comp_denominator_zero :
      roofMap ≫
          TraceAnalyticDMgmComparisonSource.quotientFunctor.map fraction.s =
        0 :=
    Eq.trans roof_comp_denominator numerator_zero
  Eq.trans
    (Eq.symm
      (Eq.trans
        (Category.assoc
          roofMap
          (TraceAnalyticDMgmComparisonSource.quotientFunctor.map
            fraction.s)
          (inv
            (TraceAnalyticDMgmComparisonSource.quotientFunctor.map
              fraction.s)))
        (Eq.trans
          (congrArg
            (fun right => roofMap ≫ right)
            denominator_hom_inv)
          (Category.comp_id roofMap))))
    (Eq.trans
      (congrArg
        (fun left =>
          left ≫
            inv
              (TraceAnalyticDMgmComparisonSource.quotientFunctor.map
                fraction.s))
        roof_comp_denominator_zero)
      (Category.zero_comp
        (inv
          (TraceAnalyticDMgmComparisonSource.quotientFunctor.map
            fraction.s))))

/-- If an additive-homotopy morphism becomes zero after postcomposition by an
analytic Verdier-inverted morphism, then its comparison-source image is zero.
-/
theorem TraceAnalyticDMgmComparisonSource.map_eq_zero_of_postcomp_inverted_zero
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (hom : source ⟶ target)
    (postcomp_zero :
      ∃ postTarget : TraceAnalyticAdditiveHomotopyCategory,
        ∃ post : target ⟶ postTarget,
          ∃ post_inverted :
            TraceAnalyticStableNullSubcategory.invertedMorphisms post,
            hom ≫ post = 0) :
    TraceAnalyticDMgmComparisonSource.quotientFunctor.map hom =
      (0 :
        TraceAnalyticDMgmComparisonSource.quotientFunctor.obj source ⟶
          TraceAnalyticDMgmComparisonSource.quotientFunctor.obj target) :=
  let map_hom_eq_map_zero :
      TraceAnalyticDMgmComparisonSource.quotientFunctor.map hom =
        TraceAnalyticDMgmComparisonSource.quotientFunctor.map
          (0 : source ⟶ target) :=
    (CategoryTheory.MorphismProperty.map_eq_iff_postcomp
      TraceAnalyticDMgmComparisonSource.quotientFunctor
      TraceAnalyticStableNullSubcategory.invertedMorphisms
      hom
      (0 : source ⟶ target)).2
        (Exists.elim
          postcomp_zero
          (fun postTarget postData =>
            Exists.elim
              postData
              (fun post postInvertedData =>
                Exists.elim
                  postInvertedData
                  (fun post_inverted hom_post_zero =>
                    Exists.intro
                      postTarget
                      (Exists.intro
                        post
                        (Exists.intro
                          post_inverted
                          (Eq.trans
                            hom_post_zero
                            (Eq.symm
                              (Category.zero_comp post)))))))))
  Eq.trans
    map_hom_eq_map_zero
    (TraceAnalyticDMgmComparisonSource.mapOf_zero source target)

/-- If the numerator of a comparison-source left fraction becomes zero after
postcomposition by an analytic Verdier-inverted morphism, then the represented
roof morphism is zero. -/
theorem TraceAnalyticDMgmComparisonSource.leftFraction_map_eq_zero_of_numerator_postcomp_zero
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (fraction :
      TraceAnalyticStableNullSubcategory.invertedMorphisms.LeftFraction
        source
        target)
    (numerator_postcomp_zero :
      ∃ postTarget : TraceAnalyticAdditiveHomotopyCategory,
        ∃ post : fraction.Y' ⟶ postTarget,
          ∃ post_inverted :
            TraceAnalyticStableNullSubcategory.invertedMorphisms post,
            fraction.f ≫ post = 0) :
    fraction.map
        TraceAnalyticDMgmComparisonSource.quotientFunctor
        (CategoryTheory.Localization.inverts
          TraceAnalyticDMgmComparisonSource.quotientFunctor
          TraceAnalyticStableNullSubcategory.invertedMorphisms) =
      0 :=
  TraceAnalyticDMgmComparisonSource.leftFraction_map_eq_zero_of_numerator_zero
    fraction
    (TraceAnalyticDMgmComparisonSource.map_eq_zero_of_postcomp_inverted_zero
      fraction.f
      numerator_postcomp_zero)

/-- If the numerator of a comparison-source left fraction is killed by
postcomposition with the first map of a distinguished triangle whose cone is
stable-null, then the represented roof morphism is zero. -/
theorem TraceAnalyticDMgmComparisonSource.leftFraction_map_eq_zero_of_numerator_nullCone_postcomp_zero
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (fraction :
      TraceAnalyticStableNullSubcategory.invertedMorphisms.LeftFraction
        source
        target)
    (postTarget postCone : TraceAnalyticAdditiveHomotopyCategory)
    (post : fraction.Y' ⟶ postTarget)
    (postConeMap : postTarget ⟶ postCone)
    (postBoundary : postCone ⟶ fraction.Y'⟦(1 : ℤ)⟧)
    (distinguished :
      Triangle.mk post postConeMap postBoundary ∈
        TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles)
    (postCone_null :
      TraceAnalyticStableNullSubcategory.P postCone)
    (numerator_post_zero : fraction.f ≫ post = 0) :
    fraction.map
        TraceAnalyticDMgmComparisonSource.quotientFunctor
        (CategoryTheory.Localization.inverts
          TraceAnalyticDMgmComparisonSource.quotientFunctor
          TraceAnalyticStableNullSubcategory.invertedMorphisms) =
      0 :=
  TraceAnalyticDMgmComparisonSource
    .leftFraction_map_eq_zero_of_numerator_postcomp_zero
      fraction
      (Exists.intro
        postTarget
        (Exists.intro
          post
          (Exists.intro
            (TraceAnalyticStableNullSubcategory
              .inverted_firstMap_of_triangle
                distinguished
                postCone_null)
            numerator_post_zero)))

/-- If the numerator of a comparison-source left fraction is killed by
postcomposition with a stable acyclic generator first map, then the represented
roof morphism is zero.  The equality identifies the roof numerator target with
the generator source before composing with the generator first map. -/
theorem TraceAnalyticDMgmComparisonSource.leftFraction_map_eq_zero_of_numerator_generator_postcomp_zero
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (fraction :
      TraceAnalyticStableNullSubcategory.invertedMorphisms.LeftFraction
        source
        target)
    (generator : TraceAnalyticStableAcyclicGenerator)
    (source_eq : fraction.Y' = generator.source)
    (numerator_generator_zero :
      fraction.f ≫ (eqToHom source_eq ≫ generator.firstMap) = 0) :
    fraction.map
        TraceAnalyticDMgmComparisonSource.quotientFunctor
        (CategoryTheory.Localization.inverts
          TraceAnalyticDMgmComparisonSource.quotientFunctor
          TraceAnalyticStableNullSubcategory.invertedMorphisms) =
      0 :=
  let transportedFirstMap : fraction.Y' ⟶ generator.target :=
    eqToHom source_eq ≫ generator.firstMap
  let transportedFirstMap_inverted :
      TraceAnalyticStableNullSubcategory.invertedMorphisms
        transportedFirstMap :=
    TraceAnalyticStableNullSubcategory.invertedMorphisms.comp_mem
      (eqToHom source_eq)
      generator.firstMap
      (CategoryTheory.Triangulated.Subcategory.W_of_isIso
        TraceAnalyticStableNullSubcategory
        (eqToHom source_eq))
      (TraceAnalyticStableNullSubcategory
        .generator_firstMap_inverted generator)
  TraceAnalyticDMgmComparisonSource
    .leftFraction_map_eq_zero_of_numerator_postcomp_zero
      fraction
      (Exists.intro
        generator.target
        (Exists.intro
          transportedFirstMap
          (Exists.intro
            transportedFirstMap_inverted
            numerator_generator_zero)))

/-- If the numerator of a comparison-source left fraction is killed by a
concrete analytic localization input's stable map, then the represented roof
morphism is zero. -/
theorem TraceAnalyticDMgmComparisonSource.leftFraction_map_eq_zero_of_numerator_localizationInput_postcomp_zero
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (fraction :
      TraceAnalyticStableNullSubcategory.invertedMorphisms.LeftFraction
        source
        target)
    (input : TraceLocalizationInput)
    (source_eq : fraction.Y' = input.stableSource)
    (numerator_input_zero :
      fraction.f ≫ (eqToHom source_eq ≫ input.stableMap) = 0) :
    fraction.map
        TraceAnalyticDMgmComparisonSource.quotientFunctor
        (CategoryTheory.Localization.inverts
          TraceAnalyticDMgmComparisonSource.quotientFunctor
          TraceAnalyticStableNullSubcategory.invertedMorphisms) =
      0 :=
  TraceAnalyticDMgmComparisonSource
    .leftFraction_map_eq_zero_of_numerator_generator_postcomp_zero
      fraction
      ({ input := input } : TraceAnalyticStableAcyclicGenerator)
      source_eq
      numerator_input_zero

end AnalyticMotives
end LFunctions
end Boundary

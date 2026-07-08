import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.VerdierQuotient.UniversalProperty.DescendByClosure.NaturalTransformations.Owner

/-!
# Components of descended natural transformations

This file records the component formula for a natural transformation descended
through the stable analytic Verdier quotient by null-killing closure data.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- At a quotient-represented object, a descended natural transformation is the
original natural transformation conjugated by the two quotient factorization
isomorphisms. -/
theorem TraceAnalyticStableMotiveCategory.descendByNullKillingClosureNatTrans_app_objectOf
    {target : Type*} [CategoryTheory.Category target]
    [CategoryTheory.HasShift target ℤ]
    [CategoryTheory.HasZeroObject target]
    [CategoryTheory.Preadditive target]
    [∀ degree : ℤ, (CategoryTheory.shiftFunctor target degree).Additive]
    [CategoryTheory.Pretriangulated target]
    (first second : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    [first.CommShift ℤ]
    [first.IsTriangulated]
    [second.CommShift ℤ]
    [second.IsTriangulated]
    (firstZeroImage : IsZero (first.obj 0))
    (firstGeneratorImage :
      ∀ generator : TraceAnalyticStableAcyclicGenerator,
        IsZero (first.obj generator.object))
    (firstShiftImage :
      ∀ (object : TraceAnalyticAdditiveHomotopyCategory)
        (degree : ℤ),
        TraceAnalyticStableNullObject object →
        IsZero (first.obj object) →
        IsZero (first.obj (object⟦degree⟧)))
    (firstExtensionImage :
      ∀ triangle : Triangle TraceAnalyticAdditiveHomotopyCategory,
        triangle ∈ TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles →
        TraceAnalyticStableNullObject triangle.obj₁ →
        TraceAnalyticStableNullObject triangle.obj₃ →
        IsZero (first.obj triangle.obj₁) →
        IsZero (first.obj triangle.obj₃) →
        IsZero (first.obj triangle.obj₂))
    (secondZeroImage : IsZero (second.obj 0))
    (secondGeneratorImage :
      ∀ generator : TraceAnalyticStableAcyclicGenerator,
        IsZero (second.obj generator.object))
    (secondShiftImage :
      ∀ (object : TraceAnalyticAdditiveHomotopyCategory)
        (degree : ℤ),
        TraceAnalyticStableNullObject object →
        IsZero (second.obj object) →
        IsZero (second.obj (object⟦degree⟧)))
    (secondExtensionImage :
      ∀ triangle : Triangle TraceAnalyticAdditiveHomotopyCategory,
        triangle ∈ TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles →
        TraceAnalyticStableNullObject triangle.obj₁ →
        TraceAnalyticStableNullObject triangle.obj₃ →
        IsZero (second.obj triangle.obj₁) →
        IsZero (second.obj triangle.obj₃) →
        IsZero (second.obj triangle.obj₂))
    (transformation : first ⟶ second)
    (object : TraceAnalyticAdditiveHomotopyCategory) :
    (TraceAnalyticStableMotiveCategory.descendByNullKillingClosureNatTrans
      first
      second
      firstZeroImage
      firstGeneratorImage
      firstShiftImage
      firstExtensionImage
      secondZeroImage
      secondGeneratorImage
      secondShiftImage
      secondExtensionImage
      transformation).app
        (TraceAnalyticStableMotiveCategory.objectOf object) =
      (TraceAnalyticStableMotiveCategory.descendByNullKillingClosureObjectIso
        first
        firstZeroImage
        firstGeneratorImage
        firstShiftImage
        firstExtensionImage
        object).hom ≫
      transformation.app object ≫
      (TraceAnalyticStableMotiveCategory.descendByNullKillingClosureObjectIso
        second
        secondZeroImage
        secondGeneratorImage
        secondShiftImage
        secondExtensionImage
        object).inv :=
  CategoryTheory.Localization.liftNatTrans_app
    TraceAnalyticStableMotiveCategory.quotientFunctor
    TraceAnalyticStableMotiveCategory.invertedMorphisms
    first
    second
    (TraceAnalyticStableMotiveCategory.descendByNullKillingClosure
      first
      firstZeroImage
      firstGeneratorImage
      firstShiftImage
      firstExtensionImage)
    (TraceAnalyticStableMotiveCategory.descendByNullKillingClosure
      second
      secondZeroImage
      secondGeneratorImage
      secondShiftImage
      secondExtensionImage)
    transformation
    object

end AnalyticMotives
end LFunctions
end Boundary

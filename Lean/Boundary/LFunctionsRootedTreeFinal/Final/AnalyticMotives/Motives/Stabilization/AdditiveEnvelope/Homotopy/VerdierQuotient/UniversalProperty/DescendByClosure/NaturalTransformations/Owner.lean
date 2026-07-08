import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.VerdierQuotient.UniversalProperty.DescendByClosure.Projections.Owner

/-!
# Natural transformations between descended functors

This file packages the natural transformation supplied by the localization
universal property for functors descended using null-killing closure data.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- A natural transformation between triangulated functors satisfying
null-killing closure data descends to a natural transformation between their
descended stable-analytic-motive functors. -/
def TraceAnalyticStableMotiveCategory.descendByNullKillingClosureNatTrans
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
    (transformation : first ⟶ second) :
    TraceAnalyticStableMotiveCategory.descendByNullKillingClosure
      first
      firstZeroImage
      firstGeneratorImage
      firstShiftImage
      firstExtensionImage ⟶
    TraceAnalyticStableMotiveCategory.descendByNullKillingClosure
      second
      secondZeroImage
      secondGeneratorImage
      secondShiftImage
      secondExtensionImage :=
  TraceAnalyticStableMotiveCategory.liftNatTrans
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

/-- The descended natural transformation is the localization-lifted natural
transformation between the two descended functors. -/
theorem TraceAnalyticStableMotiveCategory.descendByNullKillingClosureNatTrans_eq
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
    (transformation : first ⟶ second) :
    TraceAnalyticStableMotiveCategory.descendByNullKillingClosureNatTrans
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
      transformation =
    TraceAnalyticStableMotiveCategory.liftNatTrans
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
      transformation :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

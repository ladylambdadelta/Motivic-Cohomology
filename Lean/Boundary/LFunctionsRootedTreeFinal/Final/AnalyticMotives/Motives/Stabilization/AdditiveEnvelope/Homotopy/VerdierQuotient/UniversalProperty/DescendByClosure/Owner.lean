import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.NullSubcategory.Killing.InversionCriterion.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.VerdierQuotient.UniversalProperty.Owner

/-!
# Descending functors by null-killing closure

This file packages the concrete descent constructor for comparison functors:
a triangulated functor out of the additive analytic homotopy category descends
to stable analytic motives once it satisfies the null-killing closure data.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The `IsInvertedBy` certificate produced from concrete null-killing closure data. -/
def TraceAnalyticStableMotiveCategory.invertsByNullKillingClosure
    {target : Type*} [CategoryTheory.Category target]
    [CategoryTheory.HasShift target ℤ]
    [CategoryTheory.HasZeroObject target]
    [CategoryTheory.Preadditive target]
    [∀ degree : ℤ, (CategoryTheory.shiftFunctor target degree).Additive]
    [CategoryTheory.Pretriangulated target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    [functor.CommShift ℤ]
    [functor.IsTriangulated]
    (zeroImage : IsZero (functor.obj 0))
    (generatorImage :
      ∀ generator : TraceAnalyticStableAcyclicGenerator,
        IsZero (functor.obj generator.object))
    (shiftImage :
      ∀ (object : TraceAnalyticAdditiveHomotopyCategory)
        (degree : ℤ),
        TraceAnalyticStableNullObject object →
        IsZero (functor.obj object) →
        IsZero (functor.obj (object⟦degree⟧)))
    (extensionImage :
      ∀ triangle : Triangle TraceAnalyticAdditiveHomotopyCategory,
        triangle ∈ TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles →
        TraceAnalyticStableNullObject triangle.obj₁ →
        TraceAnalyticStableNullObject triangle.obj₃ →
        IsZero (functor.obj triangle.obj₁) →
        IsZero (functor.obj triangle.obj₃) →
        IsZero (functor.obj triangle.obj₂)) :
    TraceAnalyticStableMotiveCategory.invertedMorphisms.IsInvertedBy functor :=
  TraceAnalyticStableNullSubcategory.functor_inverts_of_closure
    functor
    zeroImage
    generatorImage
    shiftImage
    extensionImage

/-- Descend a triangulated functor satisfying null-killing closure data to stable
analytic motives. -/
def TraceAnalyticStableMotiveCategory.descendByNullKillingClosure
    {target : Type*} [CategoryTheory.Category target]
    [CategoryTheory.HasShift target ℤ]
    [CategoryTheory.HasZeroObject target]
    [CategoryTheory.Preadditive target]
    [∀ degree : ℤ, (CategoryTheory.shiftFunctor target degree).Additive]
    [CategoryTheory.Pretriangulated target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    [functor.CommShift ℤ]
    [functor.IsTriangulated]
    (zeroImage : IsZero (functor.obj 0))
    (generatorImage :
      ∀ generator : TraceAnalyticStableAcyclicGenerator,
        IsZero (functor.obj generator.object))
    (shiftImage :
      ∀ (object : TraceAnalyticAdditiveHomotopyCategory)
        (degree : ℤ),
        TraceAnalyticStableNullObject object →
        IsZero (functor.obj object) →
        IsZero (functor.obj (object⟦degree⟧)))
    (extensionImage :
      ∀ triangle : Triangle TraceAnalyticAdditiveHomotopyCategory,
        triangle ∈ TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles →
        TraceAnalyticStableNullObject triangle.obj₁ →
        TraceAnalyticStableNullObject triangle.obj₃ →
        IsZero (functor.obj triangle.obj₁) →
        IsZero (functor.obj triangle.obj₃) →
        IsZero (functor.obj triangle.obj₂)) :
    TraceAnalyticStableMotiveCategory ⥤ target :=
  TraceAnalyticStableMotiveCategory.lift
    functor
    (TraceAnalyticStableMotiveCategory.invertsByNullKillingClosure
      functor
      zeroImage
      generatorImage
      shiftImage
      extensionImage)

/-- The descended functor composed with the quotient is the original functor. -/
def TraceAnalyticStableMotiveCategory.descendByNullKillingClosureFac
    {target : Type*} [CategoryTheory.Category target]
    [CategoryTheory.HasShift target ℤ]
    [CategoryTheory.HasZeroObject target]
    [CategoryTheory.Preadditive target]
    [∀ degree : ℤ, (CategoryTheory.shiftFunctor target degree).Additive]
    [CategoryTheory.Pretriangulated target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    [functor.CommShift ℤ]
    [functor.IsTriangulated]
    (zeroImage : IsZero (functor.obj 0))
    (generatorImage :
      ∀ generator : TraceAnalyticStableAcyclicGenerator,
        IsZero (functor.obj generator.object))
    (shiftImage :
      ∀ (object : TraceAnalyticAdditiveHomotopyCategory)
        (degree : ℤ),
        TraceAnalyticStableNullObject object →
        IsZero (functor.obj object) →
        IsZero (functor.obj (object⟦degree⟧)))
    (extensionImage :
      ∀ triangle : Triangle TraceAnalyticAdditiveHomotopyCategory,
        triangle ∈ TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles →
        TraceAnalyticStableNullObject triangle.obj₁ →
        TraceAnalyticStableNullObject triangle.obj₃ →
        IsZero (functor.obj triangle.obj₁) →
        IsZero (functor.obj triangle.obj₃) →
        IsZero (functor.obj triangle.obj₂)) :
    TraceAnalyticStableMotiveCategory.quotientFunctor ⋙
      TraceAnalyticStableMotiveCategory.descendByNullKillingClosure
        functor
        zeroImage
        generatorImage
        shiftImage
        extensionImage ≅ functor :=
  TraceAnalyticStableMotiveCategory.liftFac
    functor
    (TraceAnalyticStableMotiveCategory.invertsByNullKillingClosure
      functor
      zeroImage
      generatorImage
      shiftImage
      extensionImage)

/-- The descended functor is the localization lift associated to the closure certificate. -/
theorem TraceAnalyticStableMotiveCategory.descendByNullKillingClosure_eq_lift
    {target : Type*} [CategoryTheory.Category target]
    [CategoryTheory.HasShift target ℤ]
    [CategoryTheory.HasZeroObject target]
    [CategoryTheory.Preadditive target]
    [∀ degree : ℤ, (CategoryTheory.shiftFunctor target degree).Additive]
    [CategoryTheory.Pretriangulated target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    [functor.CommShift ℤ]
    [functor.IsTriangulated]
    (zeroImage : IsZero (functor.obj 0))
    (generatorImage :
      ∀ generator : TraceAnalyticStableAcyclicGenerator,
        IsZero (functor.obj generator.object))
    (shiftImage :
      ∀ (object : TraceAnalyticAdditiveHomotopyCategory)
        (degree : ℤ),
        TraceAnalyticStableNullObject object →
        IsZero (functor.obj object) →
        IsZero (functor.obj (object⟦degree⟧)))
    (extensionImage :
      ∀ triangle : Triangle TraceAnalyticAdditiveHomotopyCategory,
        triangle ∈ TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles →
        TraceAnalyticStableNullObject triangle.obj₁ →
        TraceAnalyticStableNullObject triangle.obj₃ →
        IsZero (functor.obj triangle.obj₁) →
        IsZero (functor.obj triangle.obj₃) →
        IsZero (functor.obj triangle.obj₂)) :
    TraceAnalyticStableMotiveCategory.descendByNullKillingClosure
      functor
      zeroImage
      generatorImage
      shiftImage
      extensionImage =
      TraceAnalyticStableMotiveCategory.lift
        functor
        (TraceAnalyticStableMotiveCategory.invertsByNullKillingClosure
          functor
          zeroImage
          generatorImage
          shiftImage
          extensionImage) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

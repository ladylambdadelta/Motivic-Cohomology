import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.VerdierQuotient.UniversalProperty.DescendByClosure.Projections.Owner

/-!
# Generator projection formulas for descended functors

This file specializes the quotient projection formula to the three morphisms of
each stable analytic acyclic triangle.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Projection formula for the first map of a stable acyclic generator. -/
theorem TraceAnalyticStableMotiveCategory.descendByNullKillingClosure_generator_firstMap_naturality
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
        IsZero (functor.obj triangle.obj₂))
    (generator : TraceAnalyticStableAcyclicGenerator) :
    (TraceAnalyticStableMotiveCategory.descendByNullKillingClosure
      functor
      zeroImage
      generatorImage
      shiftImage
      extensionImage).map
        (TraceAnalyticStableMotiveCategory.mapOf generator.firstMap) ≫
      (TraceAnalyticStableMotiveCategory.descendByNullKillingClosureObjectIso
        functor
        zeroImage
        generatorImage
        shiftImage
        extensionImage
        generator.target).hom =
      (TraceAnalyticStableMotiveCategory.descendByNullKillingClosureObjectIso
        functor
        zeroImage
        generatorImage
        shiftImage
        extensionImage
        generator.source).hom ≫
        functor.map generator.firstMap :=
  TraceAnalyticStableMotiveCategory.descendByNullKillingClosure_mapOf_naturality
    functor
    zeroImage
    generatorImage
    shiftImage
    extensionImage
    generator.firstMap

/-- Projection formula for the cone map of a stable acyclic generator. -/
theorem TraceAnalyticStableMotiveCategory.descendByNullKillingClosure_generator_coneMap_naturality
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
        IsZero (functor.obj triangle.obj₂))
    (generator : TraceAnalyticStableAcyclicGenerator) :
    (TraceAnalyticStableMotiveCategory.descendByNullKillingClosure
      functor
      zeroImage
      generatorImage
      shiftImage
      extensionImage).map
        (TraceAnalyticStableMotiveCategory.mapOf generator.coneMap) ≫
      (TraceAnalyticStableMotiveCategory.descendByNullKillingClosureObjectIso
        functor
        zeroImage
        generatorImage
        shiftImage
        extensionImage
        generator.object).hom =
      (TraceAnalyticStableMotiveCategory.descendByNullKillingClosureObjectIso
        functor
        zeroImage
        generatorImage
        shiftImage
        extensionImage
        generator.target).hom ≫
        functor.map generator.coneMap :=
  TraceAnalyticStableMotiveCategory.descendByNullKillingClosure_mapOf_naturality
    functor
    zeroImage
    generatorImage
    shiftImage
    extensionImage
    generator.coneMap

/-- Projection formula for the connecting map of a stable acyclic generator. -/
theorem TraceAnalyticStableMotiveCategory.descendByNullKillingClosure_generator_connectingMap_naturality
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
        IsZero (functor.obj triangle.obj₂))
    (generator : TraceAnalyticStableAcyclicGenerator) :
    (TraceAnalyticStableMotiveCategory.descendByNullKillingClosure
      functor
      zeroImage
      generatorImage
      shiftImage
      extensionImage).map
        (TraceAnalyticStableMotiveCategory.mapOf generator.connectingMap) ≫
      (TraceAnalyticStableMotiveCategory.descendByNullKillingClosureObjectIso
        functor
        zeroImage
        generatorImage
        shiftImage
        extensionImage
        generator.source⟦(1 : ℤ)⟧).hom =
      (TraceAnalyticStableMotiveCategory.descendByNullKillingClosureObjectIso
        functor
        zeroImage
        generatorImage
        shiftImage
        extensionImage
        generator.object).hom ≫
        functor.map generator.connectingMap :=
  TraceAnalyticStableMotiveCategory.descendByNullKillingClosure_mapOf_naturality
    functor
    zeroImage
    generatorImage
    shiftImage
    extensionImage
    generator.connectingMap

end AnalyticMotives
end LFunctions
end Boundary

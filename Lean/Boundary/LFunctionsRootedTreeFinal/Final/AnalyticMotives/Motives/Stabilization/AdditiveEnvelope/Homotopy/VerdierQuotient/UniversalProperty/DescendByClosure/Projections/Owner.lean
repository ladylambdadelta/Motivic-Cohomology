import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.VerdierQuotient.UniversalProperty.DescendByClosure.Owner

/-!
# Projection formulas for descended functors

This file exposes the object and morphism formulas supplied by the
factorization isomorphism of a functor descended through the stable analytic
Verdier quotient.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The descended functor sends the quotient image of an additive homotopy object
to an object isomorphic to the original functor value. -/
def TraceAnalyticStableMotiveCategory.descendByNullKillingClosureObjectIso
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
    (object : TraceAnalyticAdditiveHomotopyCategory) :
    (TraceAnalyticStableMotiveCategory.descendByNullKillingClosure
      functor
      zeroImage
      generatorImage
      shiftImage
      extensionImage).obj
        (TraceAnalyticStableMotiveCategory.objectOf object) ≅
      functor.obj object :=
  (TraceAnalyticStableMotiveCategory.descendByNullKillingClosureFac
    functor
    zeroImage
    generatorImage
    shiftImage
    extensionImage).app object

/-- The object projection is the component of the quotient factorization isomorphism. -/
theorem TraceAnalyticStableMotiveCategory.descendByNullKillingClosureObjectIso_eq
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
    (object : TraceAnalyticAdditiveHomotopyCategory) :
    TraceAnalyticStableMotiveCategory.descendByNullKillingClosureObjectIso
      functor
      zeroImage
      generatorImage
      shiftImage
      extensionImage
      object =
      (TraceAnalyticStableMotiveCategory.descendByNullKillingClosureFac
        functor
        zeroImage
        generatorImage
        shiftImage
        extensionImage).app object :=
  rfl

/-- The descended functor's morphism action on represented quotient morphisms is
compatible with the original functor through the factorization isomorphism. -/
theorem TraceAnalyticStableMotiveCategory.descendByNullKillingClosure_mapOf_naturality
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
    {source targetObject : TraceAnalyticAdditiveHomotopyCategory}
    (hom : source ⟶ targetObject) :
    (TraceAnalyticStableMotiveCategory.descendByNullKillingClosure
      functor
      zeroImage
      generatorImage
      shiftImage
      extensionImage).map
        (TraceAnalyticStableMotiveCategory.mapOf hom) ≫
      (TraceAnalyticStableMotiveCategory.descendByNullKillingClosureObjectIso
        functor
        zeroImage
        generatorImage
        shiftImage
        extensionImage
        targetObject).hom =
      (TraceAnalyticStableMotiveCategory.descendByNullKillingClosureObjectIso
        functor
        zeroImage
        generatorImage
        shiftImage
        extensionImage
        source).hom ≫
        functor.map hom :=
  (TraceAnalyticStableMotiveCategory.descendByNullKillingClosureFac
    functor
    zeroImage
    generatorImage
    shiftImage
    extensionImage).hom.naturality hom

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.NullSubcategory.Killing.Owner

/-!
# Inverting null-cone morphisms

If a triangulated functor kills every object in the stable null subcategory,
then it inverts every morphism whose cone lies in that null subcategory.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

/-- A triangulated functor that kills stable null objects inverts the analytic
Verdier morphism class. -/
theorem TraceAnalyticStableNullSubcategory.functor_inverts_of_null_objects
    {target : Type*} [CategoryTheory.Category target]
    [CategoryTheory.HasShift target ℤ]
    [CategoryTheory.HasZeroObject target]
    [CategoryTheory.Preadditive target]
    [∀ degree : ℤ, (CategoryTheory.shiftFunctor target degree).Additive]
    [CategoryTheory.Pretriangulated target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    [functor.CommShift ℤ]
    [functor.IsTriangulated]
    (killsNull :
      ∀ object : TraceAnalyticAdditiveHomotopyCategory,
        TraceAnalyticStableNullSubcategory.P object →
        IsZero (functor.obj object)) :
    TraceAnalyticStableNullSubcategory.invertedMorphisms.IsInvertedBy functor :=
  fun source targetObject morphism inverted =>
    match inverted with
    | ⟨coneObject, coneMap, connectingMap, distinguished, nullCone⟩ =>
        (Triangle.isZero₃_iff_isIso₁
          (functor.mapTriangle.obj
            (Triangle.mk morphism coneMap connectingMap))
          (functor.map_distinguished
            (Triangle.mk morphism coneMap connectingMap)
            distinguished)).1
          (killsNull coneObject nullCone)

/-- A triangulated functor satisfying the concrete null-killing closure data
inverts the analytic Verdier morphism class. -/
theorem TraceAnalyticStableNullSubcategory.functor_inverts_of_closure
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
    TraceAnalyticStableNullSubcategory.invertedMorphisms.IsInvertedBy functor :=
  TraceAnalyticStableNullSubcategory.functor_inverts_of_null_objects
    functor
    (fun object null =>
      TraceAnalyticStableNullSubcategory.functor_isZero_of_closure
        functor
        zeroImage
        generatorImage
        shiftImage
        extensionImage
        object
        null)

end AnalyticMotives
end LFunctions
end Boundary

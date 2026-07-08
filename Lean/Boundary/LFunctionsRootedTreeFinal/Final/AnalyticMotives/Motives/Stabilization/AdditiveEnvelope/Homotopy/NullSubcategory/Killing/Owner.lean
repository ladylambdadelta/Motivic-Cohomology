import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.NullSubcategory.Owner

/-!
# Killing the stable null subcategory

This file records the induction principle used by comparison functors: to kill
every object in the stable null subcategory it is enough to kill zero, kill the
concrete stable acyclic generators, and be closed under shifts and
distinguished extensions.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- A functor kills all stable null objects once it kills the generators and is
closed under the operations used to generate the null class. -/
theorem TraceAnalyticStableNullObject.functor_isZero_of_closure
    {target : Type*} [CategoryTheory.Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
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
    (object : TraceAnalyticAdditiveHomotopyCategory)
    (null : TraceAnalyticStableNullObject object) :
    IsZero (functor.obj object) :=
  match null with
  | TraceAnalyticStableNullObject.zero =>
      zeroImage
  | TraceAnalyticStableNullObject.generator generator =>
      generatorImage generator
  | TraceAnalyticStableNullObject.shift shiftedObject degree shiftedNull =>
      shiftImage
        shiftedObject
        degree
        shiftedNull
        (TraceAnalyticStableNullObject.functor_isZero_of_closure
          functor
          zeroImage
          generatorImage
          shiftImage
          extensionImage
          shiftedObject
          shiftedNull)
  | TraceAnalyticStableNullObject.extension triangle distinguished leftNull rightNull =>
      extensionImage
        triangle
        distinguished
        leftNull
        rightNull
        (TraceAnalyticStableNullObject.functor_isZero_of_closure
          functor
          zeroImage
          generatorImage
          shiftImage
          extensionImage
          triangle.obj₁
          leftNull)
        (TraceAnalyticStableNullObject.functor_isZero_of_closure
          functor
          zeroImage
          generatorImage
          shiftImage
          extensionImage
          triangle.obj₃
          rightNull)

/-- The same null-killing induction principle, stated through the triangulated
subcategory predicate. -/
theorem TraceAnalyticStableNullSubcategory.functor_isZero_of_closure
    {target : Type*} [CategoryTheory.Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
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
    (object : TraceAnalyticAdditiveHomotopyCategory)
    (null : TraceAnalyticStableNullSubcategory.P object) :
    IsZero (functor.obj object) :=
  TraceAnalyticStableNullObject.functor_isZero_of_closure
    functor
    zeroImage
    generatorImage
    shiftImage
    extensionImage
    object
    null

end AnalyticMotives
end LFunctions
end Boundary

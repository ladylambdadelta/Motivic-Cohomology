import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.Descent.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.NullSubcategory.Killing.InversionCriterion.Owner

/-!
# Geometric recognition functor inversion criterion

This file specializes the concrete stable-null closure criterion to
homotopy-level functors landing in the geometric Boundary-DMgm target.
-/

universe u

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

variable {k : Type u} [Field k] [PerfectField k]

variable (composition : Boundary.CanonicalCompositionData (k := k))
variable [FiniteCorrespondence.CanonicalExternalProductFamily (k := k)]
variable [Abelian (LinearPST (Boundary.canonicalCategory composition))]
variable [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
variable [Abelian (canonicalA1NisLocalization composition)]
variable [HasDerivedCategory (canonicalA1NisLocalization composition)]
variable [(canonicalA1NisLocalizationFunctor composition).Additive]
variable [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
variable [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]

variable (twistData :
  TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
    (composition := composition))

/-- A triangulated homotopy-level functor into the geometric Boundary-DMgm
target satisfying the stable-null closure criterion inverts the analytic
Verdier morphism class. -/
theorem TraceAnalyticMotiveRecognition.geometricHomotopyFunctor_inverts_of_closure
    [HasShift
      (TraceAnalyticDMgmComparisonTarget.geometricMotives
        (composition := composition) twistData) ℤ]
    [HasZeroObject
      (TraceAnalyticDMgmComparisonTarget.geometricMotives
        (composition := composition) twistData)]
    [Preadditive
      (TraceAnalyticDMgmComparisonTarget.geometricMotives
        (composition := composition) twistData)]
    [∀ degree : ℤ,
      (shiftFunctor
        (TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
        degree).Additive]
    [Pretriangulated
      (TraceAnalyticDMgmComparisonTarget.geometricMotives
        (composition := composition) twistData)]
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    [homotopyFunctor.CommShift ℤ]
    [homotopyFunctor.IsTriangulated]
    (zeroImage : IsZero (homotopyFunctor.obj 0))
    (generatorImage :
      ∀ generator : TraceAnalyticStableAcyclicGenerator,
        IsZero (homotopyFunctor.obj generator.object))
    (shiftImage :
      ∀ (object : TraceAnalyticAdditiveHomotopyCategory)
        (degree : ℤ),
        TraceAnalyticStableNullObject object →
        IsZero (homotopyFunctor.obj object) →
        IsZero (homotopyFunctor.obj (object⟦degree⟧)))
    (extensionImage :
      ∀ triangle : Triangle TraceAnalyticAdditiveHomotopyCategory,
        triangle ∈ TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles →
        TraceAnalyticStableNullObject triangle.obj₁ →
        TraceAnalyticStableNullObject triangle.obj₃ →
        IsZero (homotopyFunctor.obj triangle.obj₁) →
        IsZero (homotopyFunctor.obj triangle.obj₃) →
        IsZero (homotopyFunctor.obj triangle.obj₂)) :
    TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
      homotopyFunctor :=
  TraceAnalyticStableNullSubcategory.functor_inverts_of_closure
    homotopyFunctor
    zeroImage
    generatorImage
    shiftImage
    extensionImage

/-- The descended geometric recognition functor constructed from a
homotopy-level functor and the concrete stable-null closure criterion. -/
def TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctorOfClosure
    [HasShift
      (TraceAnalyticDMgmComparisonTarget.geometricMotives
        (composition := composition) twistData) ℤ]
    [HasZeroObject
      (TraceAnalyticDMgmComparisonTarget.geometricMotives
        (composition := composition) twistData)]
    [Preadditive
      (TraceAnalyticDMgmComparisonTarget.geometricMotives
        (composition := composition) twistData)]
    [∀ degree : ℤ,
      (shiftFunctor
        (TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
        degree).Additive]
    [Pretriangulated
      (TraceAnalyticDMgmComparisonTarget.geometricMotives
        (composition := composition) twistData)]
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    [homotopyFunctor.CommShift ℤ]
    [homotopyFunctor.IsTriangulated]
    (zeroImage : IsZero (homotopyFunctor.obj 0))
    (generatorImage :
      ∀ generator : TraceAnalyticStableAcyclicGenerator,
        IsZero (homotopyFunctor.obj generator.object))
    (shiftImage :
      ∀ (object : TraceAnalyticAdditiveHomotopyCategory)
        (degree : ℤ),
        TraceAnalyticStableNullObject object →
        IsZero (homotopyFunctor.obj object) →
        IsZero (homotopyFunctor.obj (object⟦degree⟧)))
    (extensionImage :
      ∀ triangle : Triangle TraceAnalyticAdditiveHomotopyCategory,
        triangle ∈ TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles →
        TraceAnalyticStableNullObject triangle.obj₁ →
        TraceAnalyticStableNullObject triangle.obj₃ →
        IsZero (homotopyFunctor.obj triangle.obj₁) →
        IsZero (homotopyFunctor.obj triangle.obj₃) →
        IsZero (homotopyFunctor.obj triangle.obj₂)) :
    TraceAnalyticDMgmComparisonSource ⥤
      TraceAnalyticDMgmComparisonTarget.geometricMotives
        (composition := composition) twistData :=
  TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctor
    (composition := composition)
    twistData
    homotopyFunctor
    (TraceAnalyticMotiveRecognition.geometricHomotopyFunctor_inverts_of_closure
      (composition := composition)
      twistData
      homotopyFunctor
      zeroImage
      generatorImage
      shiftImage
      extensionImage)

/-- The closure-constructed descended geometric functor is the general
descended geometric functor applied to the closure-produced inversion proof. -/
theorem TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctorOfClosure_eq_descended
    [HasShift
      (TraceAnalyticDMgmComparisonTarget.geometricMotives
        (composition := composition) twistData) ℤ]
    [HasZeroObject
      (TraceAnalyticDMgmComparisonTarget.geometricMotives
        (composition := composition) twistData)]
    [Preadditive
      (TraceAnalyticDMgmComparisonTarget.geometricMotives
        (composition := composition) twistData)]
    [∀ degree : ℤ,
      (shiftFunctor
        (TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
        degree).Additive]
    [Pretriangulated
      (TraceAnalyticDMgmComparisonTarget.geometricMotives
        (composition := composition) twistData)]
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    [homotopyFunctor.CommShift ℤ]
    [homotopyFunctor.IsTriangulated]
    (zeroImage : IsZero (homotopyFunctor.obj 0))
    (generatorImage :
      ∀ generator : TraceAnalyticStableAcyclicGenerator,
        IsZero (homotopyFunctor.obj generator.object))
    (shiftImage :
      ∀ (object : TraceAnalyticAdditiveHomotopyCategory)
        (degree : ℤ),
        TraceAnalyticStableNullObject object →
        IsZero (homotopyFunctor.obj object) →
        IsZero (homotopyFunctor.obj (object⟦degree⟧)))
    (extensionImage :
      ∀ triangle : Triangle TraceAnalyticAdditiveHomotopyCategory,
        triangle ∈ TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles →
        TraceAnalyticStableNullObject triangle.obj₁ →
        TraceAnalyticStableNullObject triangle.obj₃ →
        IsZero (homotopyFunctor.obj triangle.obj₁) →
        IsZero (homotopyFunctor.obj triangle.obj₃) →
        IsZero (homotopyFunctor.obj triangle.obj₂)) :
    TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctorOfClosure
        (composition := composition)
        twistData
        homotopyFunctor
        zeroImage
        generatorImage
        shiftImage
        extensionImage =
      TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctor
        (composition := composition)
        twistData
        homotopyFunctor
        (TraceAnalyticMotiveRecognition.geometricHomotopyFunctor_inverts_of_closure
          (composition := composition)
          twistData
          homotopyFunctor
          zeroImage
          generatorImage
          shiftImage
          extensionImage) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.DMgmFunctor.Descent.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.NullSubcategory.Killing.InversionCriterion.Owner

/-!
# Recognition functor inversion criterion

This file packages the concrete null-killing closure criterion as the input
needed to descend a homotopy-level Boundary-DMgm functor to the stable
recognition functor.
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

/-- A triangulated homotopy-level functor satisfying the stable-null closure
criterion inverts the analytic Verdier morphism class. -/
theorem TraceAnalyticMotiveRecognition.homotopyFunctor_inverts_of_closure
    [HasShift (TraceAnalyticDMgmComparisonTarget (composition := composition)) ℤ]
    [HasZeroObject (TraceAnalyticDMgmComparisonTarget (composition := composition))]
    [Preadditive (TraceAnalyticDMgmComparisonTarget (composition := composition))]
    [∀ degree : ℤ,
      (shiftFunctor
        (TraceAnalyticDMgmComparisonTarget (composition := composition))
        degree).Additive]
    [Pretriangulated
      (TraceAnalyticDMgmComparisonTarget (composition := composition))]
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
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

/-- The descended recognition functor constructed from a homotopy-level functor
and the concrete stable-null closure criterion. -/
def TraceAnalyticMotiveRecognition.descendedDMgmFunctorOfClosure
    [HasShift (TraceAnalyticDMgmComparisonTarget (composition := composition)) ℤ]
    [HasZeroObject (TraceAnalyticDMgmComparisonTarget (composition := composition))]
    [Preadditive (TraceAnalyticDMgmComparisonTarget (composition := composition))]
    [∀ degree : ℤ,
      (shiftFunctor
        (TraceAnalyticDMgmComparisonTarget (composition := composition))
        degree).Additive]
    [Pretriangulated
      (TraceAnalyticDMgmComparisonTarget (composition := composition))]
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
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
      TraceAnalyticDMgmComparisonTarget (composition := composition) :=
  TraceAnalyticMotiveRecognition.descendedDMgmFunctor
    (composition := composition)
    homotopyFunctor
    (TraceAnalyticMotiveRecognition.homotopyFunctor_inverts_of_closure
      (composition := composition)
      homotopyFunctor
      zeroImage
      generatorImage
      shiftImage
      extensionImage)

/-- The closure-constructed descended functor is the general descended functor
applied to the closure-produced inversion proof. -/
theorem TraceAnalyticMotiveRecognition.descendedDMgmFunctorOfClosure_eq_descended
    [HasShift (TraceAnalyticDMgmComparisonTarget (composition := composition)) ℤ]
    [HasZeroObject (TraceAnalyticDMgmComparisonTarget (composition := composition))]
    [Preadditive (TraceAnalyticDMgmComparisonTarget (composition := composition))]
    [∀ degree : ℤ,
      (shiftFunctor
        (TraceAnalyticDMgmComparisonTarget (composition := composition))
        degree).Additive]
    [Pretriangulated
      (TraceAnalyticDMgmComparisonTarget (composition := composition))]
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
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
    TraceAnalyticMotiveRecognition.descendedDMgmFunctorOfClosure
        (composition := composition)
        homotopyFunctor
        zeroImage
        generatorImage
        shiftImage
        extensionImage =
      TraceAnalyticMotiveRecognition.descendedDMgmFunctor
        (composition := composition)
        homotopyFunctor
        (TraceAnalyticMotiveRecognition.homotopyFunctor_inverts_of_closure
          (composition := composition)
          homotopyFunctor
          zeroImage
          generatorImage
          shiftImage
          extensionImage) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

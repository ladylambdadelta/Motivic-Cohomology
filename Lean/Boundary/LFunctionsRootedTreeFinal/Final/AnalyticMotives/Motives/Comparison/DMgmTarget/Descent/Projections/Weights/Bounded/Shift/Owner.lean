import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Descent.Projections.Weights.Bounded.Owner

/-!
# Boundary DMgm descent projections for shifted bounded analytic weights

This file specializes descent projection formulas to stable comparison-source
objects and maps represented by shifted bounded analytic complexes.
-/

universe u

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

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

/-- Object projection for a descended Boundary-DMgm comparison functor on a
stable shifted bounded analytic complex. -/
def TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorShiftedBoundedObjectIso
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
      (composition := composition)
      functor
      inverts).obj
        (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
          complex
          degree) ≅
      functor.obj
        (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyObject
          complex
          degree) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
    (composition := composition)
    functor
    inverts
    (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyObject
      complex
      degree)

/-- The shifted bounded object projection is the general quotient-object
projection at the shifted bounded homotopy representative. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorShiftedBoundedObjectIso_eq
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorShiftedBoundedObjectIso
        (composition := composition)
        functor
        inverts
        complex
        degree =
      TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition)
        functor
        inverts
        (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyObject
          complex
          degree) :=
  rfl

/-- Morphism projection for a descended Boundary-DMgm comparison functor on a
stable shifted map represented by a bounded analytic chain map. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_shiftedBoundedMap_naturality
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target)
    (degree : ℤ) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
      (composition := composition)
      functor
      inverts).map
        (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedMap
          hom
          degree) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorShiftedBoundedObjectIso
        (composition := composition)
        functor
        inverts
        target
        degree).hom =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorShiftedBoundedObjectIso
        (composition := composition)
        functor
        inverts
        source
        degree).hom ≫
        functor.map
          (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyMap
            hom
            degree) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_mapOf_naturality
    (composition := composition)
    functor
    inverts
    (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyMap
      hom
      degree)

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Geometric.Descent.Projections.Weights.Bounded.Owner

/-!
# Geometric Boundary DMgm descent projections for shifted bounded weights

This file specializes geometric Boundary-DMgm descent projection formulas to
stable shifted bounded analytic complexes and shifted bounded chain maps.
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

variable (twistData :
  TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
    (composition := composition))

/-- Object projection for a descended geometric Boundary-DMgm comparison
functor on a stable shifted bounded analytic complex. -/
def TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorShiftedBoundedObjectIso
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
      (composition := composition)
      twistData
      functor
      inverts).obj
        (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
          complex
          degree) ≅
      functor.obj
        (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyObject
          complex
          degree) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorObjectIso
    (composition := composition)
    twistData
    functor
    inverts
    (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyObject
      complex
      degree)

/-- The geometric shifted bounded object projection is the general
quotient-object projection at the shifted bounded homotopy representative. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorShiftedBoundedObjectIso_eq
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorShiftedBoundedObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        complex
        degree =
      TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyObject
          complex
          degree) :=
  rfl

/-- Morphism projection for a descended geometric Boundary-DMgm comparison
functor on a stable shifted map represented by a bounded analytic chain map. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor_shiftedBoundedMap_naturality
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
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
    (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
      (composition := composition)
      twistData
      functor
      inverts).map
        (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedMap
          hom
          degree) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorShiftedBoundedObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        target
        degree).hom =
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorShiftedBoundedObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        source
        degree).hom ≫
        functor.map
          (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyMap
            hom
            degree) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor_mapOf_naturality
    (composition := composition)
    twistData
    functor
    inverts
    (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyMap
      hom
      degree)

end AnalyticMotives
end LFunctions
end Boundary

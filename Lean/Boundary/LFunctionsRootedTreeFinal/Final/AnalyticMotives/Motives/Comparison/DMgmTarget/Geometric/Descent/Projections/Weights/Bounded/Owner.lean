import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Geometric.Descent.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Weights.Source.Bounds.Stable.Owner

/-!
# Geometric Boundary DMgm descent projections for bounded weights

This file specializes geometric Boundary-DMgm descent projection formulas to
stable comparison-source objects and maps represented by bounded analytic
complexes.
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
functor on a stable bounded analytic complex. -/
def TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorBoundedObjectIso
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
      (composition := composition)
      twistData
      functor
      inverts).obj
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject
          complex) ≅
      functor.obj
        (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyObject
          complex) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorObjectIso
    (composition := composition)
    twistData
    functor
    inverts
    (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyObject
      complex)

/-- The geometric bounded object projection is the general quotient-object
projection at the bounded homotopy representative. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorBoundedObjectIso_eq
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorBoundedObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        complex =
      TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyObject
          complex) :=
  rfl

/-- Morphism projection for a descended geometric Boundary-DMgm comparison
functor on a stable map represented by a bounded analytic chain map. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor_boundedMap_naturality
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
        target) :
    (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
      (composition := composition)
      twistData
      functor
      inverts).map
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorBoundedObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        target).hom =
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorBoundedObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        source).hom ≫
        functor.map
          (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyMap hom) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor_mapOf_naturality
    (composition := composition)
    twistData
    functor
    inverts
    (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyMap hom)

end AnalyticMotives
end LFunctions
end Boundary

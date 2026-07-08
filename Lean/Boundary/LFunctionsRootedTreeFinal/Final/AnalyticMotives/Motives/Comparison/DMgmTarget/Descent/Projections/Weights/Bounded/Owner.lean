import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Descent.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Weights.Source.Bounds.Stable.Owner

/-!
# Boundary DMgm descent projections for bounded analytic weights

This file specializes the general descent projection formulas to stable
comparison-source objects and maps represented by bounded analytic complexes.
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
stable bounded analytic complex. -/
def TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorBoundedObjectIso
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
      (composition := composition)
      functor
      inverts).obj
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject
          complex) ≅
      functor.obj
        (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyObject
          complex) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
    (composition := composition)
    functor
    inverts
    (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyObject
      complex)

/-- The bounded object projection is the general quotient-object projection at
the bounded homotopy representative. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorBoundedObjectIso_eq
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorBoundedObjectIso
        (composition := composition)
        functor
        inverts
        complex =
      TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition)
        functor
        inverts
        (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyObject
          complex) :=
  rfl

/-- Morphism projection for a descended Boundary-DMgm comparison functor on a
stable map represented by a bounded analytic chain map. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_boundedMap_naturality
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
        target) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
      (composition := composition)
      functor
      inverts).map
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorBoundedObjectIso
        (composition := composition)
        functor
        inverts
        target).hom =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorBoundedObjectIso
        (composition := composition)
        functor
        inverts
        source).hom ≫
        functor.map
          (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyMap hom) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_mapOf_naturality
    (composition := composition)
    functor
    inverts
    (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyMap hom)

end AnalyticMotives
end LFunctions
end Boundary

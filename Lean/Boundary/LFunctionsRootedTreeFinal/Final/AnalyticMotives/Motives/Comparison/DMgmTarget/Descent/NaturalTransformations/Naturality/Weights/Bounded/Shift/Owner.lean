import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Descent.NaturalTransformations.Naturality.Weights.Bounded.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Weights.Source.Bounds.Stable.Owner

/-!
# Boundary DMgm descended naturality for shifted bounded weights

This file specializes descended-natural-transformation naturality to stable
shifted bounded analytic chain maps.
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

/-- Naturality of a Boundary-DMgm descended natural transformation on a stable
shifted bounded analytic chain map. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_shiftedBoundedMap_naturality
    (first second :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (firstInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        first)
    (secondInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        second)
    (transformation : first ⟶ second)
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target)
    (degree : ℤ) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
      (composition := composition)
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
          source
          degree) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
        (composition := composition)
        second
        secondInverts).map
          (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedMap
            hom
            degree) =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
        (composition := composition)
        first
        firstInverts).map
          (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedMap
            hom
            degree) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
        (composition := composition)
        first
        second
        firstInverts
        secondInverts
        transformation).app
          (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
            target
            degree) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_mapOf_naturality
    (composition := composition)
    first
    second
    firstInverts
    secondInverts
    transformation
    (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyMap
      hom
      degree)

end AnalyticMotives
end LFunctions
end Boundary

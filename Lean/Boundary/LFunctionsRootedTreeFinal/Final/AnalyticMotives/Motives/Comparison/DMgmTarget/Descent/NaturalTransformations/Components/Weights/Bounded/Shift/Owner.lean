import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Descent.NaturalTransformations.Components.Weights.Bounded.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Descent.Projections.Weights.Bounded.Shift.Owner

/-!
# Components of descended transformations on shifted bounded weights

This file specializes descended-natural-transformation component formulas to
stable shifted bounded analytic complexes.
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

/-- At a stable shifted bounded analytic object, a Boundary-DMgm descended
natural transformation is the original transformation conjugated by the shifted
bounded descent factorization isomorphisms. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_app_shiftedBoundedObject
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
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
      (composition := composition)
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
          complex
          degree) =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorShiftedBoundedObjectIso
        (composition := composition)
        first
        firstInverts
        complex
        degree).hom ≫
      transformation.app
        (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyObject
          complex
          degree) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorShiftedBoundedObjectIso
        (composition := composition)
        second
        secondInverts
        complex
        degree).inv :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_app_objectOf
    (composition := composition)
    first
    second
    firstInverts
    secondInverts
    transformation
    (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyObject
      complex
      degree)

end AnalyticMotives
end LFunctions
end Boundary

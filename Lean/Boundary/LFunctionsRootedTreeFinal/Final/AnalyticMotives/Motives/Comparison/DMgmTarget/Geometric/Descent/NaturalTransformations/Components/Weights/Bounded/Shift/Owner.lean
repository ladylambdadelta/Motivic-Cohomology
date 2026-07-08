import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Geometric.Descent.NaturalTransformations.Components.Weights.Bounded.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Geometric.Descent.Projections.Weights.Bounded.Shift.Owner

/-!
# Components of geometric descended transformations on shifted bounded weights

This file specializes geometric descended-natural-transformation component
formulas to stable shifted bounded analytic complexes.
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

/-- At a stable shifted bounded analytic object, a geometric Boundary-DMgm
descended natural transformation is the original transformation conjugated by
the shifted bounded descent factorization isomorphisms. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_app_shiftedBoundedObject
    (first second :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
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
    (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans
      (composition := composition)
      twistData
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
          complex
          degree) =
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorShiftedBoundedObjectIso
        (composition := composition)
        twistData
        first
        firstInverts
        complex
        degree).hom ≫
      transformation.app
        (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyObject
          complex
          degree) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorShiftedBoundedObjectIso
        (composition := composition)
        twistData
        second
        secondInverts
        complex
        degree).inv :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_app_objectOf
    (composition := composition)
    twistData
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

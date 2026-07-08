import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Geometric.Descent.NaturalTransformations.Components.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Geometric.Descent.Projections.Weights.Bounded.Owner

/-!
# Components of geometric descended transformations on bounded weights

This file specializes the represented-object component formula for geometric
Boundary-DMgm descended natural transformations to stable bounded analytic
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

/-- At a stable bounded analytic object, a geometric Boundary-DMgm descended
natural transformation is the original transformation conjugated by the bounded
descent factorization isomorphisms. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_app_boundedObject
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
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans
      (composition := composition)
      twistData
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject
          complex) =
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorBoundedObjectIso
        (composition := composition)
        twistData
        first
        firstInverts
        complex).hom ≫
      transformation.app
        (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyObject
          complex) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorBoundedObjectIso
        (composition := composition)
        twistData
        second
        secondInverts
        complex).inv :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_app_objectOf
    (composition := composition)
    twistData
    first
    second
    firstInverts
    secondInverts
    transformation
    (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyObject complex)

end AnalyticMotives
end LFunctions
end Boundary

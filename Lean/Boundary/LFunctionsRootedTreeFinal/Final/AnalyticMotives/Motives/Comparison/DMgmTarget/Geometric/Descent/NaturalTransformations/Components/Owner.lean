import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Geometric.Descent.NaturalTransformations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Geometric.Descent.Projections.Owner

/-!
# Components of geometric Boundary DMgm descended natural transformations

This file records the component formula for natural transformations descended
to the geometric Boundary DMgm target.
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

/-- At a quotient-represented analytic object, a geometric Boundary-DMgm
descended natural transformation is the original natural transformation
conjugated by the two descent factorization isomorphisms. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_app_objectOf
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
    (object : TraceAnalyticAdditiveHomotopyCategory) :
    (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans
      (composition := composition)
      twistData
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticStableHomotopyComparisonSource.objectOf object) =
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorObjectIso
        (composition := composition)
        twistData
        first
        firstInverts
        object).hom ≫
      transformation.app object ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorObjectIso
        (composition := composition)
        twistData
        second
        secondInverts
        object).inv :=
  CategoryTheory.Localization.liftNatTrans_app
    TraceAnalyticStableHomotopyComparisonSource.quotientFunctor
    TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms
    first
    second
    (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
      (composition := composition)
      twistData
      first
      firstInverts)
    (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
      (composition := composition)
      twistData
      second
      secondInverts)
    transformation
    object

end AnalyticMotives
end LFunctions
end Boundary

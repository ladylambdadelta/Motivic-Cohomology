import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Descent.NaturalTransformations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Descent.Projections.Owner

/-!
# Components of Boundary DMgm descended natural transformations

This file records the component formula for natural transformations descended
to the concrete Boundary `DM_gm(Q)_Q` target.
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

/-- At a quotient-represented analytic object, a Boundary-DMgm descended natural
transformation is the original natural transformation conjugated by the two
descent factorization isomorphisms. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_app_objectOf
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
    (object : TraceAnalyticAdditiveHomotopyCategory) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
      (composition := composition)
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticStableHomotopyComparisonSource.objectOf object) =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition)
        first
        firstInverts
        object).hom ≫
      transformation.app object ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition)
        second
        secondInverts
        object).inv :=
  CategoryTheory.Localization.liftNatTrans_app
    TraceAnalyticStableHomotopyComparisonSource.quotientFunctor
    TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms
    first
    second
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
      (composition := composition)
      first
      firstInverts)
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
      (composition := composition)
      second
      secondInverts)
    transformation
    object

end AnalyticMotives
end LFunctions
end Boundary

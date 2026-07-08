import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Descent.NaturalTransformations.Owner

/-!
# Naturality of Boundary DMgm descended natural transformations

This file records the naturality square for natural transformations descended
to the concrete Boundary `DM_gm(Q)_Q` target, evaluated on morphisms represented
by the additive analytic homotopy category.
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

/-- Naturality of a Boundary-DMgm descended natural transformation on a
represented stable analytic morphism. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_mapOf_naturality
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
    {source targetObject : TraceAnalyticAdditiveHomotopyCategory}
    (hom : source ⟶ targetObject) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
      (composition := composition)
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticStableHomotopyComparisonSource.objectOf source) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
        (composition := composition)
        second
        secondInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf hom) =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
        (composition := composition)
        first
        firstInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf hom) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
        (composition := composition)
        first
        second
        firstInverts
        secondInverts
        transformation).app
          (TraceAnalyticStableHomotopyComparisonSource.objectOf targetObject) :=
  (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
    (composition := composition)
    first
    second
    firstInverts
    secondInverts
    transformation).naturality
      (TraceAnalyticStableHomotopyComparisonSource.mapOf hom)

end AnalyticMotives
end LFunctions
end Boundary

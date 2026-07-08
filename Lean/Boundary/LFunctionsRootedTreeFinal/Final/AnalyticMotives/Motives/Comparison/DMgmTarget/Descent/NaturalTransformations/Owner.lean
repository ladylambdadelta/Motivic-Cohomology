import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Descent.Owner

/-!
# Natural transformations after Boundary DMgm descent

This file specializes natural-transformation descent across the stable homotopy
comparison source to the concrete Boundary `DM_gm(Q)_Q` comparison target.
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

/-- A natural transformation between two null-inverting additive-homotopy
functors descends to a natural transformation between their Boundary-DMgm
comparison descents. -/
def TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
    (first second :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (firstInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        first)
    (secondInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        second)
    (transformation : first ⟶ second) :
    TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
      (composition := composition)
      first
      firstInverts ⟶
    TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
      (composition := composition)
      second
      secondInverts :=
  TraceAnalyticStableHomotopyComparisonSource.liftNatTrans
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

/-- The descended Boundary-DMgm natural transformation is the stable homotopy
comparison lifted natural transformation. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_eq_liftNatTrans
    (first second :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (firstInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        first)
    (secondInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        second)
    (transformation : first ⟶ second) :
    TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
      (composition := composition)
      first
      second
      firstInverts
      secondInverts
      transformation =
    TraceAnalyticStableHomotopyComparisonSource.liftNatTrans
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
      transformation :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

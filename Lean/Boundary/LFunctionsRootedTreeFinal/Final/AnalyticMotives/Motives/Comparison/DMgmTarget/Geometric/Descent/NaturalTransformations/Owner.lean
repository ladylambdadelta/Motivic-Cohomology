import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Geometric.Descent.Owner

/-!
# Natural transformations after geometric Boundary DMgm descent

This file specializes natural-transformation descent across the stable homotopy
comparison source to functors landing in the geometric Boundary DMgm target.
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

/-- A natural transformation between two null-inverting additive-homotopy
functors descends to a natural transformation between their geometric
Boundary-DMgm comparison descents. -/
def TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans
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
    (transformation : first ⟶ second) :
    TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
      (composition := composition)
      twistData
      first
      firstInverts ⟶
    TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
      (composition := composition)
      twistData
      second
      secondInverts :=
  TraceAnalyticStableHomotopyComparisonSource.liftNatTrans
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

/-- The descended geometric Boundary-DMgm natural transformation is the stable
homotopy comparison lifted natural transformation. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_eq_liftNatTrans
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
    (transformation : first ⟶ second) :
    TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans
      (composition := composition)
      twistData
      first
      second
      firstInverts
      secondInverts
      transformation =
    TraceAnalyticStableHomotopyComparisonSource.liftNatTrans
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
      transformation :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

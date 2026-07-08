import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Endpoints.Descent.Owner

/-!
# Descent endpoint natural transformations

This file exposes descended natural transformations for concrete and geometric
Boundary DMgm endpoint descents under comparison-facing names.
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

/-- Endpoint descended natural transformation between concrete Boundary-DMgm
descended functors. -/
def TraceAnalyticMotiveComparison.concreteTarget_descendInvertingFunctorNatTrans
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
    TraceAnalyticMotiveComparison.concreteTarget_descendInvertingFunctor
      (composition := composition)
      first
      firstInverts ⟶
    TraceAnalyticMotiveComparison.concreteTarget_descendInvertingFunctor
      (composition := composition)
      second
      secondInverts :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
    (composition := composition)
    first
    second
    firstInverts
    secondInverts
    transformation

/-- Concrete endpoint descended natural transformations are stable homotopy
comparison lifted natural transformations. -/
theorem TraceAnalyticMotiveComparison.concreteTarget_descendInvertingFunctorNatTrans_eq_liftNatTrans
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
    TraceAnalyticMotiveComparison.concreteTarget_descendInvertingFunctorNatTrans
        (composition := composition)
        first
        second
        firstInverts
        secondInverts
        transformation =
      TraceAnalyticStableHomotopyComparisonSource.liftNatTrans
        first
        second
        (TraceAnalyticMotiveComparison.concreteTarget_descendInvertingFunctor
          (composition := composition)
          first
          firstInverts)
        (TraceAnalyticMotiveComparison.concreteTarget_descendInvertingFunctor
          (composition := composition)
          second
          secondInverts)
        transformation :=
  rfl

/-- Endpoint descended natural transformation between geometric Boundary-DMgm
descended functors. -/
def TraceAnalyticMotiveComparison.geometricTarget_descendInvertingFunctorNatTrans
    (twistData :
      TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
        (composition := composition))
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
    TraceAnalyticMotiveComparison.geometricTarget_descendInvertingFunctor
      (composition := composition)
      twistData
      first
      firstInverts ⟶
    TraceAnalyticMotiveComparison.geometricTarget_descendInvertingFunctor
      (composition := composition)
      twistData
      second
      secondInverts :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans
    (composition := composition)
    twistData
    first
    second
    firstInverts
    secondInverts
    transformation

/-- Geometric endpoint descended natural transformations are stable homotopy
comparison lifted natural transformations. -/
theorem TraceAnalyticMotiveComparison.geometricTarget_descendInvertingFunctorNatTrans_eq_liftNatTrans
    (twistData :
      TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
        (composition := composition))
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
    TraceAnalyticMotiveComparison.geometricTarget_descendInvertingFunctorNatTrans
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
        (TraceAnalyticMotiveComparison.geometricTarget_descendInvertingFunctor
          (composition := composition)
          twistData
          first
          firstInverts)
        (TraceAnalyticMotiveComparison.geometricTarget_descendInvertingFunctor
          (composition := composition)
          twistData
          second
          secondInverts)
        transformation :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Geometric.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableHomotopyCategory.Owner

/-!
# Descent of comparison functors to the geometric Boundary DMgm target

This file specializes the Verdier localization universal property to functors
landing in the geometric Boundary motive target exposed by the analytic
comparison lane.
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

/-- A null-inverting additive-homotopy functor descends to the stable analytic
comparison source with values in the geometric Boundary DMgm target. -/
def TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor) :
    TraceAnalyticDMgmComparisonSource ⥤
      TraceAnalyticDMgmComparisonTarget.geometricMotives
        (composition := composition) twistData :=
  TraceAnalyticStableHomotopyComparisonSource.lift
    functor
    inverts

/-- The descended geometric Boundary-DMgm comparison functor factors the
original additive-homotopy functor through the stable analytic quotient. -/
def TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorFac
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor) :
    TraceAnalyticStableHomotopyComparisonSource.quotientFunctor ⋙
      TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
        (composition := composition)
        twistData
        functor
        inverts ≅
      functor :=
  TraceAnalyticStableHomotopyComparisonSource.liftFac
    functor
    inverts

/-- The descended geometric Boundary-DMgm comparison functor is the specialized
Verdier localization lift. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor_eq_lift
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor) :
    TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
        (composition := composition)
        twistData
        functor
        inverts =
      TraceAnalyticStableHomotopyComparisonSource.lift
        functor
        inverts :=
  rfl

/-- The geometric Boundary-DMgm comparison factorization is the specialized
Verdier localization factorization. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorFac_eq_liftFac
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor) :
    TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorFac
        (composition := composition)
        twistData
        functor
        inverts =
      TraceAnalyticStableHomotopyComparisonSource.liftFac
        functor
        inverts :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

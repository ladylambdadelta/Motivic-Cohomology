import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableHomotopyCategory.Owner

/-!
# Descent of comparison functors to the Boundary DMgm target

This file specializes the Verdier localization universal property to the
concrete Boundary `DM_gm(Q)_Q` target.  A functor from additive analytic
homotopy motives into the Boundary target descends to stable analytic motives
once it inverts the analytic null morphisms.
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

/-- A null-inverting additive-homotopy functor descends to the stable analytic
comparison source with values in the concrete Boundary DMgm target. -/
def TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor) :
    TraceAnalyticDMgmComparisonSource ⥤
      TraceAnalyticDMgmComparisonTarget (composition := composition) :=
  TraceAnalyticStableHomotopyComparisonSource.lift
    functor
    inverts

/-- The descended Boundary-DMgm comparison functor factors the original
additive-homotopy functor through the stable analytic quotient. -/
def TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorFac
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor) :
    TraceAnalyticStableHomotopyComparisonSource.quotientFunctor ⋙
      TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
        (composition := composition)
        functor
        inverts ≅
      functor :=
  TraceAnalyticStableHomotopyComparisonSource.liftFac
    functor
    inverts

/-- The descended Boundary-DMgm comparison functor is the specialized Verdier
localization lift. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_eq_lift
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor) :
    TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
        (composition := composition)
        functor
        inverts =
      TraceAnalyticStableHomotopyComparisonSource.lift
        functor
        inverts :=
  rfl

/-- The Boundary-DMgm comparison factorization is the specialized Verdier
localization factorization. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorFac_eq_liftFac
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor) :
    TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorFac
        (composition := composition)
        functor
        inverts =
      TraceAnalyticStableHomotopyComparisonSource.liftFac
        functor
        inverts :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

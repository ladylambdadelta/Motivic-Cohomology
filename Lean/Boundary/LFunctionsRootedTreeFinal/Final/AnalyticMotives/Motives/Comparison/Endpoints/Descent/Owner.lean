import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Summary.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Descent.Summary.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Geometric.Descent.Summary.Owner

/-!
# Descent endpoint functors

This file exposes the concrete and geometric Boundary DMgm descended functors
and their factorization isomorphisms under comparison-facing names.
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

/-- Endpoint descended functor from the stable analytic comparison source to
the concrete Boundary DMgm target. -/
def TraceAnalyticMotiveComparison.concreteTarget_descendInvertingFunctor
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor) :
    TraceAnalyticDMgmComparisonSource ⥤
      TraceAnalyticDMgmComparisonTarget (composition := composition) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
    (composition := composition)
    functor
    inverts

/-- Endpoint factorization isomorphism for concrete Boundary DMgm descent. -/
def TraceAnalyticMotiveComparison.concreteTarget_descendInvertingFunctorFac
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor) :
    TraceAnalyticStableHomotopyComparisonSource.quotientFunctor ⋙
      TraceAnalyticMotiveComparison.concreteTarget_descendInvertingFunctor
        (composition := composition)
        functor
        inverts ≅
      functor :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorFac
    (composition := composition)
    functor
    inverts

/-- Concrete Boundary DMgm endpoint descent is the stable Verdier lift. -/
theorem TraceAnalyticMotiveComparison.concreteTarget_descendInvertingFunctor_eq_lift
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor) :
    TraceAnalyticMotiveComparison.concreteTarget_descendInvertingFunctor
        (composition := composition)
        functor
        inverts =
      TraceAnalyticStableHomotopyComparisonSource.lift
        functor
        inverts :=
  rfl

/-- Concrete Boundary DMgm endpoint factorization is the stable Verdier
factorization. -/
theorem TraceAnalyticMotiveComparison.concreteTarget_descendInvertingFunctorFac_eq_liftFac
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor) :
    TraceAnalyticMotiveComparison.concreteTarget_descendInvertingFunctorFac
        (composition := composition)
        functor
        inverts =
      TraceAnalyticStableHomotopyComparisonSource.liftFac
        functor
        inverts :=
  rfl

/-- Endpoint descended functor from the stable analytic comparison source to
the geometric Boundary DMgm target. -/
def TraceAnalyticMotiveComparison.geometricTarget_descendInvertingFunctor
    (twistData :
      TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
        (composition := composition))
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
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
    (composition := composition)
    twistData
    functor
    inverts

/-- Endpoint factorization isomorphism for geometric Boundary DMgm descent. -/
def TraceAnalyticMotiveComparison.geometricTarget_descendInvertingFunctorFac
    (twistData :
      TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
        (composition := composition))
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor) :
    TraceAnalyticStableHomotopyComparisonSource.quotientFunctor ⋙
      TraceAnalyticMotiveComparison.geometricTarget_descendInvertingFunctor
        (composition := composition)
        twistData
        functor
        inverts ≅
      functor :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorFac
    (composition := composition)
    twistData
    functor
    inverts

/-- Geometric Boundary DMgm endpoint descent is the stable Verdier lift. -/
theorem TraceAnalyticMotiveComparison.geometricTarget_descendInvertingFunctor_eq_lift
    (twistData :
      TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
        (composition := composition))
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor) :
    TraceAnalyticMotiveComparison.geometricTarget_descendInvertingFunctor
        (composition := composition)
        twistData
        functor
        inverts =
      TraceAnalyticStableHomotopyComparisonSource.lift
        functor
        inverts :=
  rfl

/-- Geometric Boundary DMgm endpoint factorization is the stable Verdier
factorization. -/
theorem TraceAnalyticMotiveComparison.geometricTarget_descendInvertingFunctorFac_eq_liftFac
    (twistData :
      TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
        (composition := composition))
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor) :
    TraceAnalyticMotiveComparison.geometricTarget_descendInvertingFunctorFac
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

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Descent.Projections.Owner

/-!
# Generator projection formulas for Boundary DMgm descent

This file specializes the Boundary-DMgm descent projection formula to the three
morphisms in every stable analytic acyclic generator triangle.
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

/-- Boundary-DMgm descent projection formula for the first map of a stable
acyclic generator. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_generator_firstMap_naturality
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (generator : TraceAnalyticStableAcyclicGenerator) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
      (composition := composition)
      functor
      inverts).map
        (TraceAnalyticStableHomotopyComparisonSource.mapOf generator.firstMap) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition)
        functor
        inverts
        generator.target).hom =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition)
        functor
        inverts
        generator.source).hom ≫
        functor.map generator.firstMap :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_mapOf_naturality
    (composition := composition)
    functor
    inverts
    generator.firstMap

/-- Boundary-DMgm descent projection formula for the cone map of a stable
acyclic generator. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_generator_coneMap_naturality
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (generator : TraceAnalyticStableAcyclicGenerator) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
      (composition := composition)
      functor
      inverts).map
        (TraceAnalyticStableHomotopyComparisonSource.mapOf generator.coneMap) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition)
        functor
        inverts
        generator.object).hom =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition)
        functor
        inverts
        generator.target).hom ≫
        functor.map generator.coneMap :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_mapOf_naturality
    (composition := composition)
    functor
    inverts
    generator.coneMap

/-- Boundary-DMgm descent projection formula for the connecting map of a stable
acyclic generator. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_generator_connectingMap_naturality
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (generator : TraceAnalyticStableAcyclicGenerator) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
      (composition := composition)
      functor
      inverts).map
        (TraceAnalyticStableHomotopyComparisonSource.mapOf generator.connectingMap) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition)
        functor
        inverts
        generator.source⟦(1 : ℤ)⟧).hom =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition)
        functor
        inverts
        generator.object).hom ≫
        functor.map generator.connectingMap :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_mapOf_naturality
    (composition := composition)
    functor
    inverts
    generator.connectingMap

end AnalyticMotives
end LFunctions
end Boundary

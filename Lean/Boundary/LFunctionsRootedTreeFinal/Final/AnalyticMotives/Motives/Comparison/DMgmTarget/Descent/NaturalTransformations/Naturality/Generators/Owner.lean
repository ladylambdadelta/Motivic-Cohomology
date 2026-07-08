import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Descent.NaturalTransformations.Naturality.Owner

/-!
# Generator naturality for Boundary DMgm descended transformations

This file specializes represented-morphism naturality of descended natural
transformations to the three maps in every stable analytic acyclic generator
triangle.
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

/-- Naturality of a Boundary-DMgm descended natural transformation on the first
map of a stable acyclic generator. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_generator_firstMap_naturality
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
    (generator : TraceAnalyticStableAcyclicGenerator) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
      (composition := composition)
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticStableHomotopyComparisonSource.objectOf generator.source) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
        (composition := composition)
        second
        secondInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf generator.firstMap) =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
        (composition := composition)
        first
        firstInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf generator.firstMap) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
        (composition := composition)
        first
        second
        firstInverts
        secondInverts
        transformation).app
          (TraceAnalyticStableHomotopyComparisonSource.objectOf generator.target) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_mapOf_naturality
    (composition := composition)
    first
    second
    firstInverts
    secondInverts
    transformation
    generator.firstMap

/-- Naturality of a Boundary-DMgm descended natural transformation on the cone
map of a stable acyclic generator. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_generator_coneMap_naturality
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
    (generator : TraceAnalyticStableAcyclicGenerator) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
      (composition := composition)
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticStableHomotopyComparisonSource.objectOf generator.target) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
        (composition := composition)
        second
        secondInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf generator.coneMap) =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
        (composition := composition)
        first
        firstInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf generator.coneMap) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
        (composition := composition)
        first
        second
        firstInverts
        secondInverts
        transformation).app
          (TraceAnalyticStableHomotopyComparisonSource.objectOf generator.object) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_mapOf_naturality
    (composition := composition)
    first
    second
    firstInverts
    secondInverts
    transformation
    generator.coneMap

/-- Naturality of a Boundary-DMgm descended natural transformation on the
connecting map of a stable acyclic generator. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_generator_connectingMap_naturality
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
    (generator : TraceAnalyticStableAcyclicGenerator) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
      (composition := composition)
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticStableHomotopyComparisonSource.objectOf generator.object) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
        (composition := composition)
        second
        secondInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf generator.connectingMap) =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
        (composition := composition)
        first
        firstInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf generator.connectingMap) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
        (composition := composition)
        first
        second
        firstInverts
        secondInverts
        transformation).app
          (TraceAnalyticStableHomotopyComparisonSource.objectOf
            (generator.source⟦(1 : ℤ)⟧)) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_mapOf_naturality
    (composition := composition)
    first
    second
    firstInverts
    secondInverts
    transformation
    generator.connectingMap

end AnalyticMotives
end LFunctions
end Boundary

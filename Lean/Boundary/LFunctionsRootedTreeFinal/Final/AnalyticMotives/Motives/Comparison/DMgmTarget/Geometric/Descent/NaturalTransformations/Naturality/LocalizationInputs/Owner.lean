import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Geometric.Descent.NaturalTransformations.Naturality.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.LocalizationInput.Owner

/-!
# Localization-input naturality for geometric Boundary DMgm descended transformations

This file specializes represented-morphism naturality of descended natural
transformations to stable maps attached to analytic localization inputs, for
functors landing in the geometric Boundary DMgm target.
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

/-- Naturality of a geometric Boundary-DMgm descended natural transformation on
an analytic localization-input stable map. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_localizationInput_stableMap_naturality
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
    (transformation : first ⟶ second)
    (input : TraceLocalizationInput) :
    (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans
      (composition := composition)
      twistData
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticStableHomotopyComparisonSource.objectOf input.stableSource) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
        (composition := composition)
        twistData
        second
        secondInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf input.stableMap) =
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
        (composition := composition)
        twistData
        first
        firstInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf input.stableMap) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans
        (composition := composition)
        twistData
        first
        second
        firstInverts
        secondInverts
        transformation).app
          (TraceAnalyticStableHomotopyComparisonSource.objectOf input.stableTarget) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_mapOf_naturality
    (composition := composition)
    twistData
    first
    second
    firstInverts
    secondInverts
    transformation
    input.stableMap

/-- Naturality on descent-channel localization-input stable maps in the
geometric Boundary-DMgm target. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_descentChannel_stableMap_naturality
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
    (transformation : first ⟶ second)
    (source target : QTraceExpression) :
    (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans
      (composition := composition)
      twistData
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticStableHomotopyComparisonSource.objectOf
          (TraceLocalizationInput.descentChannel source target).stableSource) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
        (composition := composition)
        twistData
        second
        secondInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceLocalizationInput.descentChannel source target).stableMap) =
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
        (composition := composition)
        twistData
        first
        firstInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceLocalizationInput.descentChannel source target).stableMap) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans
        (composition := composition)
        twistData
        first
        second
        firstInverts
        secondInverts
        transformation).app
          (TraceAnalyticStableHomotopyComparisonSource.objectOf
            (TraceLocalizationInput.descentChannel source target).stableTarget) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_localizationInput_stableMap_naturality
    (composition := composition)
    twistData
    first
    second
    firstInverts
    secondInverts
    transformation
    (TraceLocalizationInput.descentChannel source target)

/-- Naturality on descent-refinement localization-input stable maps in the
geometric Boundary-DMgm target. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_descentRefinement_stableMap_naturality
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
    (transformation : first ⟶ second)
    (source target : QTraceExpression) :
    (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans
      (composition := composition)
      twistData
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticStableHomotopyComparisonSource.objectOf
          (TraceLocalizationInput.descentRefinement source target).stableSource) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
        (composition := composition)
        twistData
        second
        secondInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceLocalizationInput.descentRefinement source target).stableMap) =
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
        (composition := composition)
        twistData
        first
        firstInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceLocalizationInput.descentRefinement source target).stableMap) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans
        (composition := composition)
        twistData
        first
        second
        firstInverts
        secondInverts
        transformation).app
          (TraceAnalyticStableHomotopyComparisonSource.objectOf
            (TraceLocalizationInput.descentRefinement source target).stableTarget) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_localizationInput_stableMap_naturality
    (composition := composition)
    twistData
    first
    second
    firstInverts
    secondInverts
    transformation
    (TraceLocalizationInput.descentRefinement source target)

/-- Naturality on descent-schedule localization-input stable maps in the
geometric Boundary-DMgm target. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_descentSchedule_stableMap_naturality
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
    (transformation : first ⟶ second)
    (source target : QTraceExpression) :
    (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans
      (composition := composition)
      twistData
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticStableHomotopyComparisonSource.objectOf
          (TraceLocalizationInput.descentSchedule source target).stableSource) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
        (composition := composition)
        twistData
        second
        secondInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceLocalizationInput.descentSchedule source target).stableMap) =
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
        (composition := composition)
        twistData
        first
        firstInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceLocalizationInput.descentSchedule source target).stableMap) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans
        (composition := composition)
        twistData
        first
        second
        firstInverts
        secondInverts
        transformation).app
          (TraceAnalyticStableHomotopyComparisonSource.objectOf
            (TraceLocalizationInput.descentSchedule source target).stableTarget) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_localizationInput_stableMap_naturality
    (composition := composition)
    twistData
    first
    second
    firstInverts
    secondInverts
    transformation
    (TraceLocalizationInput.descentSchedule source target)

/-- Naturality on interval-Stokes localization-input stable maps in the
geometric Boundary-DMgm target. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_intervalStokes_stableMap_naturality
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
    (transformation : first ⟶ second)
    (source target : QTraceExpression) :
    (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans
      (composition := composition)
      twistData
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticStableHomotopyComparisonSource.objectOf
          (TraceLocalizationInput.intervalStokes source target).stableSource) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
        (composition := composition)
        twistData
        second
        secondInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceLocalizationInput.intervalStokes source target).stableMap) =
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
        (composition := composition)
        twistData
        first
        firstInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceLocalizationInput.intervalStokes source target).stableMap) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans
        (composition := composition)
        twistData
        first
        second
        firstInverts
        secondInverts
        transformation).app
          (TraceAnalyticStableHomotopyComparisonSource.objectOf
            (TraceLocalizationInput.intervalStokes source target).stableTarget) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_localizationInput_stableMap_naturality
    (composition := composition)
    twistData
    first
    second
    firstInverts
    secondInverts
    transformation
    (TraceLocalizationInput.intervalStokes source target)

/-- Naturality on interval-Fubini localization-input stable maps in the
geometric Boundary-DMgm target. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_intervalFubini_stableMap_naturality
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
    (transformation : first ⟶ second)
    (source target : QTraceExpression) :
    (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans
      (composition := composition)
      twistData
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticStableHomotopyComparisonSource.objectOf
          (TraceLocalizationInput.intervalFubini source target).stableSource) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
        (composition := composition)
        twistData
        second
        secondInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceLocalizationInput.intervalFubini source target).stableMap) =
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
        (composition := composition)
        twistData
        first
        firstInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceLocalizationInput.intervalFubini source target).stableMap) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans
        (composition := composition)
        twistData
        first
        second
        firstInverts
        secondInverts
        transformation).app
          (TraceAnalyticStableHomotopyComparisonSource.objectOf
            (TraceLocalizationInput.intervalFubini source target).stableTarget) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_localizationInput_stableMap_naturality
    (composition := composition)
    twistData
    first
    second
    firstInverts
    secondInverts
    transformation
    (TraceLocalizationInput.intervalFubini source target)

/-- Naturality on Tate-weight-drop localization-input stable maps in the
geometric Boundary-DMgm target. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_tateWeightDrop_stableMap_naturality
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
    (transformation : first ⟶ second)
    (source target : QTraceExpression) :
    (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans
      (composition := composition)
      twistData
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticStableHomotopyComparisonSource.objectOf
          (TraceLocalizationInput.tateWeightDrop source target).stableSource) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
        (composition := composition)
        twistData
        second
        secondInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceLocalizationInput.tateWeightDrop source target).stableMap) =
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
        (composition := composition)
        twistData
        first
        firstInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceLocalizationInput.tateWeightDrop source target).stableMap) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans
        (composition := composition)
        twistData
        first
        second
        firstInverts
        secondInverts
        transformation).app
          (TraceAnalyticStableHomotopyComparisonSource.objectOf
            (TraceLocalizationInput.tateWeightDrop source target).stableTarget) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_localizationInput_stableMap_naturality
    (composition := composition)
    twistData
    first
    second
    firstInverts
    secondInverts
    transformation
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary

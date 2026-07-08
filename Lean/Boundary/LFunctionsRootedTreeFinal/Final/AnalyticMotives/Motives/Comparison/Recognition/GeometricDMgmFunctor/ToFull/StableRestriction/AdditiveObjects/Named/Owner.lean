import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.ToFull.StableRestriction.AdditiveObjects.Owner

/-!
# Named full-from-geometric additive-object restriction formulas

This file specializes the full-from-geometric additive finite-family
restriction formula to the seven named analytic rewrite generators.
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

/-- Descended full-from-geometric additive comparison naturality for Stokes. -/
theorem TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionObjectIso_stokes_naturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor
      (composition := composition)
      twistData
      homotopyFunctor
      inverts).map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
          (TraceRewriteGenerator.stokes source target)) ≫
      (TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        (TraceAnalyticMotiveComparison.sourceTraceAdditiveObject
          (TraceRewriteGenerator.stokes source target).targetObject)).hom =
      (TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        (TraceAnalyticMotiveComparison.sourceTraceAdditiveObject
          (TraceRewriteGenerator.stokes source target).sourceObject)).hom ≫
        (TraceAnalyticMotiveRecognition.fullFromGeometricAdditiveObjectRestrictionFunctor
          (composition := composition)
          twistData
          homotopyFunctor).map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
            (TraceRewriteGenerator.stokes source target)) :=
  TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionObjectIso_rewriteGenerator_naturality
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    (TraceRewriteGenerator.stokes source target)

/-- Descended full-from-geometric additive comparison naturality for residue. -/
theorem TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionObjectIso_residue_naturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor
      (composition := composition)
      twistData
      homotopyFunctor
      inverts).map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
          (TraceRewriteGenerator.residue source target)) ≫
      (TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        (TraceAnalyticMotiveComparison.sourceTraceAdditiveObject
          (TraceRewriteGenerator.residue source target).targetObject)).hom =
      (TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        (TraceAnalyticMotiveComparison.sourceTraceAdditiveObject
          (TraceRewriteGenerator.residue source target).sourceObject)).hom ≫
        (TraceAnalyticMotiveRecognition.fullFromGeometricAdditiveObjectRestrictionFunctor
          (composition := composition)
          twistData
          homotopyFunctor).map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
            (TraceRewriteGenerator.residue source target)) :=
  TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionObjectIso_rewriteGenerator_naturality
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    (TraceRewriteGenerator.residue source target)

/-- Descended full-from-geometric additive comparison naturality for channel. -/
theorem TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionObjectIso_channel_naturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor
      (composition := composition)
      twistData
      homotopyFunctor
      inverts).map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
          (TraceRewriteGenerator.channel source target)) ≫
      (TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        (TraceAnalyticMotiveComparison.sourceTraceAdditiveObject
          (TraceRewriteGenerator.channel source target).targetObject)).hom =
      (TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        (TraceAnalyticMotiveComparison.sourceTraceAdditiveObject
          (TraceRewriteGenerator.channel source target).sourceObject)).hom ≫
        (TraceAnalyticMotiveRecognition.fullFromGeometricAdditiveObjectRestrictionFunctor
          (composition := composition)
          twistData
          homotopyFunctor).map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
            (TraceRewriteGenerator.channel source target)) :=
  TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionObjectIso_rewriteGenerator_naturality
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    (TraceRewriteGenerator.channel source target)

/-- Descended full-from-geometric additive comparison naturality for refinement. -/
theorem TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionObjectIso_refinement_naturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor
      (composition := composition)
      twistData
      homotopyFunctor
      inverts).map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
          (TraceRewriteGenerator.refinement source target)) ≫
      (TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        (TraceAnalyticMotiveComparison.sourceTraceAdditiveObject
          (TraceRewriteGenerator.refinement source target).targetObject)).hom =
      (TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        (TraceAnalyticMotiveComparison.sourceTraceAdditiveObject
          (TraceRewriteGenerator.refinement source target).sourceObject)).hom ≫
        (TraceAnalyticMotiveRecognition.fullFromGeometricAdditiveObjectRestrictionFunctor
          (composition := composition)
          twistData
          homotopyFunctor).map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
            (TraceRewriteGenerator.refinement source target)) :=
  TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionObjectIso_rewriteGenerator_naturality
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    (TraceRewriteGenerator.refinement source target)

/-- Descended full-from-geometric additive comparison naturality for schedule. -/
theorem TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionObjectIso_schedule_naturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor
      (composition := composition)
      twistData
      homotopyFunctor
      inverts).map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
          (TraceRewriteGenerator.schedule source target)) ≫
      (TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        (TraceAnalyticMotiveComparison.sourceTraceAdditiveObject
          (TraceRewriteGenerator.schedule source target).targetObject)).hom =
      (TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        (TraceAnalyticMotiveComparison.sourceTraceAdditiveObject
          (TraceRewriteGenerator.schedule source target).sourceObject)).hom ≫
        (TraceAnalyticMotiveRecognition.fullFromGeometricAdditiveObjectRestrictionFunctor
          (composition := composition)
          twistData
          homotopyFunctor).map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
            (TraceRewriteGenerator.schedule source target)) :=
  TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionObjectIso_rewriteGenerator_naturality
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    (TraceRewriteGenerator.schedule source target)

/-- Descended full-from-geometric additive comparison naturality for weight-drop. -/
theorem TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionObjectIso_weightDrop_naturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor
      (composition := composition)
      twistData
      homotopyFunctor
      inverts).map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
          (TraceRewriteGenerator.weightDrop source target)) ≫
      (TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        (TraceAnalyticMotiveComparison.sourceTraceAdditiveObject
          (TraceRewriteGenerator.weightDrop source target).targetObject)).hom =
      (TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        (TraceAnalyticMotiveComparison.sourceTraceAdditiveObject
          (TraceRewriteGenerator.weightDrop source target).sourceObject)).hom ≫
        (TraceAnalyticMotiveRecognition.fullFromGeometricAdditiveObjectRestrictionFunctor
          (composition := composition)
          twistData
          homotopyFunctor).map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
            (TraceRewriteGenerator.weightDrop source target)) :=
  TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionObjectIso_rewriteGenerator_naturality
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    (TraceRewriteGenerator.weightDrop source target)

/-- Descended full-from-geometric additive comparison naturality for Fubini. -/
theorem TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionObjectIso_fubini_naturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor
      (composition := composition)
      twistData
      homotopyFunctor
      inverts).map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
          (TraceRewriteGenerator.fubini source target)) ≫
      (TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        (TraceAnalyticMotiveComparison.sourceTraceAdditiveObject
          (TraceRewriteGenerator.fubini source target).targetObject)).hom =
      (TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        (TraceAnalyticMotiveComparison.sourceTraceAdditiveObject
          (TraceRewriteGenerator.fubini source target).sourceObject)).hom ≫
        (TraceAnalyticMotiveRecognition.fullFromGeometricAdditiveObjectRestrictionFunctor
          (composition := composition)
          twistData
          homotopyFunctor).map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
            (TraceRewriteGenerator.fubini source target)) :=
  TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionObjectIso_rewriteGenerator_naturality
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    (TraceRewriteGenerator.fubini source target)

/-- Descended full-from-geometric additive restriction formula for Stokes. -/
theorem TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor_stokesMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor
        inverts).map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
          (TraceRewriteGenerator.stokes source target)) =
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition)
        twistData
        homotopyFunctor
        inverts).map
        (TraceAnalyticMotiveRecognition.stableAdditiveSourceFunctor.map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
            (TraceRewriteGenerator.stokes source target))) :=
  TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor_rewriteGeneratorMap
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    (TraceRewriteGenerator.stokes source target)

/-- Descended full-from-geometric additive restriction formula for residue. -/
theorem TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor_residueMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor
        inverts).map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
          (TraceRewriteGenerator.residue source target)) =
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition)
        twistData
        homotopyFunctor
        inverts).map
        (TraceAnalyticMotiveRecognition.stableAdditiveSourceFunctor.map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
            (TraceRewriteGenerator.residue source target))) :=
  TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor_rewriteGeneratorMap
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    (TraceRewriteGenerator.residue source target)

/-- Descended full-from-geometric additive restriction formula for channel. -/
theorem TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor_channelMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor
        inverts).map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
          (TraceRewriteGenerator.channel source target)) =
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition)
        twistData
        homotopyFunctor
        inverts).map
        (TraceAnalyticMotiveRecognition.stableAdditiveSourceFunctor.map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
            (TraceRewriteGenerator.channel source target))) :=
  TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor_rewriteGeneratorMap
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    (TraceRewriteGenerator.channel source target)

/-- Descended full-from-geometric additive restriction formula for refinement. -/
theorem TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor_refinementMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor
        inverts).map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
          (TraceRewriteGenerator.refinement source target)) =
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition)
        twistData
        homotopyFunctor
        inverts).map
        (TraceAnalyticMotiveRecognition.stableAdditiveSourceFunctor.map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
            (TraceRewriteGenerator.refinement source target))) :=
  TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor_rewriteGeneratorMap
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    (TraceRewriteGenerator.refinement source target)

/-- Descended full-from-geometric additive restriction formula for schedule. -/
theorem TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor_scheduleMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor
        inverts).map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
          (TraceRewriteGenerator.schedule source target)) =
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition)
        twistData
        homotopyFunctor
        inverts).map
        (TraceAnalyticMotiveRecognition.stableAdditiveSourceFunctor.map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
            (TraceRewriteGenerator.schedule source target))) :=
  TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor_rewriteGeneratorMap
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    (TraceRewriteGenerator.schedule source target)

/-- Descended full-from-geometric additive restriction formula for weight-drop. -/
theorem TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor_weightDropMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor
        inverts).map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
          (TraceRewriteGenerator.weightDrop source target)) =
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition)
        twistData
        homotopyFunctor
        inverts).map
        (TraceAnalyticMotiveRecognition.stableAdditiveSourceFunctor.map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
            (TraceRewriteGenerator.weightDrop source target))) :=
  TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor_rewriteGeneratorMap
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    (TraceRewriteGenerator.weightDrop source target)

/-- Descended full-from-geometric additive restriction formula for Fubini. -/
theorem TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor_fubiniMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor
        inverts).map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
          (TraceRewriteGenerator.fubini source target)) =
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition)
        twistData
        homotopyFunctor
        inverts).map
        (TraceAnalyticMotiveRecognition.stableAdditiveSourceFunctor.map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
            (TraceRewriteGenerator.fubini source target))) :=
  TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor_rewriteGeneratorMap
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    (TraceRewriteGenerator.fubini source target)

end AnalyticMotives
end LFunctions
end Boundary

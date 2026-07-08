import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.DMgmFunctor.Descent.Named.Owner

/-!
# Trace-object restriction of homotopy-level recognition functors

This file records the concrete trace-object functor obtained by restricting a
homotopy-level Boundary-DMgm functor along the existing trace-object homotopy
endpoint.
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

/-- The trace-object restriction of a homotopy-level recognition functor. -/
def TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition)) :
    TraceCorQObject ⥤
      TraceAnalyticDMgmComparisonTarget (composition := composition) :=
  TraceAnalyticMotiveComparison.sourceTraceHomotopyFunctor ⋙
    homotopyFunctor

/-- The trace-object restriction is homotopy endpoint followed by the supplied
homotopy-level functor. -/
theorem TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor_eq_comp
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition)) :
    TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor
        (composition := composition)
        homotopyFunctor =
      TraceAnalyticMotiveComparison.sourceTraceHomotopyFunctor ⋙
        homotopyFunctor :=
  rfl

/-- Object formula for the trace-object restriction of a homotopy-level
recognition functor. -/
theorem TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor_obj
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (object : TraceCorQObject) :
    (TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor
        (composition := composition)
        homotopyFunctor).obj object =
      homotopyFunctor.obj
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject object) :=
  rfl

/-- Map formula for the trace-object restriction of a homotopy-level
recognition functor. -/
theorem TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor_map
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    {source target : TraceCorQObject}
    (hom : source ⟶ target) :
    (TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor
        (composition := composition)
        homotopyFunctor).map hom =
      homotopyFunctor.map
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyMap hom) :=
  rfl

/-- The trace-object restriction sends a rewrite generator's certified trace
hom to the homotopy-level image of its recognition homotopy stage. -/
theorem TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor_rewriteGeneratorMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (generator : TraceRewriteGenerator) :
    (TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor
        (composition := composition)
        homotopyFunctor).map generator.traceHom =
      homotopyFunctor.map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
          generator) :=
  rfl

/-- Trace-object restriction formula for Stokes. -/
theorem TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor_stokesMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor
        (composition := composition)
        homotopyFunctor).map
        (TraceRewriteGenerator.stokes source target).traceHom =
      homotopyFunctor.map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
          (TraceRewriteGenerator.stokes source target)) :=
  TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor_rewriteGeneratorMap
    (composition := composition)
    homotopyFunctor
    (TraceRewriteGenerator.stokes source target)

/-- Trace-object restriction formula for residue. -/
theorem TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor_residueMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor
        (composition := composition)
        homotopyFunctor).map
        (TraceRewriteGenerator.residue source target).traceHom =
      homotopyFunctor.map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
          (TraceRewriteGenerator.residue source target)) :=
  TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor_rewriteGeneratorMap
    (composition := composition)
    homotopyFunctor
    (TraceRewriteGenerator.residue source target)

/-- Trace-object restriction formula for channel. -/
theorem TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor_channelMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor
        (composition := composition)
        homotopyFunctor).map
        (TraceRewriteGenerator.channel source target).traceHom =
      homotopyFunctor.map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
          (TraceRewriteGenerator.channel source target)) :=
  TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor_rewriteGeneratorMap
    (composition := composition)
    homotopyFunctor
    (TraceRewriteGenerator.channel source target)

/-- Trace-object restriction formula for refinement. -/
theorem TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor_refinementMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor
        (composition := composition)
        homotopyFunctor).map
        (TraceRewriteGenerator.refinement source target).traceHom =
      homotopyFunctor.map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
          (TraceRewriteGenerator.refinement source target)) :=
  TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor_rewriteGeneratorMap
    (composition := composition)
    homotopyFunctor
    (TraceRewriteGenerator.refinement source target)

/-- Trace-object restriction formula for schedule. -/
theorem TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor_scheduleMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor
        (composition := composition)
        homotopyFunctor).map
        (TraceRewriteGenerator.schedule source target).traceHom =
      homotopyFunctor.map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
          (TraceRewriteGenerator.schedule source target)) :=
  TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor_rewriteGeneratorMap
    (composition := composition)
    homotopyFunctor
    (TraceRewriteGenerator.schedule source target)

/-- Trace-object restriction formula for weight-drop. -/
theorem TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor_weightDropMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor
        (composition := composition)
        homotopyFunctor).map
        (TraceRewriteGenerator.weightDrop source target).traceHom =
      homotopyFunctor.map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
          (TraceRewriteGenerator.weightDrop source target)) :=
  TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor_rewriteGeneratorMap
    (composition := composition)
    homotopyFunctor
    (TraceRewriteGenerator.weightDrop source target)

/-- Trace-object restriction formula for Fubini. -/
theorem TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor_fubiniMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor
        (composition := composition)
        homotopyFunctor).map
        (TraceRewriteGenerator.fubini source target).traceHom =
      homotopyFunctor.map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
          (TraceRewriteGenerator.fubini source target)) :=
  TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor_rewriteGeneratorMap
    (composition := composition)
    homotopyFunctor
    (TraceRewriteGenerator.fubini source target)

end AnalyticMotives
end LFunctions
end Boundary

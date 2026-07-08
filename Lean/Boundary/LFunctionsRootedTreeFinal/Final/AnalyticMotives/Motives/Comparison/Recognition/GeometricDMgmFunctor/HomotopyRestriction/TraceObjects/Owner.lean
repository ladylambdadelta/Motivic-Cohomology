import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.Descent.Owner

/-!
# Trace-object restriction of geometric homotopy-level recognition functors

This file records the trace-object restriction obtained by composing the
existing source trace-homotopy endpoint with a homotopy-level functor landing
in the geometric Boundary-DMgm target.
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

/-- The trace-object restriction of a geometric homotopy-level recognition
functor. -/
def TraceAnalyticMotiveRecognition.geometricTraceObjectRestrictionFunctor
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData) :
    TraceCorQObject ⥤
      TraceAnalyticDMgmComparisonTarget.geometricMotives
        (composition := composition) twistData :=
  TraceAnalyticMotiveComparison.sourceTraceHomotopyFunctor ⋙
    homotopyFunctor

/-- Object formula for the geometric trace-object restriction. -/
theorem TraceAnalyticMotiveRecognition.geometricTraceObjectRestrictionFunctor_obj
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (object : TraceCorQObject) :
    (TraceAnalyticMotiveRecognition.geometricTraceObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).obj object =
      homotopyFunctor.obj
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject object) :=
  rfl

/-- Map formula for the geometric trace-object restriction. -/
theorem TraceAnalyticMotiveRecognition.geometricTraceObjectRestrictionFunctor_map
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    {source target : TraceCorQObject}
    (hom : source ⟶ target) :
    (TraceAnalyticMotiveRecognition.geometricTraceObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).map hom =
      homotopyFunctor.map
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyMap hom) :=
  rfl

/-- The geometric trace-object restriction sends a rewrite generator's
certified trace hom to the homotopy-level image of its recognition homotopy
stage. -/
theorem TraceAnalyticMotiveRecognition.geometricTraceObjectRestrictionFunctor_rewriteGeneratorMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (generator : TraceRewriteGenerator) :
    (TraceAnalyticMotiveRecognition.geometricTraceObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).map generator.traceHom =
      homotopyFunctor.map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
          generator) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

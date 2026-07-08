import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.HomotopyRestriction.TraceObjects.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.ToFull.Owner

/-!
# Trace-object restriction of full recognition functors from geometric data

This file records the trace-object restriction obtained from a geometric
homotopy-level recognition functor by postcomposing with the geometric-to-full
Boundary-DMgm target functor.
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

/-- The full-from-geometric trace-object restriction. -/
def TraceAnalyticMotiveRecognition.fullFromGeometricTraceObjectRestrictionFunctor
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData) :
    TraceCorQObject ⥤
      TraceAnalyticDMgmComparisonTarget (composition := composition) :=
  TraceAnalyticMotiveRecognition.geometricTraceObjectRestrictionFunctor
    (composition := composition)
    twistData
    homotopyFunctor ⋙
      TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData

/-- The full-from-geometric trace-object restriction is the geometric
trace-object restriction followed by the geometric-to-full target functor. -/
theorem TraceAnalyticMotiveRecognition.fullFromGeometricTraceObjectRestrictionFunctor_eq_comp
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData) :
    TraceAnalyticMotiveRecognition.fullFromGeometricTraceObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor =
      TraceAnalyticMotiveRecognition.geometricTraceObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor ⋙
        TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
          (composition := composition) twistData :=
  rfl

/-- Object formula for the full-from-geometric trace-object restriction. -/
theorem TraceAnalyticMotiveRecognition.fullFromGeometricTraceObjectRestrictionFunctor_obj
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (object : TraceCorQObject) :
    (TraceAnalyticMotiveRecognition.fullFromGeometricTraceObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).obj object =
      (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData).obj
        ((TraceAnalyticMotiveRecognition.geometricTraceObjectRestrictionFunctor
          (composition := composition)
          twistData
          homotopyFunctor).obj object) :=
  rfl

/-- Map formula for the full-from-geometric trace-object restriction. -/
theorem TraceAnalyticMotiveRecognition.fullFromGeometricTraceObjectRestrictionFunctor_map
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    {source target : TraceCorQObject}
    (hom : source ⟶ target) :
    (TraceAnalyticMotiveRecognition.fullFromGeometricTraceObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).map hom =
      (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData).map
        ((TraceAnalyticMotiveRecognition.geometricTraceObjectRestrictionFunctor
          (composition := composition)
          twistData
          homotopyFunctor).map hom) :=
  rfl

/-- The full-from-geometric trace-object restriction sends a rewrite
generator's certified trace hom to the geometric trace-object image followed
by the geometric-to-full target functor. -/
theorem TraceAnalyticMotiveRecognition.fullFromGeometricTraceObjectRestrictionFunctor_rewriteGeneratorMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (generator : TraceRewriteGenerator) :
    (TraceAnalyticMotiveRecognition.fullFromGeometricTraceObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).map generator.traceHom =
      (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData).map
        ((TraceAnalyticMotiveRecognition.geometricTraceObjectRestrictionFunctor
          (composition := composition)
          twistData
          homotopyFunctor).map generator.traceHom) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

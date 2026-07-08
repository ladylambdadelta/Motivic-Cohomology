import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Presheaves.Linear.Owner

/-!
# Top-root linear trace presheaves

This file exposes additive and Q-linear behavior of trace-presheaf evaluation
and representable-presheaf inclusion under the top-level `AnalyticMotivesRoot`
namespace.
-/

open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes the preadditive structure on trace presheaves. -/
def AnalyticMotivesRoot.traceCorQPresheafPreadditive :
    CategoryTheory.Preadditive TraceCorQPresheaf :=
  TraceCorQPresheaf.preadditive

/-- The top root exposes the rational linear structure on trace presheaves. -/
def AnalyticMotivesRoot.traceCorQPresheafLinearRat :
    CategoryTheory.Linear Rat TraceCorQPresheaf :=
  TraceCorQPresheaf.linearRat

/-- The top root exposes the preadditive structure on representable trace presheaves. -/
def AnalyticMotivesRoot.traceCorQRepresentablePresheafPreadditive :
    CategoryTheory.Preadditive TraceCorQRepresentablePresheaf :=
  TraceCorQRepresentablePresheaf.preadditive

/-- The top root exposes the rational linear structure on representable trace presheaves. -/
def AnalyticMotivesRoot.traceCorQRepresentablePresheafLinearRat :
    CategoryTheory.Linear Rat TraceCorQRepresentablePresheaf :=
  TraceCorQRepresentablePresheaf.linearRat

/-- The top root exposes that inclusion preserves addition of representable-presheaf morphisms. -/
theorem AnalyticMotivesRoot.traceCorQRepresentablePresheaf_inclusion_map_add
    {source target : TraceCorQRepresentablePresheaf}
    (left right : source ⟶ target) :
    TraceCorQRepresentablePresheaf.inclusion.map (left + right) =
      TraceCorQRepresentablePresheaf.inclusion.map left +
        TraceCorQRepresentablePresheaf.inclusion.map right :=
  TraceCorQRepresentablePresheaf.inclusion_map_add
    left
    right

/-- The top root exposes that inclusion preserves rational scalar multiplication. -/
theorem AnalyticMotivesRoot.traceCorQRepresentablePresheaf_inclusion_map_smul
    {source target : TraceCorQRepresentablePresheaf}
    (coefficient : Rat)
    (morphism : source ⟶ target) :
    TraceCorQRepresentablePresheaf.inclusion.map (coefficient • morphism) =
      coefficient • TraceCorQRepresentablePresheaf.inclusion.map morphism :=
  TraceCorQRepresentablePresheaf.inclusion_map_smul
    coefficient
    morphism

/-- The top root exposes that evaluation preserves addition of presheaf morphisms. -/
theorem AnalyticMotivesRoot.traceCorQPresheaf_evaluation_map_add
    (object : TraceCorQObject)
    {source target : TraceCorQPresheaf}
    (left right : source ⟶ target) :
    (TraceCorQPresheaf.evaluation object).map (left + right) =
      (TraceCorQPresheaf.evaluation object).map left +
        (TraceCorQPresheaf.evaluation object).map right :=
  TraceCorQPresheaf.evaluation_map_add
    object
    left
    right

/-- The top root exposes that evaluation preserves rational scalar multiplication. -/
theorem AnalyticMotivesRoot.traceCorQPresheaf_evaluation_map_smul
    (object : TraceCorQObject)
    {source target : TraceCorQPresheaf}
    (coefficient : Rat)
    (morphism : source ⟶ target) :
    (TraceCorQPresheaf.evaluation object).map (coefficient • morphism) =
      coefficient • (TraceCorQPresheaf.evaluation object).map morphism :=
  TraceCorQPresheaf.evaluation_map_smul
    object
    coefficient
    morphism

end AnalyticMotives
end LFunctions
end Boundary

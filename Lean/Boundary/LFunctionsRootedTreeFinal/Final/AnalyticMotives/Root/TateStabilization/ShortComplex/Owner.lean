import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Motives.Summary.TateStabilization.ShortComplex.Owner

/-!
# Public Tate short-complex facade

This file exposes the Tate bounded mapping-cone short-complex projections at
the top root surface.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Public root summary: the short complex of the Tate bounded mapping cone. -/
def AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeShortComplex
    (source target : QTraceExpression) :
    ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeShortComplex
    source
    target

/-- Public root summary: the Tate bounded mapping-cone short complex has the source
object as its left vertex. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeShortComplex_X₁
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeShortComplex.X₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeShortComplex_X₁
    source
    target

/-- Public root summary: the Tate bounded mapping-cone short complex has the target
object as its middle vertex. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeShortComplex_X₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeShortComplex.X₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeShortComplex_X₂
    source
    target

/-- Public root summary: the Tate bounded mapping-cone short complex has the cone object
as its right vertex. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeShortComplex_X₃
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeShortComplex.X₃ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObject
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeShortComplex_X₃
    source
    target

/-- Public root summary: the first morphism of the Tate bounded mapping-cone short
complex is the bounded map. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeShortComplex_f
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeShortComplex.f =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeShortComplex_f
    source
    target

/-- Public root summary: the second morphism of the Tate bounded mapping-cone short
complex is the cone-inclusion map. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeShortComplex_g
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeShortComplex.g =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeShortComplex_g
    source
    target

/-- Public root summary: the Tate bounded mapping-cone short complex has zero
composite. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeShortComplex_zero
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeShortComplex.f ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeShortComplex.g =
      0 :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeShortComplex_zero
    source
    target

end AnalyticMotives
end LFunctions
end Boundary

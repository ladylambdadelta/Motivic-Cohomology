import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.TateStabilization.ShortComplex.Owner

/-!
# Public motive summary for Tate short complexes

This file exposes the Tate bounded mapping-cone short-complex projections
through the public `AnalyticMotivesRoot` namespace.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Public motive summary: the short complex of the Tate bounded mapping cone. -/
def AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeShortComplex
    (source target : QTraceExpression) :
    ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeShortComplex
    source
    target

/-- Public motive summary: the Tate bounded mapping-cone short complex has the source
object as its left vertex. -/
theorem AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeShortComplex_X₁
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeShortComplex.X₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeShortComplex_X₁
    source
    target

/-- Public motive summary: the Tate bounded mapping-cone short complex has the target
object as its middle vertex. -/
theorem AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeShortComplex_X₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeShortComplex.X₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeShortComplex_X₂
    source
    target

/-- Public motive summary: the Tate bounded mapping-cone short complex has the cone
object as its right vertex. -/
theorem AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeShortComplex_X₃
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeShortComplex.X₃ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObject
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeShortComplex_X₃
    source
    target

/-- Public motive summary: the first morphism of the Tate bounded mapping-cone short
complex is the bounded map. -/
theorem AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeShortComplex_f
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeShortComplex.f =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeShortComplex_f
    source
    target

/-- Public motive summary: the second morphism of the Tate bounded mapping-cone short
complex is the cone-inclusion map. -/
theorem AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeShortComplex_g
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeShortComplex.g =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeShortComplex_g
    source
    target

/-- Public motive summary: the Tate bounded mapping-cone short complex has zero
composite. -/
theorem AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeShortComplex_zero
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeShortComplex.f ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeShortComplex.g =
      0 :=
  TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeShortComplex_zero
    source
    target

end AnalyticMotives
end LFunctions
end Boundary

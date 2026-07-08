import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.TateStabilization.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.LocalizationInput.ShortComplex.Owner

/-!
# Motive-root Tate short complexes

This file exposes the short complex of the Tate weight-drop bounded mapping
cone through the motive-root namespace.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Motive-root facade: the short complex of the Tate bounded mapping cone. -/
def TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeShortComplex
    (source target : QTraceExpression) :
    ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeShortComplex

/-- Motive-root facade: the Tate bounded mapping-cone short complex has the source object
as its left vertex. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeShortComplex_X₁
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeShortComplex.X₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeShortComplex_X₁
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the Tate bounded mapping-cone short complex has the target object
as its middle vertex. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeShortComplex_X₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeShortComplex.X₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeShortComplex_X₂
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the Tate bounded mapping-cone short complex has the cone object
as its right vertex. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeShortComplex_X₃
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeShortComplex.X₃ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObject
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeShortComplex_X₃
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the first morphism of the Tate bounded mapping-cone short complex
is the bounded map. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeShortComplex_f
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeShortComplex.f =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeShortComplex_f
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the second morphism of the Tate bounded mapping-cone short
complex is the cone-inclusion map. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeShortComplex_g
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeShortComplex.g =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeShortComplex_g
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the Tate bounded mapping-cone short complex has zero composite. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeShortComplex_zero
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeShortComplex.f ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeShortComplex.g =
      0 :=
  TraceLocalizationInput.boundedMappingConeShortComplex_zero
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary

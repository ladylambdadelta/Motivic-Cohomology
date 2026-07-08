import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Summary.LocalizationInput.Triangles.Owner

/-!
# Motive-root localization-input cone triangle projections

This file exposes the projection facts for the bounded mapping-cone triangle
attached to an arbitrary localization input.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root summary: the first bounded representative is the common-bounded source. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeTriangle_first
    (input : TraceLocalizationInput) :
    input.boundedMappingConeTriangle.first =
      input.commonBoundedAdditiveSourceComplex :=
  TraceLocalizationInput.boundedMappingConeTriangle_first
    input

/-- Motive-root summary: the second bounded representative is the common-bounded target. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeTriangle_second
    (input : TraceLocalizationInput) :
    input.boundedMappingConeTriangle.second =
      input.commonBoundedAdditiveTargetComplex :=
  TraceLocalizationInput.boundedMappingConeTriangle_second
    input

/-- Motive-root summary: the underlying triangle is the bounded mapping-cone triangle of
the bounded localization-input map. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeTriangle_triangle
    (input : TraceLocalizationInput) :
    input.boundedMappingConeTriangle.triangle =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.triangle
        input.boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeTriangle_triangle
    input

/-- Motive-root summary: the first homotopy object is the source object of the bounded
mapping-cone construction. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeTriangle_firstObject
    (input : TraceLocalizationInput) :
    input.boundedMappingConeTriangle.firstObject =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        input.boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeTriangle_firstObject
    input

/-- Motive-root summary: the second homotopy object is the target object of the bounded
mapping-cone construction. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeTriangle_secondObject
    (input : TraceLocalizationInput) :
    input.boundedMappingConeTriangle.secondObject =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        input.boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeTriangle_secondObject
    input

/-- Motive-root summary: the first triangle map is the bounded localization-input map. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeTriangle_firstMap
    (input : TraceLocalizationInput) :
    input.boundedMappingConeTriangle.firstMap =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        input.boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeTriangle_firstMap
    input

/-- Motive-root summary: the third vertex is the bounded mapping-cone third object. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeTriangle_thirdVertex
    (input : TraceLocalizationInput) :
    input.boundedMappingConeTriangle.triangleThirdVertex =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.triangle
        input.boundedAdditiveComplexHom).obj₃ :=
  TraceLocalizationInput.boundedMappingConeTriangle_thirdVertex
    input

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Summary.LocalizationInput.Triangles.Projections.Owner

/-!
# Top-root localization-input cone triangle projections

This file exposes bounded mapping-cone triangle projection facts for arbitrary
localization inputs.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public motive summary: the first bounded representative is the common-bounded source. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeTriangle_first
    (input : TraceLocalizationInput) :
    input.boundedMappingConeTriangle.first =
      input.commonBoundedAdditiveSourceComplex :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeTriangle_first
    input

/-- Public motive summary: the second bounded representative is the common-bounded target. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeTriangle_second
    (input : TraceLocalizationInput) :
    input.boundedMappingConeTriangle.second =
      input.commonBoundedAdditiveTargetComplex :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeTriangle_second
    input

/-- Public motive summary: the underlying triangle is the bounded mapping-cone triangle
of the bounded localization-input map. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeTriangle_triangle
    (input : TraceLocalizationInput) :
    input.boundedMappingConeTriangle.triangle =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.triangle
        input.boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeTriangle_triangle
    input

/-- Public motive summary: the first homotopy object is the source object of the bounded
mapping-cone construction. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeTriangle_firstObject
    (input : TraceLocalizationInput) :
    input.boundedMappingConeTriangle.firstObject =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        input.boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeTriangle_firstObject
    input

/-- Public motive summary: the second homotopy object is the target object of the bounded
mapping-cone construction. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeTriangle_secondObject
    (input : TraceLocalizationInput) :
    input.boundedMappingConeTriangle.secondObject =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        input.boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeTriangle_secondObject
    input

/-- Public motive summary: the first triangle map is the bounded localization-input map. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeTriangle_firstMap
    (input : TraceLocalizationInput) :
    input.boundedMappingConeTriangle.firstMap =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        input.boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeTriangle_firstMap
    input

/-- Public motive summary: the third vertex is the bounded mapping-cone third object. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeTriangle_thirdVertex
    (input : TraceLocalizationInput) :
    input.boundedMappingConeTriangle.triangleThirdVertex =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.triangle
        input.boundedAdditiveComplexHom).obj₃ :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeTriangle_thirdVertex
    input

end AnalyticMotives
end LFunctions
end Boundary

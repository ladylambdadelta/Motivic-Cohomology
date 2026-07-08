import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Motives.Summary.LocalizationInput.Triangles.Projections.Owner

/-!
# Public localization-input cone triangle projection facade

This file exposes bounded mapping-cone triangle projection facts for arbitrary
localization inputs at the top root surface.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public root facade: the first bounded representative is the common-bounded source. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeTriangle_first
    (input : TraceLocalizationInput) :
    input.boundedMappingConeTriangle.first =
      input.commonBoundedAdditiveSourceComplex :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeTriangle_first
    input

/-- Public root facade: the second bounded representative is the common-bounded target. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeTriangle_second
    (input : TraceLocalizationInput) :
    input.boundedMappingConeTriangle.second =
      input.commonBoundedAdditiveTargetComplex :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeTriangle_second
    input

/-- Public root facade: the underlying triangle is the bounded mapping-cone triangle of
the bounded localization-input map. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeTriangle_triangle
    (input : TraceLocalizationInput) :
    input.boundedMappingConeTriangle.triangle =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.triangle
        input.boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeTriangle_triangle
    input

/-- Public root facade: the first homotopy object is the source object of the bounded
mapping-cone construction. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeTriangle_firstObject
    (input : TraceLocalizationInput) :
    input.boundedMappingConeTriangle.firstObject =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        input.boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeTriangle_firstObject
    input

/-- Public root facade: the second homotopy object is the target object of the bounded
mapping-cone construction. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeTriangle_secondObject
    (input : TraceLocalizationInput) :
    input.boundedMappingConeTriangle.secondObject =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        input.boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeTriangle_secondObject
    input

/-- Public root facade: the first triangle map is the bounded localization-input map. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeTriangle_firstMap
    (input : TraceLocalizationInput) :
    input.boundedMappingConeTriangle.firstMap =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        input.boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeTriangle_firstMap
    input

/-- Public root facade: the third vertex is the bounded mapping-cone third object. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeTriangle_thirdVertex
    (input : TraceLocalizationInput) :
    input.boundedMappingConeTriangle.triangleThirdVertex =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.triangle
        input.boundedAdditiveComplexHom).obj₃ :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeTriangle_thirdVertex
    input

end AnalyticMotives
end LFunctions
end Boundary

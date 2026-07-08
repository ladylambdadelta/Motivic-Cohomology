import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.EndpointPayload.Owner

/-!
# Top-root unstable input endpoint payload
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic-motives root exposes unstable forward endpoint rectangles. -/
theorem AnalyticMotivesRoot.unstableForward_endpointImportedRectangles
    (input : TraceLocalizationInput) :
    input.unstableForward.endpointImportedRectangles =
      input.sourceObject.importedRectangles ++
        input.targetObject.importedRectangles :=
  TraceAnalyticMotive.unstableForward_endpointImportedRectangles
    input

/-- The analytic-motives root exposes unstable inverse endpoint rectangles. -/
theorem AnalyticMotivesRoot.unstableInverse_endpointImportedRectangles
    (input : TraceLocalizationInput) :
    input.unstableInverse.endpointImportedRectangles =
      input.targetObject.importedRectangles ++
        input.sourceObject.importedRectangles :=
  TraceAnalyticMotive.unstableInverse_endpointImportedRectangles
    input

/-- The analytic-motives root exposes unstable forward endpoint-count lengths. -/
theorem AnalyticMotivesRoot.unstableForward_endpointImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    input.unstableForward.endpointImportedRectangleCount =
      input.unstableForward.endpointImportedRectangles.length :=
  TraceAnalyticMotive.unstableForward_endpointImportedRectangleCount_eq_length
    input

/-- The analytic-motives root exposes unstable inverse endpoint-count lengths. -/
theorem AnalyticMotivesRoot.unstableInverse_endpointImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    input.unstableInverse.endpointImportedRectangleCount =
      input.unstableInverse.endpointImportedRectangles.length :=
  TraceAnalyticMotive.unstableInverse_endpointImportedRectangleCount_eq_length
    input

end AnalyticMotives
end LFunctions
end Boundary

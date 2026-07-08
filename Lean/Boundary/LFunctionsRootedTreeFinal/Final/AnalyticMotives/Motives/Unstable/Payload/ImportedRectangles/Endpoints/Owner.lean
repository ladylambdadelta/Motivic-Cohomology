import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Payload.Owner

/-!
# Endpoint imported rectangles in the unstable envelope

This file exposes endpoint imported-rectangle payload for arbitrary unstable
analytic-motive homs, inherited from the localized-word category.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Endpoint rectangles carried by an unstable analytic-motive hom. -/
def TraceUnstableAnalyticMotiveHom.endpointImportedRectangles
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  TraceLocalizedWordHom.endpointImportedRectangles hom

/-- Endpoint imported-rectangle count carried by an unstable analytic-motive hom. -/
def TraceUnstableAnalyticMotiveHom.endpointImportedRectangleCount
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    Nat :=
  TraceLocalizedWordHom.endpointImportedRectangleCount hom

/-- Endpoint imported count is the length of the endpoint rectangle list. -/
theorem TraceUnstableAnalyticMotiveHom.endpointImportedRectangleCount_eq_length
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    hom.endpointImportedRectangleCount =
      hom.endpointImportedRectangles.length :=
  TraceLocalizedWordHom.endpointImportedRectangleCount_eq_length
    hom

end AnalyticMotives
end LFunctions
end Boundary

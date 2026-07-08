import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Payload.Lengths.Owner

/-!
# Identity imported-rectangle payload in the unstable envelope

This file exposes imported-rectangle endpoint payload for identity homs in the
unstable analytic-motive envelope.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Identity hom source endpoint count is the object's imported count. -/
theorem TraceUnstableAnalyticMotiveHom.id_sourceImportedRectangleCount
    (object : TraceUnstableAnalyticMotive) :
    (TraceLocalizationWordClass.identity object.underlying).sourceImportedRectangleCount =
      TraceLocalizedWordObject.importedRectangleCount object :=
  TraceLocalizedWordHom.id_sourceImportedRectangleCount
    object

/-- Identity hom target endpoint count is the object's imported count. -/
theorem TraceUnstableAnalyticMotiveHom.id_targetImportedRectangleCount
    (object : TraceUnstableAnalyticMotive) :
    (TraceLocalizationWordClass.identity object.underlying).targetImportedRectangleCount =
      TraceLocalizedWordObject.importedRectangleCount object :=
  TraceLocalizedWordHom.id_targetImportedRectangleCount
    object

/-- Identity hom endpoint rectangles are the object's imported rectangles twice. -/
theorem TraceUnstableAnalyticMotiveHom.id_endpointImportedRectangles
    (object : TraceUnstableAnalyticMotive) :
    (TraceLocalizationWordClass.identity object.underlying).endpointImportedRectangles =
      TraceLocalizedWordObject.importedRectangles object ++
        TraceLocalizedWordObject.importedRectangles object :=
  TraceLocalizedWordHom.id_endpointImportedRectangles
    object

/-- Identity hom endpoint imported count is the object's imported count twice. -/
theorem TraceUnstableAnalyticMotiveHom.id_endpointImportedRectangleCount
    (object : TraceUnstableAnalyticMotive) :
    (TraceLocalizationWordClass.identity object.underlying).endpointImportedRectangleCount =
      TraceLocalizedWordObject.importedRectangleCount object +
        TraceLocalizedWordObject.importedRectangleCount object :=
  TraceLocalizedWordHom.id_endpointImportedRectangleCount
    object

/-- Identity hom endpoint imported count is its endpoint rectangle-list length. -/
theorem TraceUnstableAnalyticMotiveHom.id_endpointImportedRectangleCount_eq_length
    (object : TraceUnstableAnalyticMotive) :
    (TraceLocalizationWordClass.identity object.underlying).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.identity object.underlying).endpointImportedRectangles.length :=
  TraceLocalizedWordHom.id_endpointImportedRectangleCount_eq_length
    object

end AnalyticMotives
end LFunctions
end Boundary

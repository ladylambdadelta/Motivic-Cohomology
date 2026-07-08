import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Payload.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Payload.LedgerRectangles.Lengths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Payload.LedgerRectangles.Owner

/-!
# Top-root compact generator localized payloads

This file exposes the analytic finite-rectangle payload carried by the
localized-word object of a compact geometric generator at the public root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The localized object of a compact generator has the generator imported rectangles. -/
theorem AnalyticMotivesRoot.compactGenerator_localizedObject_importedRectangles
    (generator : TraceAnalyticGeometricGenerator) :
    generator.localizedObject.importedRectangles =
      generator.importedRectangles :=
  TraceAnalyticMotive.compactGenerator_localizedObject_importedRectangles
    generator

/-- The localized object of a compact generator has the generator imported count. -/
theorem AnalyticMotivesRoot.compactGenerator_localizedObject_importedRectangleCount
    (generator : TraceAnalyticGeometricGenerator) :
    generator.localizedObject.importedRectangleCount =
      generator.importedRectangleCount :=
  TraceAnalyticMotive.compactGenerator_localizedObject_importedRectangleCount
    generator

/-- The localized object imported count is counted by its rectangle list. -/
theorem AnalyticMotivesRoot.compactGenerator_localizedObject_importedRectangleCount_eq_length
    (generator : TraceAnalyticGeometricGenerator) :
    generator.localizedObject.importedRectangleCount =
      generator.localizedObject.importedRectangles.length :=
  TraceAnalyticMotive.compactGenerator_localizedObject_importedRectangleCount_eq_length
    generator

/-- The generator imported count agrees with the localized-object rectangle-list length. -/
theorem AnalyticMotivesRoot.compactGenerator_importedRectangleCount_eq_localizedObject_length
    (generator : TraceAnalyticGeometricGenerator) :
    generator.importedRectangleCount =
      generator.localizedObject.importedRectangles.length :=
  TraceAnalyticMotive.compactGenerator_importedRectangleCount_eq_localizedObject_length
    generator

/-- The generator imported rectangles agree with the localized-object imported rectangles. -/
theorem AnalyticMotivesRoot.compactGenerator_importedRectangles_eq_localizedObject
    (generator : TraceAnalyticGeometricGenerator) :
    generator.importedRectangles =
      generator.localizedObject.importedRectangles :=
  TraceAnalyticMotive.compactGenerator_importedRectangles_eq_localizedObject
    generator

end AnalyticMotives
end LFunctions
end Boundary

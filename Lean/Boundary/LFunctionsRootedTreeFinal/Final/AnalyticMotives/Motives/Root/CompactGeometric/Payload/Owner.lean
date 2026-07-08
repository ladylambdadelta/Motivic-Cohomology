import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Payload.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Payload.LedgerRectangles.Lengths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Payload.LedgerRectangles.Owner

/-!
# Motive-root compact generator localized payloads

This file exposes the analytic finite-rectangle payload carried by the
localized-word object of a compact geometric generator, and re-exports its
certificate-ledger payload children.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The localized object of a compact generator has the generator imported rectangles. -/
theorem TraceAnalyticMotive.compactGenerator_localizedObject_importedRectangles
    (generator : TraceAnalyticGeometricGenerator) :
    generator.localizedObject.importedRectangles =
      generator.importedRectangles :=
  TraceAnalyticGeometricGenerator.localizedObject_importedRectangles
    generator

/-- The localized object of a compact generator has the generator imported count. -/
theorem TraceAnalyticMotive.compactGenerator_localizedObject_importedRectangleCount
    (generator : TraceAnalyticGeometricGenerator) :
    generator.localizedObject.importedRectangleCount =
      generator.importedRectangleCount :=
  TraceAnalyticGeometricGenerator.localizedObject_importedRectangleCount
    generator

/-- The localized object imported count is counted by its rectangle list. -/
theorem TraceAnalyticMotive.compactGenerator_localizedObject_importedRectangleCount_eq_length
    (generator : TraceAnalyticGeometricGenerator) :
    generator.localizedObject.importedRectangleCount =
      generator.localizedObject.importedRectangles.length :=
  TraceAnalyticGeometricGenerator.localizedObject_importedRectangleCount_eq_length
    generator

/-- The generator imported count agrees with the localized-object rectangle-list length. -/
theorem TraceAnalyticMotive.compactGenerator_importedRectangleCount_eq_localizedObject_length
    (generator : TraceAnalyticGeometricGenerator) :
    generator.importedRectangleCount =
      generator.localizedObject.importedRectangles.length :=
  TraceAnalyticGeometricGenerator.importedRectangleCount_eq_localizedObject_length
    generator

/-- The generator imported rectangles agree with the localized-object imported rectangles. -/
theorem TraceAnalyticMotive.compactGenerator_importedRectangles_eq_localizedObject
    (generator : TraceAnalyticGeometricGenerator) :
    generator.importedRectangles =
      generator.localizedObject.importedRectangles :=
  TraceAnalyticGeometricGenerator.importedRectangles_eq_localizedObject
    generator

end AnalyticMotives
end LFunctions
end Boundary

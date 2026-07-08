import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Payload.Owner

/-!
# Analytic payload for compact geometric generators

This file records how the imported finite-rectangle payload of a compact
geometric generator is seen by its localized-word object.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The localized object of a compact generator has the generator's imported rectangles. -/
theorem TraceAnalyticGeometricGenerator.localizedObject_importedRectangles
    (generator : TraceAnalyticGeometricGenerator) :
    generator.localizedObject.importedRectangles =
      generator.importedRectangles :=
  rfl

/-- The localized object of a compact generator has the generator's imported count. -/
theorem TraceAnalyticGeometricGenerator.localizedObject_importedRectangleCount
    (generator : TraceAnalyticGeometricGenerator) :
    generator.localizedObject.importedRectangleCount =
      generator.importedRectangleCount :=
  rfl

/-- The localized object imported count is counted by its imported rectangle list. -/
theorem TraceAnalyticGeometricGenerator.localizedObject_importedRectangleCount_eq_length
    (generator : TraceAnalyticGeometricGenerator) :
    generator.localizedObject.importedRectangleCount =
      generator.localizedObject.importedRectangles.length :=
  TraceLocalizedWordObject.importedRectangleCount_eq_length
    generator.localizedObject

/-- The generator imported count agrees with the localized-object rectangle list length. -/
theorem TraceAnalyticGeometricGenerator.importedRectangleCount_eq_localizedObject_length
    (generator : TraceAnalyticGeometricGenerator) :
    generator.importedRectangleCount =
      generator.localizedObject.importedRectangles.length :=
  Eq.trans
    (Eq.symm
      (TraceAnalyticGeometricGenerator.localizedObject_importedRectangleCount
        generator))
    (TraceAnalyticGeometricGenerator.localizedObject_importedRectangleCount_eq_length
      generator)

/-- The generator imported rectangles agree with the localized-object imported rectangles. -/
theorem TraceAnalyticGeometricGenerator.importedRectangles_eq_localizedObject
    (generator : TraceAnalyticGeometricGenerator) :
    generator.importedRectangles =
      generator.localizedObject.importedRectangles :=
  Eq.symm
    (TraceAnalyticGeometricGenerator.localizedObject_importedRectangles
      generator)

end AnalyticMotives
end LFunctions
end Boundary

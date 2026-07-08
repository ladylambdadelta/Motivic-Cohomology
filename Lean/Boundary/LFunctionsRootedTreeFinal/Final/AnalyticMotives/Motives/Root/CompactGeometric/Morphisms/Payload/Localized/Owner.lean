import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Morphisms.Payload.Owner

/-!
# Motive-root compact morphism localized endpoint payloads

This file exposes the agreement between compact morphism endpoint rectangle
payloads and the localized objects of their endpoint generators.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A compact morphism source rectangle payload agrees with the source localized object. -/
theorem TraceAnalyticMotive.compactGeneratorMorphism_sourceImportedRectangles_eq_localizedObject
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.sourceImportedRectangles =
      source.localizedObject.importedRectangles :=
  TraceAnalyticGeometricGenerator.Hom.sourceImportedRectangles_eq_localizedObject
    morphism

/-- A compact morphism target rectangle payload agrees with the target localized object. -/
theorem TraceAnalyticMotive.compactGeneratorMorphism_targetImportedRectangles_eq_localizedObject
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.targetImportedRectangles =
      target.localizedObject.importedRectangles :=
  TraceAnalyticGeometricGenerator.Hom.targetImportedRectangles_eq_localizedObject
    morphism

end AnalyticMotives
end LFunctions
end Boundary

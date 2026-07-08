import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Forgetful.Payload.LedgerRectangles.Owner

/-!
# Motive-root compact forgetful ledger rectangles

This file exposes certificate-ledger rectangle-list facts for the compact
forgetful functor payload.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The forgotten object rectangle list is the generator certificate-ledger list. -/
theorem TraceAnalyticMotive.compactGenerator_forgetfulFunctor_obj_importedRectangles_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
      generator).importedRectangles =
      generator.certificateLedger.importedRectangles :=
  TraceAnalyticGeometricGenerator.forgetfulFunctor_obj_importedRectangles_eq_certificateLedger
    generator

/-- A compact morphism source rectangle list agrees with the forgotten source ledger list. -/
theorem TraceAnalyticMotive.compactGeneratorMorphism_sourceImportedRectangles_eq_forgetful_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.sourceImportedRectangles =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        source).certificateLedger.importedRectangles :=
  TraceAnalyticGeometricGenerator.Hom.sourceImportedRectangles_eq_forgetful_source_certificateLedger
    morphism

/-- A compact morphism target rectangle list agrees with the forgotten target ledger list. -/
theorem TraceAnalyticMotive.compactGeneratorMorphism_targetImportedRectangles_eq_forgetful_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.targetImportedRectangles =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        target).certificateLedger.importedRectangles :=
  TraceAnalyticGeometricGenerator.Hom.targetImportedRectangles_eq_forgetful_target_certificateLedger
    morphism

end AnalyticMotives
end LFunctions
end Boundary

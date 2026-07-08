import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Functors.Forgetful.Payload.LedgerRectangles.Owner

/-!
# Top-root compact forgetful ledger rectangles

This file exposes certificate-ledger rectangle-list facts for the compact
forgetful functor payload.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The forgotten object rectangle list is the generator certificate-ledger list. -/
theorem AnalyticMotivesRoot.compactGenerator_forgetfulFunctor_obj_importedRectangles_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
      generator).importedRectangles =
      generator.certificateLedger.importedRectangles :=
  TraceAnalyticMotive.compactGenerator_forgetfulFunctor_obj_importedRectangles_eq_certificateLedger
    generator

/-- A compact morphism source rectangle list agrees with the forgotten source ledger list. -/
theorem AnalyticMotivesRoot.compactGeneratorMorphism_sourceImportedRectangles_eq_forgetful_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.sourceImportedRectangles =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        source).certificateLedger.importedRectangles :=
  TraceAnalyticMotive.compactGeneratorMorphism_sourceImportedRectangles_eq_forgetful_source_certificateLedger
    morphism

/-- A compact morphism target rectangle list agrees with the forgotten target ledger list. -/
theorem AnalyticMotivesRoot.compactGeneratorMorphism_targetImportedRectangles_eq_forgetful_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.targetImportedRectangles =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        target).certificateLedger.importedRectangles :=
  TraceAnalyticMotive.compactGeneratorMorphism_targetImportedRectangles_eq_forgetful_target_certificateLedger
    morphism

end AnalyticMotives
end LFunctions
end Boundary

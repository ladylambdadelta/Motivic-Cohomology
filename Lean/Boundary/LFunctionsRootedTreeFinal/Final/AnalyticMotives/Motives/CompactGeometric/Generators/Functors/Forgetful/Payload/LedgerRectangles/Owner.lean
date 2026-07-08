import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Forgetful.Payload.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Morphisms.Payload.LedgerRectangles.Owner

/-!
# Ledger rectangle lists for compact-generator forgetful payloads

This file records that imported-rectangle lists preserved by the
compact-generator forgetful functor are the corresponding certificate-ledger
rectangle lists.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The forgotten object rectangle list is the generator certificate-ledger list. -/
theorem TraceAnalyticGeometricGenerator.forgetfulFunctor_obj_importedRectangles_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
      generator).importedRectangles =
      generator.certificateLedger.importedRectangles :=
  TraceAnalyticGeometricGenerator.importedRectangles_eq_certificateLedger
    generator

/-- A compact morphism source rectangle list agrees with the forgotten source ledger list. -/
theorem TraceAnalyticGeometricGenerator.Hom.sourceImportedRectangles_eq_forgetful_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.sourceImportedRectangles =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        source).certificateLedger.importedRectangles :=
  TraceAnalyticGeometricGenerator.Hom.sourceImportedRectangles_eq_source_certificateLedger
    morphism

/-- A compact morphism target rectangle list agrees with the forgotten target ledger list. -/
theorem TraceAnalyticGeometricGenerator.Hom.targetImportedRectangles_eq_forgetful_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.targetImportedRectangles =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        target).certificateLedger.importedRectangles :=
  TraceAnalyticGeometricGenerator.Hom.targetImportedRectangles_eq_target_certificateLedger
    morphism

end AnalyticMotives
end LFunctions
end Boundary

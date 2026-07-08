import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Forgetful.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Morphisms.Payload.LedgerCounts.Owner

/-!
# Ledger counts for compact-generator forgetful payloads

This file records that payload counts preserved by the compact-generator
forgetful functor are counted by the corresponding certificate ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The forgotten object imported count is counted by the generator ledger. -/
theorem TraceAnalyticGeometricGenerator.forgetfulFunctor_obj_importedRectangleCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
      generator).importedRectangleCount =
      generator.certificateLedger.importedRectangleCount :=
  TraceAnalyticGeometricGenerator.importedRectangleCount_eq_certificateLedger
    generator

/-- The forgotten object bookkeeping count is counted by the generator ledger. -/
theorem TraceAnalyticGeometricGenerator.forgetfulFunctor_obj_traceBookkeepingCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
      generator).traceBookkeepingCount =
      generator.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticGeometricGenerator.traceBookkeepingCount_eq_certificateLedger
    generator

/-- The forgotten object rewrite count is counted by the generator ledger. -/
theorem TraceAnalyticGeometricGenerator.forgetfulFunctor_obj_rewriteStepCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
      generator).rewriteStepCount =
      generator.certificateLedger.rewriteStepCount :=
  TraceAnalyticGeometricGenerator.rewriteStepCount_eq_certificateLedger
    generator

/-- A compact morphism source count agrees with the forgotten source ledger count. -/
theorem TraceAnalyticGeometricGenerator.Hom.sourceImportedRectangleCount_eq_forgetful_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.sourceImportedRectangleCount =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        source).certificateLedger.importedRectangleCount :=
  TraceAnalyticGeometricGenerator.Hom.sourceImportedRectangleCount_eq_source_certificateLedger
    morphism

/-- A compact morphism target count agrees with the forgotten target ledger count. -/
theorem TraceAnalyticGeometricGenerator.Hom.targetImportedRectangleCount_eq_forgetful_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.targetImportedRectangleCount =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        target).certificateLedger.importedRectangleCount :=
  TraceAnalyticGeometricGenerator.Hom.targetImportedRectangleCount_eq_target_certificateLedger
    morphism

end AnalyticMotives
end LFunctions
end Boundary

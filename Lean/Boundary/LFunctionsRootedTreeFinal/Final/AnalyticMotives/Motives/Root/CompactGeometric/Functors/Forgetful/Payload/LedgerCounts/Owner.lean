import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Forgetful.Payload.LedgerCounts.Owner

/-!
# Motive-root compact forgetful ledger counts

This file exposes certificate-ledger count facts for the compact forgetful
functor payload.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The forgotten object imported count is counted by the generator ledger. -/
theorem TraceAnalyticMotive.compactGenerator_forgetfulFunctor_obj_importedRectangleCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
      generator).importedRectangleCount =
      generator.certificateLedger.importedRectangleCount :=
  TraceAnalyticGeometricGenerator.forgetfulFunctor_obj_importedRectangleCount_eq_certificateLedger
    generator

/-- The forgotten object bookkeeping count is counted by the generator ledger. -/
theorem TraceAnalyticMotive.compactGenerator_forgetfulFunctor_obj_traceBookkeepingCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
      generator).traceBookkeepingCount =
      generator.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticGeometricGenerator.forgetfulFunctor_obj_traceBookkeepingCount_eq_certificateLedger
    generator

/-- The forgotten object rewrite count is counted by the generator ledger. -/
theorem TraceAnalyticMotive.compactGenerator_forgetfulFunctor_obj_rewriteStepCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
      generator).rewriteStepCount =
      generator.certificateLedger.rewriteStepCount :=
  TraceAnalyticGeometricGenerator.forgetfulFunctor_obj_rewriteStepCount_eq_certificateLedger
    generator

/-- A compact morphism source count agrees with the forgotten source ledger count. -/
theorem TraceAnalyticMotive.compactGeneratorMorphism_sourceImportedRectangleCount_eq_forgetful_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.sourceImportedRectangleCount =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        source).certificateLedger.importedRectangleCount :=
  TraceAnalyticGeometricGenerator.Hom.sourceImportedRectangleCount_eq_forgetful_source_certificateLedger
    morphism

/-- A compact morphism target count agrees with the forgotten target ledger count. -/
theorem TraceAnalyticMotive.compactGeneratorMorphism_targetImportedRectangleCount_eq_forgetful_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.targetImportedRectangleCount =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        target).certificateLedger.importedRectangleCount :=
  TraceAnalyticGeometricGenerator.Hom.targetImportedRectangleCount_eq_forgetful_target_certificateLedger
    morphism

end AnalyticMotives
end LFunctions
end Boundary

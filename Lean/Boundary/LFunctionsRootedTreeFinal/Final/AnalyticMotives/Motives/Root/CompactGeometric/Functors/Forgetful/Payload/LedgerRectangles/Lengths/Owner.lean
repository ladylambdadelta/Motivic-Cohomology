import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Forgetful.Payload.LedgerRectangles.Lengths.Owner

/-!
# Motive-root compact forgetful ledger rectangle lengths

This file exposes count-as-length facts for certificate-ledger rectangle lists
of the compact forgetful functor payload.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The forgotten object certificate-ledger rectangle list has the forgotten imported count. -/
theorem TraceAnalyticMotive.compactGenerator_forgetfulFunctor_obj_certificateLedgerRectangles_length
    (generator : TraceAnalyticGeometricGenerator) :
    generator.certificateLedger.importedRectangleCount =
      generator.certificateLedger.importedRectangles.length :=
  TraceAnalyticGeometricGenerator.forgetfulFunctor_obj_certificateLedgerRectangles_length
    generator

/-- A forgotten source ledger rectangle list has the source endpoint imported count. -/
theorem TraceAnalyticMotive.compactGeneratorMorphism_source_forgetful_certificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
      source).certificateLedger.importedRectangleCount =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        source).certificateLedger.importedRectangles.length :=
  TraceAnalyticGeometricGenerator.Hom.source_forgetful_certificateLedgerRectangles_length
    morphism

/-- A forgotten target ledger rectangle list has the target endpoint imported count. -/
theorem TraceAnalyticMotive.compactGeneratorMorphism_target_forgetful_certificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
      target).certificateLedger.importedRectangleCount =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        target).certificateLedger.importedRectangles.length :=
  TraceAnalyticGeometricGenerator.Hom.target_forgetful_certificateLedgerRectangles_length
    morphism

end AnalyticMotives
end LFunctions
end Boundary

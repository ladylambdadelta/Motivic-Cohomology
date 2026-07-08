import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Forgetful.Payload.LedgerRectangles.Owner

/-!
# Lengths of compact-generator forgetful ledger rectangle lists

This file connects forgetful-functor certificate-ledger rectangle-list formulas
to the corresponding imported-rectangle count formulas.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The forgotten object certificate-ledger rectangle list has the forgotten imported count. -/
theorem TraceAnalyticGeometricGenerator.forgetfulFunctor_obj_certificateLedgerRectangles_length
    (generator : TraceAnalyticGeometricGenerator) :
    generator.certificateLedger.importedRectangleCount =
      generator.certificateLedger.importedRectangles.length :=
  Eq.trans
    (Eq.sym
      (TraceAnalyticGeometricGenerator.forgetfulFunctor_obj_importedRectangleCount_eq_certificateLedger
        generator))
    (Eq.trans
      (TraceAnalyticGeometricGenerator.forgetfulFunctor_obj_importedRectangleCount_eq_length
        generator)
      (congrArg
        List.length
        (TraceAnalyticGeometricGenerator.forgetfulFunctor_obj_importedRectangles_eq_certificateLedger
          generator)))

/-- A forgotten source ledger rectangle list has the source endpoint imported count. -/
theorem TraceAnalyticGeometricGenerator.Hom.source_forgetful_certificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
      source).certificateLedger.importedRectangleCount =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        source).certificateLedger.importedRectangles.length :=
  Eq.trans
    (Eq.sym
      (TraceAnalyticGeometricGenerator.Hom.sourceImportedRectangleCount_eq_forgetful_source_certificateLedger
        morphism))
    (Eq.trans
      (TraceAnalyticGeometricGenerator.Hom.sourceImportedRectangleCount_eq_length
        morphism)
      (congrArg
        List.length
        (TraceAnalyticGeometricGenerator.Hom.sourceImportedRectangles_eq_forgetful_source_certificateLedger
          morphism)))

/-- A forgotten target ledger rectangle list has the target endpoint imported count. -/
theorem TraceAnalyticGeometricGenerator.Hom.target_forgetful_certificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
      target).certificateLedger.importedRectangleCount =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        target).certificateLedger.importedRectangles.length :=
  Eq.trans
    (Eq.sym
      (TraceAnalyticGeometricGenerator.Hom.targetImportedRectangleCount_eq_forgetful_target_certificateLedger
        morphism))
    (Eq.trans
      (TraceAnalyticGeometricGenerator.Hom.targetImportedRectangleCount_eq_length
        morphism)
      (congrArg
        List.length
        (TraceAnalyticGeometricGenerator.Hom.targetImportedRectangles_eq_forgetful_target_certificateLedger
          morphism)))

end AnalyticMotives
end LFunctions
end Boundary

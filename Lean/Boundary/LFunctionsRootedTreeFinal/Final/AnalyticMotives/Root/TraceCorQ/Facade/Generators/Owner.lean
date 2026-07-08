import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Facade.Objects.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Facade.Generators.Owner

/-!
# Top-root trace-correspondence generator facade

This file exposes `TraceCorQ` generator payload and composition wrappers under
`AnalyticMotivesRoot`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes generator certificate-ledger splitting. -/
theorem AnalyticMotivesRoot.traceCorQGenerator_certificateLedger_eq_source_target_path
    (generator : TraceCorQGenerator) :
    generator.certificateLedger =
      ResidueChannelCertificateLedger.append
        generator.source.certificateLedger
        (ResidueChannelCertificateLedger.append
          generator.target.certificateLedger
          generator.pathCertificateLedger) :=
  TraceCorQ.generator_certificateLedger_eq_source_target_path
    generator

/-- The top root exposes generator imported-rectangle counts as list lengths. -/
theorem AnalyticMotivesRoot.traceCorQGenerator_importedRectangleCount_eq_length
    (generator : TraceCorQGenerator) :
    generator.importedRectangleCount =
      generator.importedRectangles.length :=
  TraceCorQ.generator_importedRectangleCount_eq_length
    generator

/-- The top root exposes generator imported-rectangle payload splitting. -/
theorem AnalyticMotivesRoot.traceCorQGenerator_importedRectangleCount_eq_source_target_path
    (generator : TraceCorQGenerator) :
    generator.importedRectangleCount =
      generator.source.importedRectangleCount +
        (generator.target.importedRectangleCount +
          generator.pathCertificateLedger.importedRectangleCount) :=
  TraceCorQ.generator_importedRectangleCount_eq_source_target_path
    generator

/-- The top root exposes generator imported-rectangle list splitting. -/
theorem AnalyticMotivesRoot.traceCorQGenerator_importedRectangles_eq_source_target_path
    (generator : TraceCorQGenerator) :
    generator.importedRectangles =
      generator.source.importedRectangles ++
        (generator.target.importedRectangles ++
          generator.pathCertificateLedger.importedRectangles) :=
  TraceCorQ.generator_importedRectangles_eq_source_target_path
    generator

/-- The top root exposes generator bookkeeping payload splitting. -/
theorem AnalyticMotivesRoot.traceCorQGenerator_traceBookkeepingCount_eq_source_target_path
    (generator : TraceCorQGenerator) :
    generator.traceBookkeepingCount =
      generator.source.traceBookkeepingCount +
        (generator.target.traceBookkeepingCount +
          generator.pathCertificateLedger.traceBookkeepingCount) :=
  TraceCorQ.generator_traceBookkeepingCount_eq_source_target_path
    generator

/-- The top root exposes generator rewrite-step payload splitting. -/
theorem AnalyticMotivesRoot.traceCorQGenerator_rewriteStepCount_eq_source_target_path
    (generator : TraceCorQGenerator) :
    generator.rewriteStepCount =
      generator.source.rewriteStepCount +
        (generator.target.rewriteStepCount +
          generator.pathCertificateLedger.rewriteStepCount) :=
  TraceCorQ.generator_rewriteStepCount_eq_source_target_path
    generator

/-- The top root exposes identity trace-correspondence generators. -/
def AnalyticMotivesRoot.traceCorQGenerator_id
    (object : TraceCorQObject) :
    TraceCorQGenerator :=
  TraceCorQ.generator_id object

/-- The top root exposes trace-correspondence generator composition. -/
def AnalyticMotivesRoot.traceCorQGenerator_comp
    (first second : TraceCorQGenerator) :
    TraceCorQGenerator :=
  TraceCorQ.generator_comp first second

/-- The top root exposes identity-generator sources. -/
theorem AnalyticMotivesRoot.traceCorQGenerator_id_source
    (object : TraceCorQObject) :
    (TraceCorQGenerator.id object).source =
      object :=
  TraceCorQ.generator_id_source object

/-- The top root exposes identity-generator targets. -/
theorem AnalyticMotivesRoot.traceCorQGenerator_id_target
    (object : TraceCorQObject) :
    (TraceCorQGenerator.id object).target =
      object :=
  TraceCorQ.generator_id_target object

/-- The top root exposes composition-generator sources. -/
theorem AnalyticMotivesRoot.traceCorQGenerator_comp_source
    (first second : TraceCorQGenerator) :
    (TraceCorQGenerator.comp first second).source =
      first.source :=
  TraceCorQ.generator_comp_source first second

/-- The top root exposes composition-generator targets. -/
theorem AnalyticMotivesRoot.traceCorQGenerator_comp_target
    (first second : TraceCorQGenerator) :
    (TraceCorQGenerator.comp first second).target =
      second.target :=
  TraceCorQ.generator_comp_target first second

/-- The top root exposes composition-generator paths. -/
theorem AnalyticMotivesRoot.traceCorQGenerator_comp_path
    (first second : TraceCorQGenerator) :
    (TraceCorQGenerator.comp first second).path =
      first.path.comp second.path :=
  TraceCorQ.generator_comp_path first second

/-- The top root exposes identity-generator certificate ledgers. -/
theorem AnalyticMotivesRoot.traceCorQGenerator_id_certificateLedger
    (object : TraceCorQObject) :
    (TraceCorQGenerator.id object).certificateLedger =
      (TraceTransport.id object).certificateLedger :=
  TraceCorQ.generator_id_certificateLedger object

/-- The top root exposes identity-generator imported-rectangle counts. -/
theorem AnalyticMotivesRoot.traceCorQGenerator_id_importedRectangleCount
    (object : TraceCorQObject) :
    (TraceCorQGenerator.id object).importedRectangleCount =
      (TraceTransport.id object).importedRectangleCount :=
  TraceCorQ.generator_id_importedRectangleCount object

/-- The top root exposes identity-generator imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQGenerator_id_importedRectangles
    (object : TraceCorQObject) :
    (TraceCorQGenerator.id object).importedRectangles =
      (TraceTransport.id object).importedRectangles :=
  TraceCorQ.generator_id_importedRectangles object

/-- The top root exposes identity-generator bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQGenerator_id_traceBookkeepingCount
    (object : TraceCorQObject) :
    (TraceCorQGenerator.id object).traceBookkeepingCount =
      (TraceTransport.id object).traceBookkeepingCount :=
  TraceCorQ.generator_id_traceBookkeepingCount object

/-- The top root exposes identity-generator rewrite-step counts. -/
theorem AnalyticMotivesRoot.traceCorQGenerator_id_rewriteStepCount
    (object : TraceCorQObject) :
    (TraceCorQGenerator.id object).rewriteStepCount =
      (TraceTransport.id object).rewriteStepCount :=
  TraceCorQ.generator_id_rewriteStepCount object

/-- The top root exposes identity-generator imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQGenerator_id_importedRectangles_eq_object_path
    (object : TraceCorQObject) :
    (TraceCorQGenerator.id object).importedRectangles =
      object.importedRectangles ++
        (object.importedRectangles ++
          (ResidueChannelCertificateLedger.ofRewritePath
            (TraceRewritePath.id object.source)).importedRectangles) :=
  TraceCorQ.generator_id_importedRectangles_eq_object_path object

/-- The top root exposes identity-generator rewrite-step payload. -/
theorem AnalyticMotivesRoot.traceCorQGenerator_id_rewriteStepCount_eq_object_path
    (object : TraceCorQObject) :
    (TraceCorQGenerator.id object).rewriteStepCount =
      object.rewriteStepCount +
        (object.rewriteStepCount +
          (ResidueChannelCertificateLedger.ofRewritePath
            (TraceRewritePath.id object.source)).rewriteStepCount) :=
  TraceCorQ.generator_id_rewriteStepCount_eq_object_path object

/-- The top root exposes composition-generator certificate ledgers. -/
theorem AnalyticMotivesRoot.traceCorQGenerator_comp_certificateLedger
    (first second : TraceCorQGenerator) :
    (TraceCorQGenerator.comp first second).certificateLedger =
      (TraceTransport.comp first second).certificateLedger :=
  TraceCorQ.generator_comp_certificateLedger first second

/-- The top root exposes composition-generator imported-rectangle counts. -/
theorem AnalyticMotivesRoot.traceCorQGenerator_comp_importedRectangleCount
    (first second : TraceCorQGenerator) :
    (TraceCorQGenerator.comp first second).importedRectangleCount =
      (TraceTransport.comp first second).importedRectangleCount :=
  TraceCorQ.generator_comp_importedRectangleCount first second

/-- The top root exposes composition-generator imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQGenerator_comp_importedRectangles
    (first second : TraceCorQGenerator) :
    (TraceCorQGenerator.comp first second).importedRectangles =
      (TraceTransport.comp first second).importedRectangles :=
  TraceCorQ.generator_comp_importedRectangles first second

/-- The top root exposes composition-generator bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQGenerator_comp_traceBookkeepingCount
    (first second : TraceCorQGenerator) :
    (TraceCorQGenerator.comp first second).traceBookkeepingCount =
      (TraceTransport.comp first second).traceBookkeepingCount :=
  TraceCorQ.generator_comp_traceBookkeepingCount first second

/-- The top root exposes composition-generator rewrite-step counts. -/
theorem AnalyticMotivesRoot.traceCorQGenerator_comp_rewriteStepCount
    (first second : TraceCorQGenerator) :
    (TraceCorQGenerator.comp first second).rewriteStepCount =
      (TraceTransport.comp first second).rewriteStepCount :=
  TraceCorQ.generator_comp_rewriteStepCount first second

/-- The top root exposes composition-generator imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQGenerator_comp_importedRectangles_eq_endpoints_path
    (first second : TraceCorQGenerator) :
    (TraceCorQGenerator.comp first second).importedRectangles =
      first.source.importedRectangles ++
        (second.target.importedRectangles ++
          (ResidueChannelCertificateLedger.ofRewritePath
            (first.path.comp second.path)).importedRectangles) :=
  TraceCorQ.generator_comp_importedRectangles_eq_endpoints_path first second

/-- The top root exposes composition-generator rewrite-step payload. -/
theorem AnalyticMotivesRoot.traceCorQGenerator_comp_rewriteStepCount_eq_endpoints_path
    (first second : TraceCorQGenerator) :
    (TraceCorQGenerator.comp first second).rewriteStepCount =
      first.source.rewriteStepCount +
        (second.target.rewriteStepCount +
          (ResidueChannelCertificateLedger.ofRewritePath
            (first.path.comp second.path)).rewriteStepCount) :=
  TraceCorQ.generator_comp_rewriteStepCount_eq_endpoints_path first second

end AnalyticMotives
end LFunctions
end Boundary

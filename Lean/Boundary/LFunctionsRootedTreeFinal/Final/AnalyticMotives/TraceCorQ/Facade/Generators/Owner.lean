import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Facade.Objects.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Generators.Composition.Owner

/-!
# Trace-correspondence generator facade

This file exposes the public `TraceCorQ` wrappers for generator payloads and
identity/composition generators.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes generator certificate ledgers. -/
theorem TraceCorQ.generator_certificateLedger_eq_source_target_path
    (generator : TraceCorQGenerator) :
    generator.certificateLedger =
      ResidueChannelCertificateLedger.append
        generator.source.certificateLedger
        (ResidueChannelCertificateLedger.append
          generator.target.certificateLedger
          generator.pathCertificateLedger) :=
  TraceCorQGenerator.certificateLedger_eq_source_target_path
    generator

/-- The trace-correspondence root exposes generator imported-rectangle counts. -/
theorem TraceCorQ.generator_importedRectangleCount_eq_length
    (generator : TraceCorQGenerator) :
    generator.importedRectangleCount =
      generator.importedRectangles.length :=
  TraceCorQGenerator.importedRectangleCount_eq_length_importedRectangles
    generator

/-- The trace-correspondence root exposes generator payload splitting. -/
theorem TraceCorQ.generator_importedRectangleCount_eq_source_target_path
    (generator : TraceCorQGenerator) :
    generator.importedRectangleCount =
      generator.source.importedRectangleCount +
        (generator.target.importedRectangleCount +
          generator.pathCertificateLedger.importedRectangleCount) :=
  TraceCorQGenerator.importedRectangleCount_eq_source_target_path
    generator

/-- The trace-correspondence root exposes generator imported-rectangle list splitting. -/
theorem TraceCorQ.generator_importedRectangles_eq_source_target_path
    (generator : TraceCorQGenerator) :
    generator.importedRectangles =
      generator.source.importedRectangles ++
        (generator.target.importedRectangles ++
          generator.pathCertificateLedger.importedRectangles) :=
  TraceCorQGenerator.importedRectangles_eq_source_target_path
    generator

/-- The trace-correspondence root exposes generator bookkeeping payload splitting. -/
theorem TraceCorQ.generator_traceBookkeepingCount_eq_source_target_path
    (generator : TraceCorQGenerator) :
    generator.traceBookkeepingCount =
      generator.source.traceBookkeepingCount +
        (generator.target.traceBookkeepingCount +
          generator.pathCertificateLedger.traceBookkeepingCount) :=
  TraceCorQGenerator.traceBookkeepingCount_eq_source_target_path
    generator

/-- The trace-correspondence root exposes generator rewrite-step payload splitting. -/
theorem TraceCorQ.generator_rewriteStepCount_eq_source_target_path
    (generator : TraceCorQGenerator) :
    generator.rewriteStepCount =
      generator.source.rewriteStepCount +
        (generator.target.rewriteStepCount +
          generator.pathCertificateLedger.rewriteStepCount) :=
  TraceCorQGenerator.rewriteStepCount_eq_source_target_path
    generator

/-- The trace-correspondence root exposes identity generators. -/
def TraceCorQ.generator_id
    (object : TraceCorQObject) :
    TraceCorQGenerator :=
  TraceCorQGenerator.id object

/-- The trace-correspondence root exposes generator composition. -/
def TraceCorQ.generator_comp
    (first second : TraceCorQGenerator) :
    TraceCorQGenerator :=
  TraceCorQGenerator.comp first second

/-- The trace-correspondence root exposes identity-generator sources. -/
theorem TraceCorQ.generator_id_source
    (object : TraceCorQObject) :
    (TraceCorQGenerator.id object).source =
      object :=
  TraceCorQGenerator.id_source object

/-- The trace-correspondence root exposes identity-generator targets. -/
theorem TraceCorQ.generator_id_target
    (object : TraceCorQObject) :
    (TraceCorQGenerator.id object).target =
      object :=
  TraceCorQGenerator.id_target object

/-- The trace-correspondence root exposes composition-generator sources. -/
theorem TraceCorQ.generator_comp_source
    (first second : TraceCorQGenerator) :
    (TraceCorQGenerator.comp first second).source =
      first.source :=
  TraceCorQGenerator.comp_source first second

/-- The trace-correspondence root exposes composition-generator targets. -/
theorem TraceCorQ.generator_comp_target
    (first second : TraceCorQGenerator) :
    (TraceCorQGenerator.comp first second).target =
      second.target :=
  TraceCorQGenerator.comp_target first second

/-- The trace-correspondence root exposes composition-generator paths. -/
theorem TraceCorQ.generator_comp_path
    (first second : TraceCorQGenerator) :
    (TraceCorQGenerator.comp first second).path =
      first.path.comp second.path :=
  TraceCorQGenerator.comp_path first second

/-- The trace-correspondence root exposes identity-generator certificate ledgers. -/
theorem TraceCorQ.generator_id_certificateLedger
    (object : TraceCorQObject) :
    (TraceCorQGenerator.id object).certificateLedger =
      (TraceTransport.id object).certificateLedger :=
  TraceCorQGenerator.id_certificateLedger object

/-- The trace-correspondence root exposes identity-generator imported-rectangle counts. -/
theorem TraceCorQ.generator_id_importedRectangleCount
    (object : TraceCorQObject) :
    (TraceCorQGenerator.id object).importedRectangleCount =
      (TraceTransport.id object).importedRectangleCount :=
  TraceCorQGenerator.id_importedRectangleCount object

/-- The trace-correspondence root exposes identity-generator imported rectangles. -/
theorem TraceCorQ.generator_id_importedRectangles
    (object : TraceCorQObject) :
    (TraceCorQGenerator.id object).importedRectangles =
      (TraceTransport.id object).importedRectangles :=
  TraceCorQGenerator.id_importedRectangles object

/-- The trace-correspondence root exposes identity-generator bookkeeping counts. -/
theorem TraceCorQ.generator_id_traceBookkeepingCount
    (object : TraceCorQObject) :
    (TraceCorQGenerator.id object).traceBookkeepingCount =
      (TraceTransport.id object).traceBookkeepingCount :=
  TraceCorQGenerator.id_traceBookkeepingCount object

/-- The trace-correspondence root exposes identity-generator rewrite-step counts. -/
theorem TraceCorQ.generator_id_rewriteStepCount
    (object : TraceCorQObject) :
    (TraceCorQGenerator.id object).rewriteStepCount =
      (TraceTransport.id object).rewriteStepCount :=
  TraceCorQGenerator.id_rewriteStepCount object

/-- The trace-correspondence root exposes identity-generator imported rectangles. -/
theorem TraceCorQ.generator_id_importedRectangles_eq_object_path
    (object : TraceCorQObject) :
    (TraceCorQGenerator.id object).importedRectangles =
      object.importedRectangles ++
        (object.importedRectangles ++
          (ResidueChannelCertificateLedger.ofRewritePath
            (TraceRewritePath.id object.source)).importedRectangles) :=
  TraceCorQGenerator.id_importedRectangles_eq_object_path object

/-- The trace-correspondence root exposes identity-generator rewrite-step payload. -/
theorem TraceCorQ.generator_id_rewriteStepCount_eq_object_path
    (object : TraceCorQObject) :
    (TraceCorQGenerator.id object).rewriteStepCount =
      object.rewriteStepCount +
        (object.rewriteStepCount +
          (ResidueChannelCertificateLedger.ofRewritePath
            (TraceRewritePath.id object.source)).rewriteStepCount) :=
  TraceCorQGenerator.id_rewriteStepCount_eq_object_path object

/-- The trace-correspondence root exposes composition-generator certificate ledgers. -/
theorem TraceCorQ.generator_comp_certificateLedger
    (first second : TraceCorQGenerator) :
    (TraceCorQGenerator.comp first second).certificateLedger =
      (TraceTransport.comp first second).certificateLedger :=
  TraceCorQGenerator.comp_certificateLedger first second

/-- The trace-correspondence root exposes composition-generator imported-rectangle counts. -/
theorem TraceCorQ.generator_comp_importedRectangleCount
    (first second : TraceCorQGenerator) :
    (TraceCorQGenerator.comp first second).importedRectangleCount =
      (TraceTransport.comp first second).importedRectangleCount :=
  TraceCorQGenerator.comp_importedRectangleCount first second

/-- The trace-correspondence root exposes composition-generator imported rectangles. -/
theorem TraceCorQ.generator_comp_importedRectangles
    (first second : TraceCorQGenerator) :
    (TraceCorQGenerator.comp first second).importedRectangles =
      (TraceTransport.comp first second).importedRectangles :=
  TraceCorQGenerator.comp_importedRectangles first second

/-- The trace-correspondence root exposes composition-generator bookkeeping counts. -/
theorem TraceCorQ.generator_comp_traceBookkeepingCount
    (first second : TraceCorQGenerator) :
    (TraceCorQGenerator.comp first second).traceBookkeepingCount =
      (TraceTransport.comp first second).traceBookkeepingCount :=
  TraceCorQGenerator.comp_traceBookkeepingCount first second

/-- The trace-correspondence root exposes composition-generator rewrite-step counts. -/
theorem TraceCorQ.generator_comp_rewriteStepCount
    (first second : TraceCorQGenerator) :
    (TraceCorQGenerator.comp first second).rewriteStepCount =
      (TraceTransport.comp first second).rewriteStepCount :=
  TraceCorQGenerator.comp_rewriteStepCount first second

/-- The trace-correspondence root exposes composition-generator imported rectangles. -/
theorem TraceCorQ.generator_comp_importedRectangles_eq_endpoints_path
    (first second : TraceCorQGenerator) :
    (TraceCorQGenerator.comp first second).importedRectangles =
      first.source.importedRectangles ++
        (second.target.importedRectangles ++
          (ResidueChannelCertificateLedger.ofRewritePath
            (first.path.comp second.path)).importedRectangles) :=
  TraceCorQGenerator.comp_importedRectangles_eq_endpoints_path first second

/-- The trace-correspondence root exposes composition-generator rewrite-step payload. -/
theorem TraceCorQ.generator_comp_rewriteStepCount_eq_endpoints_path
    (first second : TraceCorQGenerator) :
    (TraceCorQGenerator.comp first second).rewriteStepCount =
      first.source.rewriteStepCount +
        (second.target.rewriteStepCount +
          (ResidueChannelCertificateLedger.ofRewritePath
            (first.path.comp second.path)).rewriteStepCount) :=
  TraceCorQGenerator.comp_rewriteStepCount_eq_endpoints_path first second

end AnalyticMotives
end LFunctions
end Boundary

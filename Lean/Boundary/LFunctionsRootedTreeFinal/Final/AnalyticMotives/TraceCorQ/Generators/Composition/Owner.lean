import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Generators.Owner

/-!
# Composition of trace-correspondence generators

This file exposes identity and composition for raw `TraceCorQ` generators.

A generator is a raw trace transport, so these operations are the transport
identity and transport composition under the `TraceCorQGenerator` name.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The identity trace-correspondence generator on an object. -/
def TraceCorQGenerator.id
    (object : TraceCorQObject) :
    TraceCorQGenerator :=
  TraceTransport.id object

/-- Compose trace-correspondence generators by composing their transports. -/
def TraceCorQGenerator.comp
    (first second : TraceCorQGenerator) :
    TraceCorQGenerator :=
  TraceTransport.comp first second

/-- The identity trace-correspondence generator starts at its object. -/
theorem TraceCorQGenerator.id_source
    (object : TraceCorQObject) :
    (TraceCorQGenerator.id object).source =
      object :=
  TraceTransport.id_source object

/-- The identity trace-correspondence generator targets its object. -/
theorem TraceCorQGenerator.id_target
    (object : TraceCorQObject) :
    (TraceCorQGenerator.id object).target =
      object :=
  TraceTransport.id_target object

/-- Composition of trace-correspondence generators starts at the first source. -/
theorem TraceCorQGenerator.comp_source
    (first second : TraceCorQGenerator) :
    (TraceCorQGenerator.comp first second).source =
      first.source :=
  TraceTransport.comp_source first second

/-- Composition of trace-correspondence generators targets the second target. -/
theorem TraceCorQGenerator.comp_target
    (first second : TraceCorQGenerator) :
    (TraceCorQGenerator.comp first second).target =
      second.target :=
  TraceTransport.comp_target first second

/-- Composition of trace-correspondence generators concatenates rewrite paths. -/
theorem TraceCorQGenerator.comp_path
    (first second : TraceCorQGenerator) :
    (TraceCorQGenerator.comp first second).path =
      first.path.comp second.path :=
  TraceTransport.comp_path first second

/-- The identity generator carries the identity transport certificate ledger. -/
theorem TraceCorQGenerator.id_certificateLedger
    (object : TraceCorQObject) :
    (TraceCorQGenerator.id object).certificateLedger =
      (TraceTransport.id object).certificateLedger :=
  rfl

/-- The identity generator carries the identity transport imported payload. -/
theorem TraceCorQGenerator.id_importedRectangleCount
    (object : TraceCorQObject) :
    (TraceCorQGenerator.id object).importedRectangleCount =
      (TraceTransport.id object).importedRectangleCount :=
  rfl

/-- The identity generator exposes the identity transport imported rectangles. -/
theorem TraceCorQGenerator.id_importedRectangles
    (object : TraceCorQObject) :
    (TraceCorQGenerator.id object).importedRectangles =
      (TraceTransport.id object).importedRectangles :=
  rfl

/-- The identity generator carries the identity transport bookkeeping payload. -/
theorem TraceCorQGenerator.id_traceBookkeepingCount
    (object : TraceCorQObject) :
    (TraceCorQGenerator.id object).traceBookkeepingCount =
      (TraceTransport.id object).traceBookkeepingCount :=
  rfl

/-- The identity generator carries the identity transport rewrite-step payload. -/
theorem TraceCorQGenerator.id_rewriteStepCount
    (object : TraceCorQObject) :
    (TraceCorQGenerator.id object).rewriteStepCount =
      (TraceTransport.id object).rewriteStepCount :=
  rfl

/-- The identity generator payload splits through the identity transport endpoints and path. -/
theorem TraceCorQGenerator.id_rewriteStepCount_eq_object_path
    (object : TraceCorQObject) :
    (TraceCorQGenerator.id object).rewriteStepCount =
      object.rewriteStepCount +
        (object.rewriteStepCount +
          (ResidueChannelCertificateLedger.ofRewritePath
            (TraceRewritePath.id object.source)).rewriteStepCount) :=
  TraceTransport.id_rewriteStepCount object

/-- The identity generator exposes endpoint imported rectangles and the identity path. -/
theorem TraceCorQGenerator.id_importedRectangles_eq_object_path
    (object : TraceCorQObject) :
    (TraceCorQGenerator.id object).importedRectangles =
      object.importedRectangles ++
        (object.importedRectangles ++
          (ResidueChannelCertificateLedger.ofRewritePath
            (TraceRewritePath.id object.source)).importedRectangles) :=
  TraceTransport.id_importedRectangles object

/-- Generator composition carries the composed transport certificate ledger. -/
theorem TraceCorQGenerator.comp_certificateLedger
    (first second : TraceCorQGenerator) :
    (TraceCorQGenerator.comp first second).certificateLedger =
      (TraceTransport.comp first second).certificateLedger :=
  rfl

/-- Generator composition carries the composed transport imported payload. -/
theorem TraceCorQGenerator.comp_importedRectangleCount
    (first second : TraceCorQGenerator) :
    (TraceCorQGenerator.comp first second).importedRectangleCount =
      (TraceTransport.comp first second).importedRectangleCount :=
  rfl

/-- Generator composition exposes the composed transport imported rectangles. -/
theorem TraceCorQGenerator.comp_importedRectangles
    (first second : TraceCorQGenerator) :
    (TraceCorQGenerator.comp first second).importedRectangles =
      (TraceTransport.comp first second).importedRectangles :=
  rfl

/-- Generator composition carries the composed transport bookkeeping payload. -/
theorem TraceCorQGenerator.comp_traceBookkeepingCount
    (first second : TraceCorQGenerator) :
    (TraceCorQGenerator.comp first second).traceBookkeepingCount =
      (TraceTransport.comp first second).traceBookkeepingCount :=
  rfl

/-- Generator composition carries the composed transport rewrite-step payload. -/
theorem TraceCorQGenerator.comp_rewriteStepCount
    (first second : TraceCorQGenerator) :
    (TraceCorQGenerator.comp first second).rewriteStepCount =
      (TraceTransport.comp first second).rewriteStepCount :=
  rfl

/-- Generator composition rewrite-step payload is exposed endpoints plus concatenated path. -/
theorem TraceCorQGenerator.comp_rewriteStepCount_eq_endpoints_path
    (first second : TraceCorQGenerator) :
    (TraceCorQGenerator.comp first second).rewriteStepCount =
      first.source.rewriteStepCount +
        (second.target.rewriteStepCount +
          (ResidueChannelCertificateLedger.ofRewritePath
            (first.path.comp second.path)).rewriteStepCount) :=
  TraceTransport.comp_rewriteStepCount first second

/-- Generator composition exposes endpoint imported rectangles and the concatenated path. -/
theorem TraceCorQGenerator.comp_importedRectangles_eq_endpoints_path
    (first second : TraceCorQGenerator) :
    (TraceCorQGenerator.comp first second).importedRectangles =
      first.source.importedRectangles ++
        (second.target.importedRectangles ++
          (ResidueChannelCertificateLedger.ofRewritePath
            (first.path.comp second.path)).importedRectangles) :=
  TraceTransport.comp_importedRectangles first second

end AnalyticMotives
end LFunctions
end Boundary

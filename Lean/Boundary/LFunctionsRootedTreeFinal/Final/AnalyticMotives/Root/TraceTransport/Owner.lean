import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Owner

/-!
# Top-root trace transport

This file exposes the concrete analytic trace-transport calculus under the
top-level `AnalyticMotivesRoot` namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes identity transport sources. -/
theorem AnalyticMotivesRoot.traceTransport_id_source
    (object : TraceTransportObject) :
    (TraceTransport.id object).source =
      object :=
  TraceTransportRoot.id_source
    object

/-- The top root exposes identity transport targets. -/
theorem AnalyticMotivesRoot.traceTransport_id_target
    (object : TraceTransportObject) :
    (TraceTransport.id object).target =
      object :=
  TraceTransportRoot.id_target
    object

/-- The top root exposes identity transport paths. -/
theorem AnalyticMotivesRoot.traceTransport_id_path
    (object : TraceTransportObject) :
    (TraceTransport.id object).path =
      TraceRewritePath.id object.source :=
  TraceTransportRoot.id_path
    object

/-- The top root exposes composite transport sources. -/
theorem AnalyticMotivesRoot.traceTransport_comp_source
    (first second : TraceTransport) :
    (TraceTransport.comp first second).source =
      first.source :=
  TraceTransportRoot.comp_source
    first
    second

/-- The top root exposes composite transport targets. -/
theorem AnalyticMotivesRoot.traceTransport_comp_target
    (first second : TraceTransport) :
    (TraceTransport.comp first second).target =
      second.target :=
  TraceTransportRoot.comp_target
    first
    second

/-- The top root exposes composite transport paths. -/
theorem AnalyticMotivesRoot.traceTransport_comp_path
    (first second : TraceTransport) :
    (TraceTransport.comp first second).path =
      first.path.comp second.path :=
  TraceTransportRoot.comp_path
    first
    second

/-- The top root exposes the canonical transport certificate ledger. -/
theorem AnalyticMotivesRoot.traceTransport_certificateLedger_eq_source_target_path
    (transport : TraceTransport) :
    transport.certificateLedger =
      ResidueChannelCertificateLedger.append
        transport.source.certificateLedger
        (ResidueChannelCertificateLedger.append
          transport.target.certificateLedger
          transport.pathCertificateLedger) :=
  TraceTransportRoot.certificateLedger_eq_source_target_path
    transport

/-- The top root exposes identity path certificate ledgers. -/
theorem AnalyticMotivesRoot.traceTransport_id_pathCertificateLedger
    (object : TraceTransportObject) :
    (TraceTransport.id object).pathCertificateLedger =
      ResidueChannelCertificateLedger.ofRewritePath
        (TraceRewritePath.id object.source) :=
  TraceTransportRoot.id_pathCertificateLedger
    object

/-- The top root exposes identity transport certificate ledgers. -/
theorem AnalyticMotivesRoot.traceTransport_id_certificateLedger
    (object : TraceTransportObject) :
    (TraceTransport.id object).certificateLedger =
      ResidueChannelCertificateLedger.append
        object.certificateLedger
        (ResidueChannelCertificateLedger.append
          object.certificateLedger
          (ResidueChannelCertificateLedger.ofRewritePath
            (TraceRewritePath.id object.source))) :=
  TraceTransportRoot.id_certificateLedger
    object

/-- The top root exposes composite path certificate ledgers. -/
theorem AnalyticMotivesRoot.traceTransport_comp_pathCertificateLedger
    (first second : TraceTransport) :
    (TraceTransport.comp first second).pathCertificateLedger =
      ResidueChannelCertificateLedger.ofRewritePath
        (first.path.comp second.path) :=
  TraceTransportRoot.comp_pathCertificateLedger
    first
    second

/-- The top root exposes composite transport certificate ledgers. -/
theorem AnalyticMotivesRoot.traceTransport_comp_certificateLedger
    (first second : TraceTransport) :
    (TraceTransport.comp first second).certificateLedger =
      ResidueChannelCertificateLedger.append
        first.source.certificateLedger
        (ResidueChannelCertificateLedger.append
          second.target.certificateLedger
          (ResidueChannelCertificateLedger.ofRewritePath
            (first.path.comp second.path))) :=
  TraceTransportRoot.comp_certificateLedger
    first
    second

/-- The top root exposes the transport imported-rectangle count split. -/
theorem AnalyticMotivesRoot.traceTransport_importedRectangleCount_eq_source_target_path
    (transport : TraceTransport) :
    transport.importedRectangleCount =
      transport.source.importedRectangleCount +
        (transport.target.importedRectangleCount +
          transport.pathCertificateLedger.importedRectangleCount) :=
  TraceTransportRoot.importedRectangleCount_eq_source_target_path
    transport

/-- The top root exposes the transport imported-rectangle list split. -/
theorem AnalyticMotivesRoot.traceTransport_importedRectangles_eq_source_target_path
    (transport : TraceTransport) :
    transport.importedRectangles =
      transport.source.importedRectangles ++
        (transport.target.importedRectangles ++
          transport.pathCertificateLedger.importedRectangles) :=
  TraceTransportRoot.importedRectangles_eq_source_target_path
    transport

/-- The top root exposes the transport imported-rectangle count as list length. -/
theorem AnalyticMotivesRoot.traceTransport_importedRectangleCount_eq_length
    (transport : TraceTransport) :
    transport.importedRectangleCount =
      transport.importedRectangles.length :=
  TraceTransportRoot.importedRectangleCount_eq_length
    transport

/-- The top root exposes the transport trace-bookkeeping split. -/
theorem AnalyticMotivesRoot.traceTransport_traceBookkeepingCount_eq_source_target_path
    (transport : TraceTransport) :
    transport.traceBookkeepingCount =
      transport.source.traceBookkeepingCount +
        (transport.target.traceBookkeepingCount +
          transport.pathCertificateLedger.traceBookkeepingCount) :=
  TraceTransportRoot.traceBookkeepingCount_eq_source_target_path
    transport

/-- The top root exposes the transport rewrite-step split. -/
theorem AnalyticMotivesRoot.traceTransport_rewriteStepCount_eq_source_target_path
    (transport : TraceTransport) :
    transport.rewriteStepCount =
      transport.source.rewriteStepCount +
        (transport.target.rewriteStepCount +
          transport.pathCertificateLedger.rewriteStepCount) :=
  TraceTransportRoot.rewriteStepCount_eq_source_target_path
    transport

/-- The top root exposes finite-chain imported-rectangle count normal forms. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainDefectImportedRectangleCount_eq_sum
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect chain).importedRectangleCount =
      TraceTransport.finiteChainDefectImportedRectangleCount chain :=
  TraceTransportRoot.finiteChainAssociatedGradedDefect_importedRectangleCount_eq_sum
    chain

/-- The top root exposes finite-chain imported-rectangle list normal forms. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainDefectImportedRectangles_eq_sum
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect chain).importedRectangles =
      TraceTransport.finiteChainDefectImportedRectangles chain :=
  TraceTransportRoot.finiteChainAssociatedGradedDefect_importedRectangles_eq_sum
    chain

/-- The top root exposes finite-chain bookkeeping count normal forms. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainDefectTraceBookkeepingCount_eq_sum
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect chain).traceBookkeepingCount =
      TraceTransport.finiteChainDefectTraceBookkeepingCount chain :=
  TraceTransportRoot.finiteChainAssociatedGradedDefect_traceBookkeepingCount_eq_sum
    chain

/-- The top root exposes finite-chain rewrite-step count normal forms. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainDefectRewriteStepCount_eq_sum
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect chain).rewriteStepCount =
      TraceTransport.finiteChainDefectRewriteStepCount chain :=
  TraceTransportRoot.finiteChainAssociatedGradedDefect_rewriteStepCount_eq_sum
    chain

/-- The top root exposes finite-chain associated-graded append laws. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainAssociatedGradedDefect_append
    (first second : List TraceTransport) :
    TraceTransport.finiteChainAssociatedGradedDefect
      (first ++ second) =
      ResidueChannelCertificateLedger.append
        (TraceTransport.finiteChainAssociatedGradedDefect first)
        (TraceTransport.finiteChainAssociatedGradedDefect second) :=
  TraceTransportRoot.finiteChainAssociatedGradedDefect_append
    first
    second

/-- The top root exposes finite-chain associated-graded append rewrite payloads. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainAssociatedGradedDefect_append_rewriteStepCount
    (first second : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (first ++ second)).rewriteStepCount =
      (TraceTransport.finiteChainAssociatedGradedDefect first).rewriteStepCount +
        (TraceTransport.finiteChainAssociatedGradedDefect second).rewriteStepCount :=
  TraceTransportRoot.finiteChainAssociatedGradedDefect_append_rewriteStepCount
    first
    second

/-- The top root exposes finite-chain associated-graded append rectangle counts. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainAssociatedGradedDefect_append_importedRectangleCount
    (first second : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (first ++ second)).importedRectangleCount =
      (TraceTransport.finiteChainAssociatedGradedDefect first).importedRectangleCount +
        (TraceTransport.finiteChainAssociatedGradedDefect second).importedRectangleCount :=
  TraceTransportRoot.finiteChainAssociatedGradedDefect_append_importedRectangleCount
    first
    second

/-- The top root exposes finite-chain associated-graded append rectangle lists. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainAssociatedGradedDefect_append_importedRectangles
    (first second : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (first ++ second)).importedRectangles =
      (TraceTransport.finiteChainAssociatedGradedDefect first).importedRectangles ++
        (TraceTransport.finiteChainAssociatedGradedDefect second).importedRectangles :=
  TraceTransportRoot.finiteChainAssociatedGradedDefect_append_importedRectangles
    first
    second

/-- The top root exposes finite-chain associated-graded append bookkeeping payloads. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainAssociatedGradedDefect_append_traceBookkeepingCount
    (first second : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (first ++ second)).traceBookkeepingCount =
      (TraceTransport.finiteChainAssociatedGradedDefect first).traceBookkeepingCount +
        (TraceTransport.finiteChainAssociatedGradedDefect second).traceBookkeepingCount :=
  TraceTransportRoot.finiteChainAssociatedGradedDefect_append_traceBookkeepingCount
    first
    second

/-- The top root exposes finite-chain associated-graded associativity. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainAssociatedGradedDefect_assoc
    (first second third : List TraceTransport) :
    TraceTransport.finiteChainAssociatedGradedDefect
      ((first ++ second) ++ third) =
      ResidueChannelCertificateLedger.append
        (TraceTransport.finiteChainAssociatedGradedDefect first)
        (ResidueChannelCertificateLedger.append
          (TraceTransport.finiteChainAssociatedGradedDefect second)
          (TraceTransport.finiteChainAssociatedGradedDefect third)) :=
  TraceTransportRoot.finiteChainAssociatedGradedDefect_append_append_assoc
    first
    second
    third

/-- The top root exposes associated-graded associativity rewrite payloads. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainAssociatedGradedDefect_assoc_rewriteStepCount
    (first second third : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ((first ++ second) ++ third)).rewriteStepCount =
      (TraceTransport.finiteChainAssociatedGradedDefect first).rewriteStepCount +
        ((TraceTransport.finiteChainAssociatedGradedDefect second).rewriteStepCount +
          (TraceTransport.finiteChainAssociatedGradedDefect third).rewriteStepCount) :=
  TraceTransportRoot.finiteChainAssociatedGradedDefect_assoc_rewriteStepCount
    first
    second
    third

/-- The top root exposes associated-graded associativity rectangle counts. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainAssociatedGradedDefect_assoc_importedRectangleCount
    (first second third : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ((first ++ second) ++ third)).importedRectangleCount =
      (TraceTransport.finiteChainAssociatedGradedDefect first).importedRectangleCount +
        ((TraceTransport.finiteChainAssociatedGradedDefect second).importedRectangleCount +
          (TraceTransport.finiteChainAssociatedGradedDefect third).importedRectangleCount) :=
  TraceTransportRoot.finiteChainAssociatedGradedDefect_assoc_importedRectangleCount
    first
    second
    third

/-- The top root exposes associated-graded associativity rectangle lists. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainAssociatedGradedDefect_assoc_importedRectangles
    (first second third : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ((first ++ second) ++ third)).importedRectangles =
      (TraceTransport.finiteChainAssociatedGradedDefect first).importedRectangles ++
        ((TraceTransport.finiteChainAssociatedGradedDefect second).importedRectangles ++
          (TraceTransport.finiteChainAssociatedGradedDefect third).importedRectangles) :=
  TraceTransportRoot.finiteChainAssociatedGradedDefect_assoc_importedRectangles
    first
    second
    third

/-- The top root exposes associated-graded associativity bookkeeping payloads. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainAssociatedGradedDefect_assoc_traceBookkeepingCount
    (first second third : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ((first ++ second) ++ third)).traceBookkeepingCount =
      (TraceTransport.finiteChainAssociatedGradedDefect first).traceBookkeepingCount +
        ((TraceTransport.finiteChainAssociatedGradedDefect second).traceBookkeepingCount +
          (TraceTransport.finiteChainAssociatedGradedDefect third).traceBookkeepingCount) :=
  TraceTransportRoot.finiteChainAssociatedGradedDefect_assoc_traceBookkeepingCount
    first
    second
    third

/-- The top root exposes finite-chain associated-graded rebracketing. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainAssociatedGradedDefect_rebracket
    (first second third : List TraceTransport) :
    TraceTransport.finiteChainAssociatedGradedDefect
      ((first ++ second) ++ third) =
      TraceTransport.finiteChainAssociatedGradedDefect
        (first ++ (second ++ third)) :=
  TraceTransportRoot.finiteChainAssociatedGradedDefect_rebracket
    first
    second
    third

/-- The top root exposes associated-graded rebracketing rectangle counts. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainAssociatedGradedDefect_rebracket_importedRectangleCount
    (first second third : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ((first ++ second) ++ third)).importedRectangleCount =
      (TraceTransport.finiteChainAssociatedGradedDefect
        (first ++ (second ++ third))).importedRectangleCount :=
  TraceTransportRoot.finiteChainAssociatedGradedDefect_rebracket_importedRectangleCount
    first
    second
    third

/-- The top root exposes associated-graded rebracketing rectangle lists. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainAssociatedGradedDefect_rebracket_importedRectangles
    (first second third : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ((first ++ second) ++ third)).importedRectangles =
      (TraceTransport.finiteChainAssociatedGradedDefect
        (first ++ (second ++ third))).importedRectangles :=
  TraceTransportRoot.finiteChainAssociatedGradedDefect_rebracket_importedRectangles
    first
    second
    third

/-- The top root exposes associated-graded rebracketing bookkeeping payloads. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainAssociatedGradedDefect_rebracket_traceBookkeepingCount
    (first second third : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ((first ++ second) ++ third)).traceBookkeepingCount =
      (TraceTransport.finiteChainAssociatedGradedDefect
        (first ++ (second ++ third))).traceBookkeepingCount :=
  TraceTransportRoot.finiteChainAssociatedGradedDefect_rebracket_traceBookkeepingCount
    first
    second
    third

/-- The top root exposes associated-graded rebracketing rewrite payloads. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainAssociatedGradedDefect_rebracket_rewriteStepCount
    (first second third : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ((first ++ second) ++ third)).rewriteStepCount =
      (TraceTransport.finiteChainAssociatedGradedDefect
        (first ++ (second ++ third))).rewriteStepCount :=
  TraceTransportRoot.finiteChainAssociatedGradedDefect_rebracket_rewriteStepCount
    first
    second
    third

/-- The top root exposes finite-chain associated-graded left units. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainAssociatedGradedDefect_empty_append
    (chain : List TraceTransport) :
    TraceTransport.finiteChainAssociatedGradedDefect ([] ++ chain) =
      TraceTransport.finiteChainAssociatedGradedDefect chain :=
  TraceTransportRoot.finiteChainAssociatedGradedDefect_empty_append
    chain

/-- The top root exposes finite-chain associated-graded right units. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainAssociatedGradedDefect_append_empty
    (chain : List TraceTransport) :
    TraceTransport.finiteChainAssociatedGradedDefect (chain ++ []) =
      TraceTransport.finiteChainAssociatedGradedDefect chain :=
  TraceTransportRoot.finiteChainAssociatedGradedDefect_append_empty
    chain

/-- The top root exposes associated-graded left-unit rectangle counts. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainAssociatedGradedDefect_empty_append_importedRectangleCount
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ([] ++ chain)).importedRectangleCount =
      (TraceTransport.finiteChainAssociatedGradedDefect chain).importedRectangleCount :=
  TraceTransportRoot.finiteChainAssociatedGradedDefect_empty_append_importedRectangleCount
    chain

/-- The top root exposes associated-graded right-unit rectangle counts. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainAssociatedGradedDefect_append_empty_importedRectangleCount
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (chain ++ [])).importedRectangleCount =
      (TraceTransport.finiteChainAssociatedGradedDefect chain).importedRectangleCount :=
  TraceTransportRoot.finiteChainAssociatedGradedDefect_append_empty_importedRectangleCount
    chain

/-- The top root exposes associated-graded left-unit rectangle lists. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainAssociatedGradedDefect_empty_append_importedRectangles
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ([] ++ chain)).importedRectangles =
      (TraceTransport.finiteChainAssociatedGradedDefect chain).importedRectangles :=
  TraceTransportRoot.finiteChainAssociatedGradedDefect_empty_append_importedRectangles
    chain

/-- The top root exposes associated-graded right-unit rectangle lists. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainAssociatedGradedDefect_append_empty_importedRectangles
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (chain ++ [])).importedRectangles =
      (TraceTransport.finiteChainAssociatedGradedDefect chain).importedRectangles :=
  TraceTransportRoot.finiteChainAssociatedGradedDefect_append_empty_importedRectangles
    chain

/-- The top root exposes associated-graded left-unit bookkeeping payloads. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainAssociatedGradedDefect_empty_append_traceBookkeepingCount
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ([] ++ chain)).traceBookkeepingCount =
      (TraceTransport.finiteChainAssociatedGradedDefect chain).traceBookkeepingCount :=
  TraceTransportRoot.finiteChainAssociatedGradedDefect_empty_append_traceBookkeepingCount
    chain

/-- The top root exposes associated-graded right-unit bookkeeping payloads. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainAssociatedGradedDefect_append_empty_traceBookkeepingCount
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (chain ++ [])).traceBookkeepingCount =
      (TraceTransport.finiteChainAssociatedGradedDefect chain).traceBookkeepingCount :=
  TraceTransportRoot.finiteChainAssociatedGradedDefect_append_empty_traceBookkeepingCount
    chain

/-- The top root exposes associated-graded left-unit rewrite payloads. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainAssociatedGradedDefect_empty_append_rewriteStepCount
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ([] ++ chain)).rewriteStepCount =
      (TraceTransport.finiteChainAssociatedGradedDefect chain).rewriteStepCount :=
  TraceTransportRoot.finiteChainAssociatedGradedDefect_empty_append_rewriteStepCount
    chain

/-- The top root exposes associated-graded right-unit rewrite payloads. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainAssociatedGradedDefect_append_empty_rewriteStepCount
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (chain ++ [])).rewriteStepCount =
      (TraceTransport.finiteChainAssociatedGradedDefect chain).rewriteStepCount :=
  TraceTransportRoot.finiteChainAssociatedGradedDefect_append_empty_rewriteStepCount
    chain

/-- The top root exposes finite-chain imported-rectangle count append laws. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainDefectImportedRectangleCount_append
    (first second : List TraceTransport) :
    TraceTransport.finiteChainDefectImportedRectangleCount (first ++ second) =
      TraceTransport.finiteChainDefectImportedRectangleCount first +
        TraceTransport.finiteChainDefectImportedRectangleCount second :=
  TraceTransportRoot.finiteChainDefectImportedRectangleCount_append
    first
    second

/-- The top root exposes finite-chain imported-rectangle list append laws. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainDefectImportedRectangles_append
    (first second : List TraceTransport) :
    TraceTransport.finiteChainDefectImportedRectangles (first ++ second) =
      TraceTransport.finiteChainDefectImportedRectangles first ++
        TraceTransport.finiteChainDefectImportedRectangles second :=
  TraceTransportRoot.finiteChainDefectImportedRectangles_append
    first
    second

/-- The top root exposes finite-chain bookkeeping count append laws. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainDefectTraceBookkeepingCount_append
    (first second : List TraceTransport) :
    TraceTransport.finiteChainDefectTraceBookkeepingCount (first ++ second) =
      TraceTransport.finiteChainDefectTraceBookkeepingCount first +
        TraceTransport.finiteChainDefectTraceBookkeepingCount second :=
  TraceTransportRoot.finiteChainDefectTraceBookkeepingCount_append
    first
    second

/-- The top root exposes finite-chain rewrite-step count append laws. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainDefectRewriteStepCount_append
    (first second : List TraceTransport) :
    TraceTransport.finiteChainDefectRewriteStepCount (first ++ second) =
      TraceTransport.finiteChainDefectRewriteStepCount first +
        TraceTransport.finiteChainDefectRewriteStepCount second :=
  TraceTransportRoot.finiteChainDefectRewriteStepCount_append
    first
    second

/-- The top root exposes finite-chain imported-rectangle count associativity. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainDefectImportedRectangleCount_assoc
    (first second third : List TraceTransport) :
    TraceTransport.finiteChainDefectImportedRectangleCount ((first ++ second) ++ third) =
      TraceTransport.finiteChainDefectImportedRectangleCount first +
        (TraceTransport.finiteChainDefectImportedRectangleCount second +
          TraceTransport.finiteChainDefectImportedRectangleCount third) :=
  TraceTransportRoot.finiteChainDefectImportedRectangleCount_append_append_assoc
    first
    second
    third

/-- The top root exposes finite-chain imported-rectangle count rebracketing. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainDefectImportedRectangleCount_rebracket
    (first second third : List TraceTransport) :
    TraceTransport.finiteChainDefectImportedRectangleCount ((first ++ second) ++ third) =
      TraceTransport.finiteChainDefectImportedRectangleCount (first ++ (second ++ third)) :=
  TraceTransportRoot.finiteChainDefectImportedRectangleCount_rebracket
    first
    second
    third

/-- The top root exposes finite-chain imported-rectangle list associativity. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainDefectImportedRectangles_assoc
    (first second third : List TraceTransport) :
    TraceTransport.finiteChainDefectImportedRectangles ((first ++ second) ++ third) =
      TraceTransport.finiteChainDefectImportedRectangles first ++
        (TraceTransport.finiteChainDefectImportedRectangles second ++
          TraceTransport.finiteChainDefectImportedRectangles third) :=
  TraceTransportRoot.finiteChainDefectImportedRectangles_append_append_assoc
    first
    second
    third

/-- The top root exposes finite-chain imported-rectangle list rebracketing. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainDefectImportedRectangles_rebracket
    (first second third : List TraceTransport) :
    TraceTransport.finiteChainDefectImportedRectangles ((first ++ second) ++ third) =
      TraceTransport.finiteChainDefectImportedRectangles (first ++ (second ++ third)) :=
  TraceTransportRoot.finiteChainDefectImportedRectangles_rebracket
    first
    second
    third

/-- The top root exposes finite-chain trace-bookkeeping count associativity. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainDefectTraceBookkeepingCount_assoc
    (first second third : List TraceTransport) :
    TraceTransport.finiteChainDefectTraceBookkeepingCount ((first ++ second) ++ third) =
      TraceTransport.finiteChainDefectTraceBookkeepingCount first +
        (TraceTransport.finiteChainDefectTraceBookkeepingCount second +
          TraceTransport.finiteChainDefectTraceBookkeepingCount third) :=
  TraceTransportRoot.finiteChainDefectTraceBookkeepingCount_append_append_assoc
    first
    second
    third

/-- The top root exposes finite-chain trace-bookkeeping count rebracketing. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainDefectTraceBookkeepingCount_rebracket
    (first second third : List TraceTransport) :
    TraceTransport.finiteChainDefectTraceBookkeepingCount ((first ++ second) ++ third) =
      TraceTransport.finiteChainDefectTraceBookkeepingCount (first ++ (second ++ third)) :=
  TraceTransportRoot.finiteChainDefectTraceBookkeepingCount_rebracket
    first
    second
    third

/-- The top root exposes finite-chain rewrite-step count associativity. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainDefectRewriteStepCount_assoc
    (first second third : List TraceTransport) :
    TraceTransport.finiteChainDefectRewriteStepCount ((first ++ second) ++ third) =
      TraceTransport.finiteChainDefectRewriteStepCount first +
        (TraceTransport.finiteChainDefectRewriteStepCount second +
          TraceTransport.finiteChainDefectRewriteStepCount third) :=
  TraceTransportRoot.finiteChainDefectRewriteStepCount_append_append_assoc
    first
    second
    third

/-- The top root exposes finite-chain rewrite-step count rebracketing. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainDefectRewriteStepCount_rebracket
    (first second third : List TraceTransport) :
    TraceTransport.finiteChainDefectRewriteStepCount ((first ++ second) ++ third) =
      TraceTransport.finiteChainDefectRewriteStepCount (first ++ (second ++ third)) :=
  TraceTransportRoot.finiteChainDefectRewriteStepCount_rebracket
    first
    second
    third

/-- The top root exposes finite-chain imported-rectangle count left units. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainDefectImportedRectangleCount_empty_append
    (chain : List TraceTransport) :
    TraceTransport.finiteChainDefectImportedRectangleCount ([] ++ chain) =
      TraceTransport.finiteChainDefectImportedRectangleCount chain :=
  TraceTransportRoot.finiteChainDefectImportedRectangleCount_empty_append
    chain

/-- The top root exposes finite-chain imported-rectangle count right units. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainDefectImportedRectangleCount_append_empty
    (chain : List TraceTransport) :
    TraceTransport.finiteChainDefectImportedRectangleCount (chain ++ []) =
      TraceTransport.finiteChainDefectImportedRectangleCount chain :=
  TraceTransportRoot.finiteChainDefectImportedRectangleCount_append_empty
    chain

/-- The top root exposes finite-chain imported-rectangle list left units. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainDefectImportedRectangles_empty_append
    (chain : List TraceTransport) :
    TraceTransport.finiteChainDefectImportedRectangles ([] ++ chain) =
      TraceTransport.finiteChainDefectImportedRectangles chain :=
  TraceTransportRoot.finiteChainDefectImportedRectangles_empty_append
    chain

/-- The top root exposes finite-chain imported-rectangle list right units. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainDefectImportedRectangles_append_empty
    (chain : List TraceTransport) :
    TraceTransport.finiteChainDefectImportedRectangles (chain ++ []) =
      TraceTransport.finiteChainDefectImportedRectangles chain :=
  TraceTransportRoot.finiteChainDefectImportedRectangles_append_empty
    chain

/-- The top root exposes finite-chain bookkeeping count left units. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainDefectTraceBookkeepingCount_empty_append
    (chain : List TraceTransport) :
    TraceTransport.finiteChainDefectTraceBookkeepingCount ([] ++ chain) =
      TraceTransport.finiteChainDefectTraceBookkeepingCount chain :=
  TraceTransportRoot.finiteChainDefectTraceBookkeepingCount_empty_append
    chain

/-- The top root exposes finite-chain bookkeeping count right units. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainDefectTraceBookkeepingCount_append_empty
    (chain : List TraceTransport) :
    TraceTransport.finiteChainDefectTraceBookkeepingCount (chain ++ []) =
      TraceTransport.finiteChainDefectTraceBookkeepingCount chain :=
  TraceTransportRoot.finiteChainDefectTraceBookkeepingCount_append_empty
    chain

/-- The top root exposes finite-chain rewrite-step count left units. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainDefectRewriteStepCount_empty_append
    (chain : List TraceTransport) :
    TraceTransport.finiteChainDefectRewriteStepCount ([] ++ chain) =
      TraceTransport.finiteChainDefectRewriteStepCount chain :=
  TraceTransportRoot.finiteChainDefectRewriteStepCount_empty_append
    chain

/-- The top root exposes finite-chain rewrite-step count right units. -/
theorem AnalyticMotivesRoot.traceTransport_finiteChainDefectRewriteStepCount_append_empty
    (chain : List TraceTransport) :
    TraceTransport.finiteChainDefectRewriteStepCount (chain ++ []) =
      TraceTransport.finiteChainDefectRewriteStepCount chain :=
  TraceTransportRoot.finiteChainDefectRewriteStepCount_append_empty
    chain

end AnalyticMotives
end LFunctions
end Boundary

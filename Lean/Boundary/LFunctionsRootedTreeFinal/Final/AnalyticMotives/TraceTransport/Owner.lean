import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Core.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Certificates.Coherence.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Defects.Coherence.Owner

/-!
# Trace transport

This directory owns the analytic transport calculus from presentations to
categorical morphisms, including concrete defect ledgers carried by rewrite
paths and associated-graded defect filtrations for two-step and finite chains,
with append compatibility, three-block associativity, and rebracketing
invariance, together with binary- and triple-composite finite-chain bridges.
The triple bridge includes left- and right-associated specialized payload
formulas, including singleton-normalized defect-ledger formulas.
Finite-chain defect filtrations also expose empty-chain unit laws.
Recursive payload-sum normal forms and their append, associativity,
rebracketing, and empty-chain unit laws are available for finite chains,
together with direct associated-graded append and associativity payload normal
forms, plus right-bracketed and unit associated-graded payload normal forms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-transport root exposes identity transport sources. -/
theorem TraceTransportRoot.id_source
    (object : TraceTransportObject) :
    (TraceTransport.id object).source =
      object :=
  TraceTransport.id_source
    object

/-- The trace-transport root exposes identity transport targets. -/
theorem TraceTransportRoot.id_target
    (object : TraceTransportObject) :
    (TraceTransport.id object).target =
      object :=
  TraceTransport.id_target
    object

/-- The trace-transport root exposes identity transport paths. -/
theorem TraceTransportRoot.id_path
    (object : TraceTransportObject) :
    (TraceTransport.id object).path =
      TraceRewritePath.id object.source :=
  TraceTransport.id_path
    object

/-- The trace-transport root exposes composition sources. -/
theorem TraceTransportRoot.comp_source
    (first second : TraceTransport) :
    (TraceTransport.comp first second).source =
      first.source :=
  TraceTransport.comp_source
    first
    second

/-- The trace-transport root exposes composition targets. -/
theorem TraceTransportRoot.comp_target
    (first second : TraceTransport) :
    (TraceTransport.comp first second).target =
      second.target :=
  TraceTransport.comp_target
    first
    second

/-- The trace-transport root exposes composition paths. -/
theorem TraceTransportRoot.comp_path
    (first second : TraceTransport) :
    (TraceTransport.comp first second).path =
      first.path.comp second.path :=
  TraceTransport.comp_path
    first
    second

/-- The trace-transport root exposes canonical certificate ledgers. -/
theorem TraceTransportRoot.certificateLedger_eq_source_target_path
    (transport : TraceTransport) :
    transport.certificateLedger =
      ResidueChannelCertificateLedger.append
        transport.source.certificateLedger
        (ResidueChannelCertificateLedger.append
          transport.target.certificateLedger
          transport.pathCertificateLedger) :=
  TraceTransport.certificateLedger_eq_source_target_path
    transport

/-- The trace-transport root exposes identity path certificate ledgers. -/
theorem TraceTransportRoot.id_pathCertificateLedger
    (object : TraceTransportObject) :
    (TraceTransport.id object).pathCertificateLedger =
      ResidueChannelCertificateLedger.ofRewritePath
        (TraceRewritePath.id object.source) :=
  TraceTransport.id_pathCertificateLedger
    object

/-- The trace-transport root exposes identity transport certificate ledgers. -/
theorem TraceTransportRoot.id_certificateLedger
    (object : TraceTransportObject) :
    (TraceTransport.id object).certificateLedger =
      ResidueChannelCertificateLedger.append
        object.certificateLedger
        (ResidueChannelCertificateLedger.append
          object.certificateLedger
          (ResidueChannelCertificateLedger.ofRewritePath
            (TraceRewritePath.id object.source))) :=
  TraceTransport.id_certificateLedger
    object

/-- The trace-transport root exposes composite path certificate ledgers. -/
theorem TraceTransportRoot.comp_pathCertificateLedger
    (first second : TraceTransport) :
    (TraceTransport.comp first second).pathCertificateLedger =
      ResidueChannelCertificateLedger.ofRewritePath
        (first.path.comp second.path) :=
  TraceTransport.comp_pathCertificateLedger
    first
    second

/-- The trace-transport root exposes composite transport certificate ledgers. -/
theorem TraceTransportRoot.comp_certificateLedger
    (first second : TraceTransport) :
    (TraceTransport.comp first second).certificateLedger =
      ResidueChannelCertificateLedger.append
        first.source.certificateLedger
        (ResidueChannelCertificateLedger.append
          second.target.certificateLedger
          (ResidueChannelCertificateLedger.ofRewritePath
            (first.path.comp second.path))) :=
  TraceTransport.comp_certificateLedger
    first
    second

/-- The trace-transport root exposes imported-rectangle count as rectangle-list length. -/
theorem TraceTransportRoot.importedRectangleCount_eq_length
    (transport : TraceTransport) :
    transport.importedRectangleCount =
      transport.importedRectangles.length :=
  TraceTransport.importedRectangleCount_eq_length_importedRectangles
    transport

/-- The trace-transport root exposes imported-rectangle payload splitting. -/
theorem TraceTransportRoot.importedRectangleCount_eq_source_target_path
    (transport : TraceTransport) :
    transport.importedRectangleCount =
      transport.source.importedRectangleCount +
        (transport.target.importedRectangleCount +
          transport.pathCertificateLedger.importedRectangleCount) :=
  TraceTransport.importedRectangleCount_eq_source_target_path
    transport

/-- The trace-transport root exposes imported-rectangle list splitting. -/
theorem TraceTransportRoot.importedRectangles_eq_source_target_path
    (transport : TraceTransport) :
    transport.importedRectangles =
      transport.source.importedRectangles ++
        (transport.target.importedRectangles ++
          transport.pathCertificateLedger.importedRectangles) :=
  TraceTransport.importedRectangles_eq_source_target_path
    transport

/-- The trace-transport root exposes trace-bookkeeping payload splitting. -/
theorem TraceTransportRoot.traceBookkeepingCount_eq_source_target_path
    (transport : TraceTransport) :
    transport.traceBookkeepingCount =
      transport.source.traceBookkeepingCount +
        (transport.target.traceBookkeepingCount +
          transport.pathCertificateLedger.traceBookkeepingCount) :=
  TraceTransport.traceBookkeepingCount_eq_source_target_path
    transport

/-- The trace-transport root exposes rewrite-step payload splitting. -/
theorem TraceTransportRoot.rewriteStepCount_eq_source_target_path
    (transport : TraceTransport) :
    transport.rewriteStepCount =
      transport.source.rewriteStepCount +
        (transport.target.rewriteStepCount +
          transport.pathCertificateLedger.rewriteStepCount) :=
  TraceTransport.rewriteStepCount_eq_source_target_path
    transport

/-- The trace-transport root exposes finite-chain imported-rectangle count normal forms. -/
theorem TraceTransportRoot.finiteChainAssociatedGradedDefect_importedRectangleCount_eq_sum
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect chain).importedRectangleCount =
      TraceTransport.finiteChainDefectImportedRectangleCount chain :=
  TraceTransport.finiteChainAssociatedGradedDefect_importedRectangleCount_eq_sum
    chain

/-- The trace-transport root exposes finite-chain imported-rectangle list normal forms. -/
theorem TraceTransportRoot.finiteChainAssociatedGradedDefect_importedRectangles_eq_sum
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect chain).importedRectangles =
      TraceTransport.finiteChainDefectImportedRectangles chain :=
  TraceTransport.finiteChainAssociatedGradedDefect_importedRectangles_eq_sum
    chain

/-- The trace-transport root exposes finite-chain bookkeeping count normal forms. -/
theorem TraceTransportRoot.finiteChainAssociatedGradedDefect_traceBookkeepingCount_eq_sum
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect chain).traceBookkeepingCount =
      TraceTransport.finiteChainDefectTraceBookkeepingCount chain :=
  TraceTransport.finiteChainAssociatedGradedDefect_traceBookkeepingCount_eq_sum
    chain

/-- The trace-transport root exposes finite-chain rewrite-step count normal forms. -/
theorem TraceTransportRoot.finiteChainAssociatedGradedDefect_rewriteStepCount_eq_sum
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect chain).rewriteStepCount =
      TraceTransport.finiteChainDefectRewriteStepCount chain :=
  TraceTransport.finiteChainAssociatedGradedDefect_rewriteStepCount_eq_sum
    chain

/-- The trace-transport root exposes finite-chain associated-graded append laws. -/
theorem TraceTransportRoot.finiteChainAssociatedGradedDefect_append
    (first second : List TraceTransport) :
    TraceTransport.finiteChainAssociatedGradedDefect
      (first ++ second) =
      ResidueChannelCertificateLedger.append
        (TraceTransport.finiteChainAssociatedGradedDefect first)
        (TraceTransport.finiteChainAssociatedGradedDefect second) :=
  TraceTransport.finiteChainAssociatedGradedDefect_append
    first
    second

/-- The trace-transport root exposes finite-chain associated-graded append rewrite payloads. -/
theorem TraceTransportRoot.finiteChainAssociatedGradedDefect_append_rewriteStepCount
    (first second : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (first ++ second)).rewriteStepCount =
      (TraceTransport.finiteChainAssociatedGradedDefect first).rewriteStepCount +
        (TraceTransport.finiteChainAssociatedGradedDefect second).rewriteStepCount :=
  TraceTransport.finiteChainAssociatedGradedDefect_append_rewriteStepCount
    first
    second

/-- The trace-transport root exposes finite-chain associated-graded append rectangle counts. -/
theorem TraceTransportRoot.finiteChainAssociatedGradedDefect_append_importedRectangleCount
    (first second : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (first ++ second)).importedRectangleCount =
      (TraceTransport.finiteChainAssociatedGradedDefect first).importedRectangleCount +
        (TraceTransport.finiteChainAssociatedGradedDefect second).importedRectangleCount :=
  TraceTransport.finiteChainAssociatedGradedDefect_append_importedRectangleCount
    first
    second

/-- The trace-transport root exposes finite-chain associated-graded append rectangle lists. -/
theorem TraceTransportRoot.finiteChainAssociatedGradedDefect_append_importedRectangles
    (first second : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (first ++ second)).importedRectangles =
      (TraceTransport.finiteChainAssociatedGradedDefect first).importedRectangles ++
        (TraceTransport.finiteChainAssociatedGradedDefect second).importedRectangles :=
  TraceTransport.finiteChainAssociatedGradedDefect_append_importedRectangles
    first
    second

/-- The trace-transport root exposes finite-chain associated-graded append bookkeeping payloads. -/
theorem TraceTransportRoot.finiteChainAssociatedGradedDefect_append_traceBookkeepingCount
    (first second : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (first ++ second)).traceBookkeepingCount =
      (TraceTransport.finiteChainAssociatedGradedDefect first).traceBookkeepingCount +
        (TraceTransport.finiteChainAssociatedGradedDefect second).traceBookkeepingCount :=
  TraceTransport.finiteChainAssociatedGradedDefect_append_traceBookkeepingCount
    first
    second

/-- The trace-transport root exposes finite-chain associated-graded associativity. -/
theorem TraceTransportRoot.finiteChainAssociatedGradedDefect_append_append_assoc
    (first second third : List TraceTransport) :
    TraceTransport.finiteChainAssociatedGradedDefect
      ((first ++ second) ++ third) =
      ResidueChannelCertificateLedger.append
        (TraceTransport.finiteChainAssociatedGradedDefect first)
        (ResidueChannelCertificateLedger.append
          (TraceTransport.finiteChainAssociatedGradedDefect second)
          (TraceTransport.finiteChainAssociatedGradedDefect third)) :=
  TraceTransport.finiteChainAssociatedGradedDefect_append_append_assoc
    first
    second
    third

/-- The trace-transport root exposes associated-graded associativity rewrite payloads. -/
theorem TraceTransportRoot.finiteChainAssociatedGradedDefect_assoc_rewriteStepCount
    (first second third : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ((first ++ second) ++ third)).rewriteStepCount =
      (TraceTransport.finiteChainAssociatedGradedDefect first).rewriteStepCount +
        ((TraceTransport.finiteChainAssociatedGradedDefect second).rewriteStepCount +
          (TraceTransport.finiteChainAssociatedGradedDefect third).rewriteStepCount) :=
  TraceTransport.finiteChainAssociatedGradedDefect_append_append_assoc_rewriteStepCount
    first
    second
    third

/-- The trace-transport root exposes associated-graded associativity rectangle counts. -/
theorem TraceTransportRoot.finiteChainAssociatedGradedDefect_assoc_importedRectangleCount
    (first second third : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ((first ++ second) ++ third)).importedRectangleCount =
      (TraceTransport.finiteChainAssociatedGradedDefect first).importedRectangleCount +
        ((TraceTransport.finiteChainAssociatedGradedDefect second).importedRectangleCount +
          (TraceTransport.finiteChainAssociatedGradedDefect third).importedRectangleCount) :=
  TraceTransport.finiteChainAssociatedGradedDefect_append_append_assoc_importedRectangleCount
    first
    second
    third

/-- The trace-transport root exposes associated-graded associativity rectangle lists. -/
theorem TraceTransportRoot.finiteChainAssociatedGradedDefect_assoc_importedRectangles
    (first second third : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ((first ++ second) ++ third)).importedRectangles =
      (TraceTransport.finiteChainAssociatedGradedDefect first).importedRectangles ++
        ((TraceTransport.finiteChainAssociatedGradedDefect second).importedRectangles ++
          (TraceTransport.finiteChainAssociatedGradedDefect third).importedRectangles) :=
  TraceTransport.finiteChainAssociatedGradedDefect_append_append_assoc_importedRectangles
    first
    second
    third

/-- The trace-transport root exposes associated-graded associativity bookkeeping payloads. -/
theorem TraceTransportRoot.finiteChainAssociatedGradedDefect_assoc_traceBookkeepingCount
    (first second third : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ((first ++ second) ++ third)).traceBookkeepingCount =
      (TraceTransport.finiteChainAssociatedGradedDefect first).traceBookkeepingCount +
        ((TraceTransport.finiteChainAssociatedGradedDefect second).traceBookkeepingCount +
          (TraceTransport.finiteChainAssociatedGradedDefect third).traceBookkeepingCount) :=
  TraceTransport.finiteChainAssociatedGradedDefect_append_append_assoc_traceBookkeepingCount
    first
    second
    third

/-- The trace-transport root exposes finite-chain associated-graded rebracketing. -/
theorem TraceTransportRoot.finiteChainAssociatedGradedDefect_rebracket
    (first second third : List TraceTransport) :
    TraceTransport.finiteChainAssociatedGradedDefect
      ((first ++ second) ++ third) =
      TraceTransport.finiteChainAssociatedGradedDefect
        (first ++ (second ++ third)) :=
  TraceTransport.finiteChainAssociatedGradedDefect_rebracket
    first
    second
    third

/-- The trace-transport root exposes associated-graded rebracketing rectangle counts. -/
theorem TraceTransportRoot.finiteChainAssociatedGradedDefect_rebracket_importedRectangleCount
    (first second third : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ((first ++ second) ++ third)).importedRectangleCount =
      (TraceTransport.finiteChainAssociatedGradedDefect
        (first ++ (second ++ third))).importedRectangleCount :=
  TraceTransport.finiteChainAssociatedGradedDefect_rebracket_importedRectangleCount
    first
    second
    third

/-- The trace-transport root exposes associated-graded rebracketing rectangle lists. -/
theorem TraceTransportRoot.finiteChainAssociatedGradedDefect_rebracket_importedRectangles
    (first second third : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ((first ++ second) ++ third)).importedRectangles =
      (TraceTransport.finiteChainAssociatedGradedDefect
        (first ++ (second ++ third))).importedRectangles :=
  TraceTransport.finiteChainAssociatedGradedDefect_rebracket_importedRectangles
    first
    second
    third

/-- The trace-transport root exposes associated-graded rebracketing bookkeeping payloads. -/
theorem TraceTransportRoot.finiteChainAssociatedGradedDefect_rebracket_traceBookkeepingCount
    (first second third : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ((first ++ second) ++ third)).traceBookkeepingCount =
      (TraceTransport.finiteChainAssociatedGradedDefect
        (first ++ (second ++ third))).traceBookkeepingCount :=
  TraceTransport.finiteChainAssociatedGradedDefect_rebracket_traceBookkeepingCount
    first
    second
    third

/-- The trace-transport root exposes associated-graded rebracketing rewrite payloads. -/
theorem TraceTransportRoot.finiteChainAssociatedGradedDefect_rebracket_rewriteStepCount
    (first second third : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ((first ++ second) ++ third)).rewriteStepCount =
      (TraceTransport.finiteChainAssociatedGradedDefect
        (first ++ (second ++ third))).rewriteStepCount :=
  TraceTransport.finiteChainAssociatedGradedDefect_rebracket_rewriteStepCount
    first
    second
    third

/-- The trace-transport root exposes finite-chain associated-graded left units. -/
theorem TraceTransportRoot.finiteChainAssociatedGradedDefect_empty_append
    (chain : List TraceTransport) :
    TraceTransport.finiteChainAssociatedGradedDefect ([] ++ chain) =
      TraceTransport.finiteChainAssociatedGradedDefect chain :=
  TraceTransport.finiteChainAssociatedGradedDefect_empty_append
    chain

/-- The trace-transport root exposes finite-chain associated-graded right units. -/
theorem TraceTransportRoot.finiteChainAssociatedGradedDefect_append_empty
    (chain : List TraceTransport) :
    TraceTransport.finiteChainAssociatedGradedDefect (chain ++ []) =
      TraceTransport.finiteChainAssociatedGradedDefect chain :=
  TraceTransport.finiteChainAssociatedGradedDefect_append_empty
    chain

/-- The trace-transport root exposes associated-graded left-unit rectangle counts. -/
theorem TraceTransportRoot.finiteChainAssociatedGradedDefect_empty_append_importedRectangleCount
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ([] ++ chain)).importedRectangleCount =
      (TraceTransport.finiteChainAssociatedGradedDefect chain).importedRectangleCount :=
  TraceTransport.finiteChainAssociatedGradedDefect_empty_append_importedRectangleCount
    chain

/-- The trace-transport root exposes associated-graded right-unit rectangle counts. -/
theorem TraceTransportRoot.finiteChainAssociatedGradedDefect_append_empty_importedRectangleCount
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (chain ++ [])).importedRectangleCount =
      (TraceTransport.finiteChainAssociatedGradedDefect chain).importedRectangleCount :=
  TraceTransport.finiteChainAssociatedGradedDefect_append_empty_importedRectangleCount
    chain

/-- The trace-transport root exposes associated-graded left-unit rectangle lists. -/
theorem TraceTransportRoot.finiteChainAssociatedGradedDefect_empty_append_importedRectangles
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ([] ++ chain)).importedRectangles =
      (TraceTransport.finiteChainAssociatedGradedDefect chain).importedRectangles :=
  TraceTransport.finiteChainAssociatedGradedDefect_empty_append_importedRectangles
    chain

/-- The trace-transport root exposes associated-graded right-unit rectangle lists. -/
theorem TraceTransportRoot.finiteChainAssociatedGradedDefect_append_empty_importedRectangles
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (chain ++ [])).importedRectangles =
      (TraceTransport.finiteChainAssociatedGradedDefect chain).importedRectangles :=
  TraceTransport.finiteChainAssociatedGradedDefect_append_empty_importedRectangles
    chain

/-- The trace-transport root exposes associated-graded left-unit bookkeeping payloads. -/
theorem TraceTransportRoot.finiteChainAssociatedGradedDefect_empty_append_traceBookkeepingCount
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ([] ++ chain)).traceBookkeepingCount =
      (TraceTransport.finiteChainAssociatedGradedDefect chain).traceBookkeepingCount :=
  TraceTransport.finiteChainAssociatedGradedDefect_empty_append_traceBookkeepingCount
    chain

/-- The trace-transport root exposes associated-graded right-unit bookkeeping payloads. -/
theorem TraceTransportRoot.finiteChainAssociatedGradedDefect_append_empty_traceBookkeepingCount
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (chain ++ [])).traceBookkeepingCount =
      (TraceTransport.finiteChainAssociatedGradedDefect chain).traceBookkeepingCount :=
  TraceTransport.finiteChainAssociatedGradedDefect_append_empty_traceBookkeepingCount
    chain

/-- The trace-transport root exposes associated-graded left-unit rewrite payloads. -/
theorem TraceTransportRoot.finiteChainAssociatedGradedDefect_empty_append_rewriteStepCount
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ([] ++ chain)).rewriteStepCount =
      (TraceTransport.finiteChainAssociatedGradedDefect chain).rewriteStepCount :=
  TraceTransport.finiteChainAssociatedGradedDefect_empty_append_rewriteStepCount
    chain

/-- The trace-transport root exposes associated-graded right-unit rewrite payloads. -/
theorem TraceTransportRoot.finiteChainAssociatedGradedDefect_append_empty_rewriteStepCount
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (chain ++ [])).rewriteStepCount =
      (TraceTransport.finiteChainAssociatedGradedDefect chain).rewriteStepCount :=
  TraceTransport.finiteChainAssociatedGradedDefect_append_empty_rewriteStepCount
    chain

/-- The trace-transport root exposes finite-chain imported-rectangle count append laws. -/
theorem TraceTransportRoot.finiteChainDefectImportedRectangleCount_append
    (first second : List TraceTransport) :
    TraceTransport.finiteChainDefectImportedRectangleCount (first ++ second) =
      TraceTransport.finiteChainDefectImportedRectangleCount first +
        TraceTransport.finiteChainDefectImportedRectangleCount second :=
  TraceTransport.finiteChainDefectImportedRectangleCount_append
    first
    second

/-- The trace-transport root exposes finite-chain imported-rectangle list append laws. -/
theorem TraceTransportRoot.finiteChainDefectImportedRectangles_append
    (first second : List TraceTransport) :
    TraceTransport.finiteChainDefectImportedRectangles (first ++ second) =
      TraceTransport.finiteChainDefectImportedRectangles first ++
        TraceTransport.finiteChainDefectImportedRectangles second :=
  TraceTransport.finiteChainDefectImportedRectangles_append
    first
    second

/-- The trace-transport root exposes finite-chain bookkeeping count append laws. -/
theorem TraceTransportRoot.finiteChainDefectTraceBookkeepingCount_append
    (first second : List TraceTransport) :
    TraceTransport.finiteChainDefectTraceBookkeepingCount (first ++ second) =
      TraceTransport.finiteChainDefectTraceBookkeepingCount first +
        TraceTransport.finiteChainDefectTraceBookkeepingCount second :=
  TraceTransport.finiteChainDefectTraceBookkeepingCount_append
    first
    second

/-- The trace-transport root exposes finite-chain rewrite-step count append laws. -/
theorem TraceTransportRoot.finiteChainDefectRewriteStepCount_append
    (first second : List TraceTransport) :
    TraceTransport.finiteChainDefectRewriteStepCount (first ++ second) =
      TraceTransport.finiteChainDefectRewriteStepCount first +
        TraceTransport.finiteChainDefectRewriteStepCount second :=
  TraceTransport.finiteChainDefectRewriteStepCount_append
    first
    second

/-- The trace-transport root exposes finite-chain imported-rectangle count associativity. -/
theorem TraceTransportRoot.finiteChainDefectImportedRectangleCount_append_append_assoc
    (first second third : List TraceTransport) :
    TraceTransport.finiteChainDefectImportedRectangleCount ((first ++ second) ++ third) =
      TraceTransport.finiteChainDefectImportedRectangleCount first +
        (TraceTransport.finiteChainDefectImportedRectangleCount second +
          TraceTransport.finiteChainDefectImportedRectangleCount third) :=
  TraceTransport.finiteChainDefectImportedRectangleCount_append_append_assoc
    first
    second
    third

/-- The trace-transport root exposes finite-chain imported-rectangle count rebracketing. -/
theorem TraceTransportRoot.finiteChainDefectImportedRectangleCount_rebracket
    (first second third : List TraceTransport) :
    TraceTransport.finiteChainDefectImportedRectangleCount ((first ++ second) ++ third) =
      TraceTransport.finiteChainDefectImportedRectangleCount (first ++ (second ++ third)) :=
  TraceTransport.finiteChainDefectImportedRectangleCount_rebracket
    first
    second
    third

/-- The trace-transport root exposes finite-chain imported-rectangle list associativity. -/
theorem TraceTransportRoot.finiteChainDefectImportedRectangles_append_append_assoc
    (first second third : List TraceTransport) :
    TraceTransport.finiteChainDefectImportedRectangles ((first ++ second) ++ third) =
      TraceTransport.finiteChainDefectImportedRectangles first ++
        (TraceTransport.finiteChainDefectImportedRectangles second ++
          TraceTransport.finiteChainDefectImportedRectangles third) :=
  TraceTransport.finiteChainDefectImportedRectangles_append_append_assoc
    first
    second
    third

/-- The trace-transport root exposes finite-chain imported-rectangle list rebracketing. -/
theorem TraceTransportRoot.finiteChainDefectImportedRectangles_rebracket
    (first second third : List TraceTransport) :
    TraceTransport.finiteChainDefectImportedRectangles ((first ++ second) ++ third) =
      TraceTransport.finiteChainDefectImportedRectangles (first ++ (second ++ third)) :=
  TraceTransport.finiteChainDefectImportedRectangles_rebracket
    first
    second
    third

/-- The trace-transport root exposes finite-chain trace-bookkeeping count associativity. -/
theorem TraceTransportRoot.finiteChainDefectTraceBookkeepingCount_append_append_assoc
    (first second third : List TraceTransport) :
    TraceTransport.finiteChainDefectTraceBookkeepingCount ((first ++ second) ++ third) =
      TraceTransport.finiteChainDefectTraceBookkeepingCount first +
        (TraceTransport.finiteChainDefectTraceBookkeepingCount second +
          TraceTransport.finiteChainDefectTraceBookkeepingCount third) :=
  TraceTransport.finiteChainDefectTraceBookkeepingCount_append_append_assoc
    first
    second
    third

/-- The trace-transport root exposes finite-chain trace-bookkeeping count rebracketing. -/
theorem TraceTransportRoot.finiteChainDefectTraceBookkeepingCount_rebracket
    (first second third : List TraceTransport) :
    TraceTransport.finiteChainDefectTraceBookkeepingCount ((first ++ second) ++ third) =
      TraceTransport.finiteChainDefectTraceBookkeepingCount (first ++ (second ++ third)) :=
  TraceTransport.finiteChainDefectTraceBookkeepingCount_rebracket
    first
    second
    third

/-- The trace-transport root exposes finite-chain rewrite-step count associativity. -/
theorem TraceTransportRoot.finiteChainDefectRewriteStepCount_append_append_assoc
    (first second third : List TraceTransport) :
    TraceTransport.finiteChainDefectRewriteStepCount ((first ++ second) ++ third) =
      TraceTransport.finiteChainDefectRewriteStepCount first +
        (TraceTransport.finiteChainDefectRewriteStepCount second +
          TraceTransport.finiteChainDefectRewriteStepCount third) :=
  TraceTransport.finiteChainDefectRewriteStepCount_append_append_assoc
    first
    second
    third

/-- The trace-transport root exposes finite-chain rewrite-step count rebracketing. -/
theorem TraceTransportRoot.finiteChainDefectRewriteStepCount_rebracket
    (first second third : List TraceTransport) :
    TraceTransport.finiteChainDefectRewriteStepCount ((first ++ second) ++ third) =
      TraceTransport.finiteChainDefectRewriteStepCount (first ++ (second ++ third)) :=
  TraceTransport.finiteChainDefectRewriteStepCount_rebracket
    first
    second
    third

/-- The trace-transport root exposes finite-chain imported-rectangle count left units. -/
theorem TraceTransportRoot.finiteChainDefectImportedRectangleCount_empty_append
    (chain : List TraceTransport) :
    TraceTransport.finiteChainDefectImportedRectangleCount ([] ++ chain) =
      TraceTransport.finiteChainDefectImportedRectangleCount chain :=
  TraceTransport.finiteChainDefectImportedRectangleCount_empty_append
    chain

/-- The trace-transport root exposes finite-chain imported-rectangle count right units. -/
theorem TraceTransportRoot.finiteChainDefectImportedRectangleCount_append_empty
    (chain : List TraceTransport) :
    TraceTransport.finiteChainDefectImportedRectangleCount (chain ++ []) =
      TraceTransport.finiteChainDefectImportedRectangleCount chain :=
  TraceTransport.finiteChainDefectImportedRectangleCount_append_empty
    chain

/-- The trace-transport root exposes finite-chain imported-rectangle list left units. -/
theorem TraceTransportRoot.finiteChainDefectImportedRectangles_empty_append
    (chain : List TraceTransport) :
    TraceTransport.finiteChainDefectImportedRectangles ([] ++ chain) =
      TraceTransport.finiteChainDefectImportedRectangles chain :=
  TraceTransport.finiteChainDefectImportedRectangles_empty_append
    chain

/-- The trace-transport root exposes finite-chain imported-rectangle list right units. -/
theorem TraceTransportRoot.finiteChainDefectImportedRectangles_append_empty
    (chain : List TraceTransport) :
    TraceTransport.finiteChainDefectImportedRectangles (chain ++ []) =
      TraceTransport.finiteChainDefectImportedRectangles chain :=
  TraceTransport.finiteChainDefectImportedRectangles_append_empty
    chain

/-- The trace-transport root exposes finite-chain bookkeeping count left units. -/
theorem TraceTransportRoot.finiteChainDefectTraceBookkeepingCount_empty_append
    (chain : List TraceTransport) :
    TraceTransport.finiteChainDefectTraceBookkeepingCount ([] ++ chain) =
      TraceTransport.finiteChainDefectTraceBookkeepingCount chain :=
  TraceTransport.finiteChainDefectTraceBookkeepingCount_empty_append
    chain

/-- The trace-transport root exposes finite-chain bookkeeping count right units. -/
theorem TraceTransportRoot.finiteChainDefectTraceBookkeepingCount_append_empty
    (chain : List TraceTransport) :
    TraceTransport.finiteChainDefectTraceBookkeepingCount (chain ++ []) =
      TraceTransport.finiteChainDefectTraceBookkeepingCount chain :=
  TraceTransport.finiteChainDefectTraceBookkeepingCount_append_empty
    chain

/-- The trace-transport root exposes finite-chain rewrite-step count left units. -/
theorem TraceTransportRoot.finiteChainDefectRewriteStepCount_empty_append
    (chain : List TraceTransport) :
    TraceTransport.finiteChainDefectRewriteStepCount ([] ++ chain) =
      TraceTransport.finiteChainDefectRewriteStepCount chain :=
  TraceTransport.finiteChainDefectRewriteStepCount_empty_append
    chain

/-- The trace-transport root exposes finite-chain rewrite-step count right units. -/
theorem TraceTransportRoot.finiteChainDefectRewriteStepCount_append_empty
    (chain : List TraceTransport) :
    TraceTransport.finiteChainDefectRewriteStepCount (chain ++ []) =
      TraceTransport.finiteChainDefectRewriteStepCount chain :=
  TraceTransport.finiteChainDefectRewriteStepCount_append_empty
    chain

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Certificates.Owner

/-!
# Public certificates for typed trace hom representatives

This file exposes certificate and payload accounting for chosen representatives
of typed trace-correspondence homs.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes the raw candidate formal sum of a typed hom representative. -/
theorem AnalyticMotivesRoot.traceCorQHomRepresentative_rawCandidate_formalSum
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    representative.rawCandidate.formalSum =
      representative.formalSum.raw :=
  TraceCorQHomRepresentative.rawCandidate_formalSum
    representative

/-- The top root exposes the raw candidate ledger of a typed hom representative. -/
theorem AnalyticMotivesRoot.traceCorQHomRepresentative_rawCandidate_ledger
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    representative.rawCandidate.ledger =
      representative.ledger :=
  TraceCorQHomRepresentative.rawCandidate_ledger
    representative

/-- The top root exposes the raw candidate certificate ledger. -/
theorem AnalyticMotivesRoot.traceCorQHomRepresentative_rawCandidate_certificateLedger
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    representative.rawCandidate.certificateLedger =
      representative.certificateLedger :=
  TraceCorQHomRepresentative.rawCandidate_certificateLedger
    representative

/-- The top root exposes representative certificate-ledger splitting. -/
theorem AnalyticMotivesRoot.traceCorQHomRepresentative_certificateLedger_eq_append
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    representative.certificateLedger =
      ResidueChannelCertificateLedger.append
        representative.formalSum.certificateLedger
        representative.ledger.certificateLedger :=
  TraceCorQHomRepresentative.certificateLedger_eq
    representative

/-- The top root exposes the raw candidate imported-rectangle count. -/
theorem AnalyticMotivesRoot.traceCorQHomRepresentative_rawCandidate_importedRectangleCount
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    representative.rawCandidate.importedRectangleCount =
      representative.importedRectangleCount :=
  TraceCorQHomRepresentative.rawCandidate_importedRectangleCount
    representative

/-- The top root exposes the raw candidate imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQHomRepresentative_rawCandidate_importedRectangles
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    representative.rawCandidate.importedRectangles =
      representative.importedRectangles :=
  TraceCorQHomRepresentative.rawCandidate_importedRectangles
    representative

/-- The top root exposes the raw candidate bookkeeping count. -/
theorem AnalyticMotivesRoot.traceCorQHomRepresentative_rawCandidate_traceBookkeepingCount
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    representative.rawCandidate.traceBookkeepingCount =
      representative.traceBookkeepingCount :=
  TraceCorQHomRepresentative.rawCandidate_traceBookkeepingCount
    representative

/-- The top root exposes the raw candidate rewrite-step count. -/
theorem AnalyticMotivesRoot.traceCorQHomRepresentative_rawCandidate_rewriteStepCount
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    representative.rawCandidate.rewriteStepCount =
      representative.rewriteStepCount :=
  TraceCorQHomRepresentative.rawCandidate_rewriteStepCount
    representative

/-- The top root exposes imported-rectangle count splitting for representatives. -/
theorem AnalyticMotivesRoot.traceCorQHomRepresentative_importedRectangleCount_eq
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    representative.importedRectangleCount =
      representative.formalSum.importedRectangleCount +
        representative.ledger.importedRectangleCount :=
  TraceCorQHomRepresentative.importedRectangleCount_eq
    representative

/-- The top root exposes imported-rectangle list splitting for representatives. -/
theorem AnalyticMotivesRoot.traceCorQHomRepresentative_importedRectangles_eq
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    representative.importedRectangles =
      representative.formalSum.importedRectangles ++
        representative.ledger.importedRectangles :=
  TraceCorQHomRepresentative.importedRectangles_eq
    representative

/-- The top root exposes representative imported-rectangle count as list length. -/
theorem AnalyticMotivesRoot.traceCorQHomRepresentative_importedRectangleCount_eq_length_importedRectangles
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    representative.importedRectangleCount =
      representative.importedRectangles.length :=
  TraceCorQHomRepresentative.importedRectangleCount_eq_length_importedRectangles
    representative

/-- The top root exposes bookkeeping-count splitting for representatives. -/
theorem AnalyticMotivesRoot.traceCorQHomRepresentative_traceBookkeepingCount_eq
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    representative.traceBookkeepingCount =
      representative.formalSum.traceBookkeepingCount +
        representative.ledger.traceBookkeepingCount :=
  TraceCorQHomRepresentative.traceBookkeepingCount_eq
    representative

/-- The top root exposes rewrite-step count splitting for representatives. -/
theorem AnalyticMotivesRoot.traceCorQHomRepresentative_rewriteStepCount_eq
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    representative.rewriteStepCount =
      representative.formalSum.rewriteStepCount +
        representative.ledger.rewriteStepCount :=
  TraceCorQHomRepresentative.rewriteStepCount_eq
    representative

/-- The top root exposes the zero representative certificate ledger. -/
theorem AnalyticMotivesRoot.traceCorQHomRepresentative_zero_certificateLedger
    (source target : TraceCorQObject) :
    (TraceCorQHomRepresentative.ofFormalSumLedger
      (TraceCorQHomFormalSum.zero source target)
      TraceCorQRelationLedger.empty).certificateLedger =
      ResidueChannelCertificateLedger.empty :=
  TraceCorQHomRepresentative.zero_certificateLedger
    source
    target

/-- The top root exposes the zero representative imported-rectangle count. -/
theorem AnalyticMotivesRoot.traceCorQHomRepresentative_zero_importedRectangleCount
    (source target : TraceCorQObject) :
    (TraceCorQHomRepresentative.ofFormalSumLedger
      (TraceCorQHomFormalSum.zero source target)
      TraceCorQRelationLedger.empty).importedRectangleCount =
      0 :=
  TraceCorQHomRepresentative.zero_importedRectangleCount
    source
    target

/-- The top root exposes the zero representative imported-rectangle list. -/
theorem AnalyticMotivesRoot.traceCorQHomRepresentative_zero_importedRectangles
    (source target : TraceCorQObject) :
    (TraceCorQHomRepresentative.ofFormalSumLedger
      (TraceCorQHomFormalSum.zero source target)
      TraceCorQRelationLedger.empty).importedRectangles =
      [] :=
  TraceCorQHomRepresentative.zero_importedRectangles
    source
    target

/-- The top root exposes the zero representative bookkeeping count. -/
theorem AnalyticMotivesRoot.traceCorQHomRepresentative_zero_traceBookkeepingCount
    (source target : TraceCorQObject) :
    (TraceCorQHomRepresentative.ofFormalSumLedger
      (TraceCorQHomFormalSum.zero source target)
      TraceCorQRelationLedger.empty).traceBookkeepingCount =
      0 :=
  TraceCorQHomRepresentative.zero_traceBookkeepingCount
    source
    target

/-- The top root exposes the zero representative rewrite-step count. -/
theorem AnalyticMotivesRoot.traceCorQHomRepresentative_zero_rewriteStepCount
    (source target : TraceCorQObject) :
    (TraceCorQHomRepresentative.ofFormalSumLedger
      (TraceCorQHomFormalSum.zero source target)
      TraceCorQRelationLedger.empty).rewriteStepCount =
      0 :=
  TraceCorQHomRepresentative.zero_rewriteStepCount
    source
    target

/-- The top root exposes the singleton representative certificate ledger. -/
theorem AnalyticMotivesRoot.traceCorQHomRepresentative_singleton_emptyLedger_certificateLedger
    (source target : TraceCorQObject)
    (coefficient : Rat)
    (generator : TraceCorQGenerator)
    (source_eq : generator.source = source)
    (target_eq : generator.target = target) :
    (TraceCorQHomRepresentative.ofFormalSumLedger
      (TraceCorQHomFormalSum.singleton
        source
        target
        coefficient
        generator
        source_eq
        target_eq)
      TraceCorQRelationLedger.empty).certificateLedger =
      ResidueChannelCertificateLedger.append
        (ResidueChannelCertificateLedger.append
          generator.certificateLedger
          ResidueChannelCertificateLedger.empty)
        ResidueChannelCertificateLedger.empty :=
  TraceCorQHomRepresentative.singleton_emptyLedger_certificateLedger
    source
    target
    coefficient
    generator
    source_eq
    target_eq

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Classes.Owner

/-!
# Certificates for typed trace-correspondence hom representatives

This file owns certificate-accounting lemmas for typed hom representatives.
The quotient hom itself does not carry a canonical ledger here; only chosen
representatives do.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The raw candidate of a typed hom representative has the representative's raw formal sum. -/
theorem TraceCorQHomRepresentative.rawCandidate_formalSum
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    representative.rawCandidate.formalSum =
      representative.formalSum.raw :=
  rfl

/-- The raw candidate of a typed hom representative has the representative's relation ledger. -/
theorem TraceCorQHomRepresentative.rawCandidate_ledger
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    representative.rawCandidate.ledger =
      representative.ledger :=
  rfl

/-- The raw candidate of a typed hom representative has the representative's certificates. -/
theorem TraceCorQHomRepresentative.rawCandidate_certificateLedger
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    representative.rawCandidate.certificateLedger =
      representative.certificateLedger :=
  rfl

/--
The certificate ledger of a typed hom representative is the append of its typed
formal-sum certificates and relation-ledger certificates.
-/
theorem TraceCorQHomRepresentative.certificateLedger_eq
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    representative.certificateLedger =
      ResidueChannelCertificateLedger.append
        representative.formalSum.certificateLedger
        representative.ledger.certificateLedger :=
  rfl

/-- The imported finite-rectangle payload carried by a typed hom representative. -/
def TraceCorQHomRepresentative.importedRectangleCount
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    Nat :=
  representative.certificateLedger.importedRectangleCount

/-- The internal trace-bookkeeping payload carried by a typed hom representative. -/
def TraceCorQHomRepresentative.traceBookkeepingCount
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    Nat :=
  representative.certificateLedger.traceBookkeepingCount

/-- The explicit rewrite-step payload carried by a typed hom representative. -/
def TraceCorQHomRepresentative.rewriteStepCount
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    Nat :=
  representative.certificateLedger.rewriteStepCount

/-- The raw candidate of a typed hom representative has the representative's imported payload. -/
theorem TraceCorQHomRepresentative.rawCandidate_importedRectangleCount
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    representative.rawCandidate.importedRectangleCount =
      representative.importedRectangleCount :=
  rfl

/-- The raw candidate of a typed hom representative has the representative's bookkeeping payload. -/
theorem TraceCorQHomRepresentative.rawCandidate_traceBookkeepingCount
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    representative.rawCandidate.traceBookkeepingCount =
      representative.traceBookkeepingCount :=
  rfl

/-- The raw candidate of a typed hom representative has the representative's rewrite-step payload. -/
theorem TraceCorQHomRepresentative.rawCandidate_rewriteStepCount
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    representative.rawCandidate.rewriteStepCount =
      representative.rewriteStepCount :=
  rfl

/-- Representative imported payload splits into formal-sum and relation-ledger payload. -/
theorem TraceCorQHomRepresentative.importedRectangleCount_eq
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    representative.importedRectangleCount =
      representative.formalSum.importedRectangleCount +
        representative.ledger.importedRectangleCount :=
  ResidueChannelCertificateLedger.append_importedRectangleCount
    representative.formalSum.certificateLedger
    representative.ledger.certificateLedger

/-- Representative bookkeeping payload splits into formal-sum and relation-ledger payload. -/
theorem TraceCorQHomRepresentative.traceBookkeepingCount_eq
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    representative.traceBookkeepingCount =
      representative.formalSum.traceBookkeepingCount +
        representative.ledger.traceBookkeepingCount :=
  ResidueChannelCertificateLedger.append_traceBookkeepingCount
    representative.formalSum.certificateLedger
    representative.ledger.certificateLedger

/-- Representative rewrite-step payload splits into formal-sum and relation-ledger payload. -/
theorem TraceCorQHomRepresentative.rewriteStepCount_eq
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    representative.rewriteStepCount =
      representative.formalSum.rewriteStepCount +
        representative.ledger.rewriteStepCount :=
  ResidueChannelCertificateLedger.append_rewriteStepCount
    representative.formalSum.certificateLedger
    representative.ledger.certificateLedger

/-- The zero representative carries the empty analytic certificate ledger. -/
theorem TraceCorQHomRepresentative.zero_certificateLedger
    (source target : TraceCorQObject) :
    (TraceCorQHomRepresentative.ofFormalSumLedger
      (TraceCorQHomFormalSum.zero source target)
      TraceCorQRelationLedger.empty).certificateLedger =
      ResidueChannelCertificateLedger.empty :=
  rfl

/-- The zero representative carries no imported finite-rectangle payload. -/
theorem TraceCorQHomRepresentative.zero_importedRectangleCount
    (source target : TraceCorQObject) :
    (TraceCorQHomRepresentative.ofFormalSumLedger
      (TraceCorQHomFormalSum.zero source target)
      TraceCorQRelationLedger.empty).importedRectangleCount =
      0 :=
  rfl

/-- The zero representative carries no internal trace-bookkeeping payload. -/
theorem TraceCorQHomRepresentative.zero_traceBookkeepingCount
    (source target : TraceCorQObject) :
    (TraceCorQHomRepresentative.ofFormalSumLedger
      (TraceCorQHomFormalSum.zero source target)
      TraceCorQRelationLedger.empty).traceBookkeepingCount =
      0 :=
  rfl

/-- The zero representative carries no explicit rewrite-step payload. -/
theorem TraceCorQHomRepresentative.zero_rewriteStepCount
    (source target : TraceCorQObject) :
    (TraceCorQHomRepresentative.ofFormalSumLedger
      (TraceCorQHomFormalSum.zero source target)
      TraceCorQRelationLedger.empty).rewriteStepCount =
      0 :=
  rfl

/-- A singleton representative carries the certificate ledger of its generator. -/
theorem TraceCorQHomRepresentative.singleton_emptyLedger_certificateLedger
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
  rfl

end AnalyticMotives
end LFunctions
end Boundary

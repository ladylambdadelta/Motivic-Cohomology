import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.LedgeredTransports.CoherenceLedgers.Owner

/-!
# Analytic certificate ledgers for ledgered transports

This file owns the analytic certificate ledgers attached to the category-shape
coherence cells of ledgered trace transports.  Relation ledgers record what is
imposed in the quotient; certificate ledgers record the analytic coherence
cells justifying those relations.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic certificate ledger carried by the underlying raw transport. -/
def LedgeredTraceTransport.transportCertificateLedger
    (transport : LedgeredTraceTransport) :
    ResidueChannelCertificateLedger :=
  transport.transport.certificateLedger

/-- The imported finite-rectangle payload carried by the underlying raw transport. -/
def LedgeredTraceTransport.transportImportedRectangleCount
    (transport : LedgeredTraceTransport) :
    Nat :=
  transport.transportCertificateLedger.importedRectangleCount

/-- The internal trace-bookkeeping payload carried by the underlying raw transport. -/
def LedgeredTraceTransport.transportTraceBookkeepingCount
    (transport : LedgeredTraceTransport) :
    Nat :=
  transport.transportCertificateLedger.traceBookkeepingCount

/-- The associativity coherence certificate ledger for three ledgered transports. -/
def LedgeredTraceTransport.associativityCertificateLedger
    (first second third : LedgeredTraceTransport) :
    ResidueChannelCertificateLedger :=
  ResidueChannelCertificateLedger.ofCoherenceCell
    (LedgeredTraceTransport.compAssociativityCoherence
      first second third)

/-- The imported payload carried by the associativity coherence certificate. -/
def LedgeredTraceTransport.associativityImportedRectangleCount
    (first second third : LedgeredTraceTransport) :
    Nat :=
  (LedgeredTraceTransport.associativityCertificateLedger
    first
    second
    third).importedRectangleCount

/-- The bookkeeping payload carried by the associativity coherence certificate. -/
def LedgeredTraceTransport.associativityTraceBookkeepingCount
    (first second third : LedgeredTraceTransport) :
    Nat :=
  (LedgeredTraceTransport.associativityCertificateLedger
    first
    second
    third).traceBookkeepingCount

/-- The left-identity coherence certificate ledger for a ledgered transport. -/
def LedgeredTraceTransport.leftIdentityCertificateLedger
    (transport : LedgeredTraceTransport) :
    ResidueChannelCertificateLedger :=
  ResidueChannelCertificateLedger.ofCoherenceCell
    (LedgeredTraceTransport.leftIdentityCoherence transport)

/-- The imported payload carried by the left-identity coherence certificate. -/
def LedgeredTraceTransport.leftIdentityImportedRectangleCount
    (transport : LedgeredTraceTransport) :
    Nat :=
  (LedgeredTraceTransport.leftIdentityCertificateLedger
    transport).importedRectangleCount

/-- The bookkeeping payload carried by the left-identity coherence certificate. -/
def LedgeredTraceTransport.leftIdentityTraceBookkeepingCount
    (transport : LedgeredTraceTransport) :
    Nat :=
  (LedgeredTraceTransport.leftIdentityCertificateLedger
    transport).traceBookkeepingCount

/-- The right-identity coherence certificate ledger for a ledgered transport. -/
def LedgeredTraceTransport.rightIdentityCertificateLedger
    (transport : LedgeredTraceTransport) :
    ResidueChannelCertificateLedger :=
  ResidueChannelCertificateLedger.ofCoherenceCell
    (LedgeredTraceTransport.rightIdentityCoherence transport)

/-- The imported payload carried by the right-identity coherence certificate. -/
def LedgeredTraceTransport.rightIdentityImportedRectangleCount
    (transport : LedgeredTraceTransport) :
    Nat :=
  (LedgeredTraceTransport.rightIdentityCertificateLedger
    transport).importedRectangleCount

/-- The bookkeeping payload carried by the right-identity coherence certificate. -/
def LedgeredTraceTransport.rightIdentityTraceBookkeepingCount
    (transport : LedgeredTraceTransport) :
    Nat :=
  (LedgeredTraceTransport.rightIdentityCertificateLedger
    transport).traceBookkeepingCount

/-- The category-shape analytic certificate ledger for three ledgered transports. -/
def LedgeredTraceTransport.categoryShapeCertificateLedger
    (first second third : LedgeredTraceTransport) :
    ResidueChannelCertificateLedger :=
  ResidueChannelCertificateLedger.append
    (LedgeredTraceTransport.associativityCertificateLedger
      first second third)
    (ResidueChannelCertificateLedger.append
      (LedgeredTraceTransport.leftIdentityCertificateLedger first)
      (LedgeredTraceTransport.rightIdentityCertificateLedger third))

/-- The imported payload carried by the category-shape coherence ledger. -/
def LedgeredTraceTransport.categoryShapeImportedRectangleCount
    (first second third : LedgeredTraceTransport) :
    Nat :=
  (LedgeredTraceTransport.categoryShapeCertificateLedger
    first
    second
    third).importedRectangleCount

/-- The bookkeeping payload carried by the category-shape coherence ledger. -/
def LedgeredTraceTransport.categoryShapeTraceBookkeepingCount
    (first second third : LedgeredTraceTransport) :
    Nat :=
  (LedgeredTraceTransport.categoryShapeCertificateLedger
    first
    second
    third).traceBookkeepingCount

/-- A ledgered transport's transport certificate ledger is inherited from its raw transport. -/
theorem LedgeredTraceTransport.transportCertificateLedger_eq
    (transport : LedgeredTraceTransport) :
    transport.transportCertificateLedger =
      transport.transport.certificateLedger :=
  rfl

/-- The transport imported payload is inherited from its raw transport certificate ledger. -/
theorem LedgeredTraceTransport.transportImportedRectangleCount_eq
    (transport : LedgeredTraceTransport) :
    transport.transportImportedRectangleCount =
      transport.transport.importedRectangleCount :=
  rfl

/-- The transport bookkeeping payload is inherited from its raw transport certificate ledger. -/
theorem LedgeredTraceTransport.transportTraceBookkeepingCount_eq
    (transport : LedgeredTraceTransport) :
    transport.transportTraceBookkeepingCount =
      transport.transport.traceBookkeepingCount :=
  rfl

/-- The associativity certificate ledger is the singleton coherence-cell ledger. -/
theorem LedgeredTraceTransport.associativityCertificateLedger_eq
    (first second third : LedgeredTraceTransport) :
    LedgeredTraceTransport.associativityCertificateLedger
      first second third =
      ResidueChannelCertificateLedger.ofCoherenceCell
        (LedgeredTraceTransport.compAssociativityCoherence
          first second third) :=
  rfl

/-- The left-identity certificate ledger is the singleton coherence-cell ledger. -/
theorem LedgeredTraceTransport.leftIdentityCertificateLedger_eq
    (transport : LedgeredTraceTransport) :
    LedgeredTraceTransport.leftIdentityCertificateLedger transport =
      ResidueChannelCertificateLedger.ofCoherenceCell
        (LedgeredTraceTransport.leftIdentityCoherence transport) :=
  rfl

/-- The right-identity certificate ledger is the singleton coherence-cell ledger. -/
theorem LedgeredTraceTransport.rightIdentityCertificateLedger_eq
    (transport : LedgeredTraceTransport) :
    LedgeredTraceTransport.rightIdentityCertificateLedger transport =
      ResidueChannelCertificateLedger.ofCoherenceCell
        (LedgeredTraceTransport.rightIdentityCoherence transport) :=
  rfl

/-- The category-shape certificate ledger is associativity followed by both identity cells. -/
theorem LedgeredTraceTransport.categoryShapeCertificateLedger_eq
    (first second third : LedgeredTraceTransport) :
    LedgeredTraceTransport.categoryShapeCertificateLedger
      first second third =
      ResidueChannelCertificateLedger.append
        (LedgeredTraceTransport.associativityCertificateLedger
          first second third)
        (ResidueChannelCertificateLedger.append
          (LedgeredTraceTransport.leftIdentityCertificateLedger first)
          (LedgeredTraceTransport.rightIdentityCertificateLedger third)) :=
  rfl

/-- Category-shape imported payload is associativity plus both identity payloads. -/
theorem LedgeredTraceTransport.categoryShapeImportedRectangleCount_eq
    (first second third : LedgeredTraceTransport) :
    LedgeredTraceTransport.categoryShapeImportedRectangleCount
      first
      second
      third =
      LedgeredTraceTransport.associativityImportedRectangleCount
        first
        second
        third +
        (LedgeredTraceTransport.leftIdentityImportedRectangleCount first +
          LedgeredTraceTransport.rightIdentityImportedRectangleCount third) :=
  Eq.trans
    (ResidueChannelCertificateLedger.append_importedRectangleCount
      (LedgeredTraceTransport.associativityCertificateLedger
        first
        second
        third)
      (ResidueChannelCertificateLedger.append
        (LedgeredTraceTransport.leftIdentityCertificateLedger first)
        (LedgeredTraceTransport.rightIdentityCertificateLedger third)))
    (congrArg
      (fun count =>
        LedgeredTraceTransport.associativityImportedRectangleCount
          first
          second
          third +
          count)
      (ResidueChannelCertificateLedger.append_importedRectangleCount
        (LedgeredTraceTransport.leftIdentityCertificateLedger first)
        (LedgeredTraceTransport.rightIdentityCertificateLedger third)))

/-- Category-shape bookkeeping payload is associativity plus both identity payloads. -/
theorem LedgeredTraceTransport.categoryShapeTraceBookkeepingCount_eq
    (first second third : LedgeredTraceTransport) :
    LedgeredTraceTransport.categoryShapeTraceBookkeepingCount
      first
      second
      third =
      LedgeredTraceTransport.associativityTraceBookkeepingCount
        first
        second
        third +
        (LedgeredTraceTransport.leftIdentityTraceBookkeepingCount first +
          LedgeredTraceTransport.rightIdentityTraceBookkeepingCount third) :=
  Eq.trans
    (ResidueChannelCertificateLedger.append_traceBookkeepingCount
      (LedgeredTraceTransport.associativityCertificateLedger
        first
        second
        third)
      (ResidueChannelCertificateLedger.append
        (LedgeredTraceTransport.leftIdentityCertificateLedger first)
        (LedgeredTraceTransport.rightIdentityCertificateLedger third)))
    (congrArg
      (fun count =>
        LedgeredTraceTransport.associativityTraceBookkeepingCount
          first
          second
          third +
          count)
      (ResidueChannelCertificateLedger.append_traceBookkeepingCount
        (LedgeredTraceTransport.leftIdentityCertificateLedger first)
        (LedgeredTraceTransport.rightIdentityCertificateLedger third)))

end AnalyticMotives
end LFunctions
end Boundary

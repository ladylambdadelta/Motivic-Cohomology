import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.LedgeredTransports.CoherenceLedgers.Owner

/-!
# Core analytic certificate ledgers for ledgered transports

This file owns the analytic certificate-ledger definitions attached to
ledgered trace transports and their category-shape coherence cells.
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

/-- The imported finite rectangles carried by the underlying raw transport. -/
def LedgeredTraceTransport.transportImportedRectangles
    (transport : LedgeredTraceTransport) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  transport.transportCertificateLedger.importedRectangles

/-- The internal trace-bookkeeping payload carried by the underlying raw transport. -/
def LedgeredTraceTransport.transportTraceBookkeepingCount
    (transport : LedgeredTraceTransport) :
    Nat :=
  transport.transportCertificateLedger.traceBookkeepingCount

/-- The associativity coherence certificate ledger for three ledgered transports. -/
def LedgeredTraceTransport.associativityCertificateLedger
    (first second third : LedgeredTraceTransport) :
    ResidueChannelCertificateLedger :=
  ResidueChannelCertificateLedger.ofCertifiedCoherenceCell
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

/-- The imported rectangles carried by the associativity coherence certificate. -/
def LedgeredTraceTransport.associativityImportedRectangles
    (first second third : LedgeredTraceTransport) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  (LedgeredTraceTransport.associativityCertificateLedger
    first
    second
    third).importedRectangles

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
  ResidueChannelCertificateLedger.ofCertifiedCoherenceCell
    (LedgeredTraceTransport.leftIdentityCoherence transport)

/-- The imported payload carried by the left-identity coherence certificate. -/
def LedgeredTraceTransport.leftIdentityImportedRectangleCount
    (transport : LedgeredTraceTransport) :
    Nat :=
  (LedgeredTraceTransport.leftIdentityCertificateLedger
    transport).importedRectangleCount

/-- The imported rectangles carried by the left-identity coherence certificate. -/
def LedgeredTraceTransport.leftIdentityImportedRectangles
    (transport : LedgeredTraceTransport) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  (LedgeredTraceTransport.leftIdentityCertificateLedger
    transport).importedRectangles

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
  ResidueChannelCertificateLedger.ofCertifiedCoherenceCell
    (LedgeredTraceTransport.rightIdentityCoherence transport)

/-- The imported payload carried by the right-identity coherence certificate. -/
def LedgeredTraceTransport.rightIdentityImportedRectangleCount
    (transport : LedgeredTraceTransport) :
    Nat :=
  (LedgeredTraceTransport.rightIdentityCertificateLedger
    transport).importedRectangleCount

/-- The imported rectangles carried by the right-identity coherence certificate. -/
def LedgeredTraceTransport.rightIdentityImportedRectangles
    (transport : LedgeredTraceTransport) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  (LedgeredTraceTransport.rightIdentityCertificateLedger
    transport).importedRectangles

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

/-- The imported rectangles carried by the category-shape coherence ledger. -/
def LedgeredTraceTransport.categoryShapeImportedRectangles
    (first second third : LedgeredTraceTransport) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  (LedgeredTraceTransport.categoryShapeCertificateLedger
    first
    second
    third).importedRectangles

/-- The bookkeeping payload carried by the category-shape coherence ledger. -/
def LedgeredTraceTransport.categoryShapeTraceBookkeepingCount
    (first second third : LedgeredTraceTransport) :
    Nat :=
  (LedgeredTraceTransport.categoryShapeCertificateLedger
    first
    second
    third).traceBookkeepingCount

end AnalyticMotives
end LFunctions
end Boundary

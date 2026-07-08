import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.LedgeredTransports.Certificates.Core.Owner

/-!
# Analytic certificate-ledger facts for ledgered transports

This file owns theorem facts about the analytic certificate ledgers attached to
ledgered trace transports and their category-shape coherence cells.  The core
certificate-ledger definitions live in the `Core` child file.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

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

/-- The transport imported rectangles are inherited from its raw transport certificate ledger. -/
theorem LedgeredTraceTransport.transportImportedRectangles_eq
    (transport : LedgeredTraceTransport) :
    transport.transportImportedRectangles =
      transport.transport.importedRectangles :=
  rfl

/-- The transport bookkeeping payload is inherited from its raw transport certificate ledger. -/
theorem LedgeredTraceTransport.transportTraceBookkeepingCount_eq
    (transport : LedgeredTraceTransport) :
    transport.transportTraceBookkeepingCount =
      transport.transport.traceBookkeepingCount :=
  rfl

/-- The associativity certificate ledger records both compared paths and the cell. -/
theorem LedgeredTraceTransport.associativityCertificateLedger_eq
    (first second third : LedgeredTraceTransport) :
    LedgeredTraceTransport.associativityCertificateLedger
      first second third =
      ResidueChannelCertificateLedger.ofCertifiedCoherenceCell
        (LedgeredTraceTransport.compAssociativityCoherence
          first second third) :=
  rfl

/-- The left-identity certificate ledger records both compared paths and the cell. -/
theorem LedgeredTraceTransport.leftIdentityCertificateLedger_eq
    (transport : LedgeredTraceTransport) :
    LedgeredTraceTransport.leftIdentityCertificateLedger transport =
      ResidueChannelCertificateLedger.ofCertifiedCoherenceCell
        (LedgeredTraceTransport.leftIdentityCoherence transport) :=
  rfl

/-- The right-identity certificate ledger records both compared paths and the cell. -/
theorem LedgeredTraceTransport.rightIdentityCertificateLedger_eq
    (transport : LedgeredTraceTransport) :
    LedgeredTraceTransport.rightIdentityCertificateLedger transport =
      ResidueChannelCertificateLedger.ofCertifiedCoherenceCell
        (LedgeredTraceTransport.rightIdentityCoherence transport) :=
  rfl

/-- The associativity certificate ledger records the two triple-composition paths and cell. -/
theorem LedgeredTraceTransport.associativityCertificateLedger_eq_paths_cell
    (first second third : LedgeredTraceTransport) :
    LedgeredTraceTransport.associativityCertificateLedger
      first
      second
      third =
      ResidueChannelCertificateAtom.rewritePath
        ((first.comp second).comp third).path ::
        ResidueChannelCertificateAtom.rewritePath
          (first.comp (second.comp third)).path ::
          ResidueChannelCertificateAtom.coherenceCell
            (LedgeredTraceTransport.compAssociativityCoherence
              first
              second
              third) ::
            ResidueChannelCertificateLedger.empty :=
  rfl

/-- The left-identity certificate ledger records the identity-left path and original path. -/
theorem LedgeredTraceTransport.leftIdentityCertificateLedger_eq_paths_cell
    (transport : LedgeredTraceTransport) :
    LedgeredTraceTransport.leftIdentityCertificateLedger transport =
      ResidueChannelCertificateAtom.rewritePath
        ((LedgeredTraceTransport.id transport.source).comp transport).path ::
        ResidueChannelCertificateAtom.rewritePath transport.path ::
          ResidueChannelCertificateAtom.coherenceCell
            (LedgeredTraceTransport.leftIdentityCoherence transport) ::
            ResidueChannelCertificateLedger.empty :=
  rfl

/-- The right-identity certificate ledger records the identity-right path and original path. -/
theorem LedgeredTraceTransport.rightIdentityCertificateLedger_eq_paths_cell
    (transport : LedgeredTraceTransport) :
    LedgeredTraceTransport.rightIdentityCertificateLedger transport =
      ResidueChannelCertificateAtom.rewritePath
        (transport.comp (LedgeredTraceTransport.id transport.target)).path ::
        ResidueChannelCertificateAtom.rewritePath transport.path ::
          ResidueChannelCertificateAtom.coherenceCell
            (LedgeredTraceTransport.rightIdentityCoherence transport) ::
            ResidueChannelCertificateLedger.empty :=
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

/-- Category-shape imported rectangles are associativity followed by both identity rectangles. -/
theorem LedgeredTraceTransport.categoryShapeImportedRectangles_eq
    (first second third : LedgeredTraceTransport) :
    LedgeredTraceTransport.categoryShapeImportedRectangles
      first
      second
      third =
      LedgeredTraceTransport.associativityImportedRectangles
        first
        second
        third ++
        (LedgeredTraceTransport.leftIdentityImportedRectangles first ++
          LedgeredTraceTransport.rightIdentityImportedRectangles third) :=
  Eq.trans
    (ResidueChannelCertificateLedger.append_importedRectangles
      (LedgeredTraceTransport.associativityCertificateLedger
        first
        second
        third)
      (ResidueChannelCertificateLedger.append
        (LedgeredTraceTransport.leftIdentityCertificateLedger first)
        (LedgeredTraceTransport.rightIdentityCertificateLedger third)))
    (congrArg
      (fun rectangles =>
        LedgeredTraceTransport.associativityImportedRectangles
          first
          second
          third ++
          rectangles)
      (ResidueChannelCertificateLedger.append_importedRectangles
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

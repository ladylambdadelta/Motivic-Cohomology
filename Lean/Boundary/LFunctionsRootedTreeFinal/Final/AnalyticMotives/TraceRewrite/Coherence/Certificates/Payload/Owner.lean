import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Coherence.Certificates.Owner

/-!
# Payload facts for named coherence certificate ledgers

This file records imported-rectangle payload invariants for the certificate
ledgers attached to named higher coherence cells.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A Fubini coherence certificate ledger carries no imported finite rectangles. -/
theorem TraceCoherenceCell.fubiniCertificateLedger_importedRectangleCount
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.fubiniCertificateLedger
      source
      target).importedRectangleCount =
      0 + (0 + (0 + 0)) :=
  rfl

/-- A schedule-exchange coherence certificate ledger carries no imported finite rectangles. -/
theorem TraceCoherenceCell.scheduleExchangeCertificateLedger_importedRectangleCount
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.scheduleExchangeCertificateLedger
      source
      target).importedRectangleCount =
      0 + (0 + (0 + 0)) :=
  rfl

/-- A residue-channel coherence certificate ledger carries no imported finite rectangles. -/
theorem TraceCoherenceCell.residueChannelCertificateLedger_importedRectangleCount
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.residueChannelCertificateLedger
      source
      target).importedRectangleCount =
      0 + (0 + (0 + 0)) :=
  rfl

/-- A Stokes-residue coherence certificate ledger carries no imported finite rectangles. -/
theorem TraceCoherenceCell.stokesResidueCertificateLedger_importedRectangleCount
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.stokesResidueCertificateLedger
      source
      target).importedRectangleCount =
      0 + (0 + (0 + 0)) :=
  rfl

/-- A refinement coherence certificate ledger carries no imported finite rectangles. -/
theorem TraceCoherenceCell.refinementCertificateLedger_importedRectangleCount
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.refinementCertificateLedger
      source
      target).importedRectangleCount =
      0 + (0 + (0 + 0)) :=
  rfl

/-- An associativity coherence certificate ledger carries no imported finite rectangles. -/
theorem TraceCoherenceCell.associativityCertificateLedger_importedRectangleCount
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.associativityCertificateLedger
      source
      target).importedRectangleCount =
      0 + (0 + (0 + 0)) :=
  rfl

/-- A left-identity coherence certificate ledger carries no imported finite rectangles. -/
theorem TraceCoherenceCell.leftIdentityCertificateLedger_importedRectangleCount
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.leftIdentityCertificateLedger
      source
      target).importedRectangleCount =
      0 + (0 + (0 + 0)) :=
  rfl

/-- A right-identity coherence certificate ledger carries no imported finite rectangles. -/
theorem TraceCoherenceCell.rightIdentityCertificateLedger_importedRectangleCount
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.rightIdentityCertificateLedger
      source
      target).importedRectangleCount =
      0 + (0 + (0 + 0)) :=
  rfl

/-- A Fubini coherence certificate ledger exposes no imported finite rectangles. -/
theorem TraceCoherenceCell.fubiniCertificateLedger_importedRectangles
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.fubiniCertificateLedger
      source
      target).importedRectangles =
      [] ++ ([] ++ ([] ++ [])) :=
  rfl

/-- A schedule-exchange coherence certificate ledger exposes no imported finite rectangles. -/
theorem TraceCoherenceCell.scheduleExchangeCertificateLedger_importedRectangles
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.scheduleExchangeCertificateLedger
      source
      target).importedRectangles =
      [] ++ ([] ++ ([] ++ [])) :=
  rfl

/-- A residue-channel coherence certificate ledger exposes no imported finite rectangles. -/
theorem TraceCoherenceCell.residueChannelCertificateLedger_importedRectangles
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.residueChannelCertificateLedger
      source
      target).importedRectangles =
      [] ++ ([] ++ ([] ++ [])) :=
  rfl

/-- A Stokes-residue coherence certificate ledger exposes no imported finite rectangles. -/
theorem TraceCoherenceCell.stokesResidueCertificateLedger_importedRectangles
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.stokesResidueCertificateLedger
      source
      target).importedRectangles =
      [] ++ ([] ++ ([] ++ [])) :=
  rfl

/-- A refinement coherence certificate ledger exposes no imported finite rectangles. -/
theorem TraceCoherenceCell.refinementCertificateLedger_importedRectangles
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.refinementCertificateLedger
      source
      target).importedRectangles =
      [] ++ ([] ++ ([] ++ [])) :=
  rfl

/-- An associativity coherence certificate ledger exposes no imported finite rectangles. -/
theorem TraceCoherenceCell.associativityCertificateLedger_importedRectangles
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.associativityCertificateLedger
      source
      target).importedRectangles =
      [] ++ ([] ++ ([] ++ [])) :=
  rfl

/-- A left-identity coherence certificate ledger exposes no imported finite rectangles. -/
theorem TraceCoherenceCell.leftIdentityCertificateLedger_importedRectangles
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.leftIdentityCertificateLedger
      source
      target).importedRectangles =
      [] ++ ([] ++ ([] ++ [])) :=
  rfl

/-- A right-identity coherence certificate ledger exposes no imported finite rectangles. -/
theorem TraceCoherenceCell.rightIdentityCertificateLedger_importedRectangles
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.rightIdentityCertificateLedger
      source
      target).importedRectangles =
      [] ++ ([] ++ ([] ++ [])) :=
  rfl

/-- A Fubini coherence certificate ledger count is the length of its rectangle list. -/
theorem TraceCoherenceCell.fubiniCertificateLedger_importedRectangleCount_eq_length
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.fubiniCertificateLedger
      source
      target).importedRectangleCount =
      (TraceCoherenceCell.fubiniCertificateLedger
        source
        target).importedRectangles.length :=
  ResidueChannelCertificateLedger.importedRectangleCount_eq_length_importedRectangles
    (TraceCoherenceCell.fubiniCertificateLedger source target)

/-- A schedule-exchange coherence certificate ledger count is the length of its rectangle list. -/
theorem TraceCoherenceCell.scheduleExchangeCertificateLedger_importedRectangleCount_eq_length
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.scheduleExchangeCertificateLedger
      source
      target).importedRectangleCount =
      (TraceCoherenceCell.scheduleExchangeCertificateLedger
        source
        target).importedRectangles.length :=
  ResidueChannelCertificateLedger.importedRectangleCount_eq_length_importedRectangles
    (TraceCoherenceCell.scheduleExchangeCertificateLedger source target)

/-- A residue-channel coherence certificate ledger count is the length of its rectangle list. -/
theorem TraceCoherenceCell.residueChannelCertificateLedger_importedRectangleCount_eq_length
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.residueChannelCertificateLedger
      source
      target).importedRectangleCount =
      (TraceCoherenceCell.residueChannelCertificateLedger
        source
        target).importedRectangles.length :=
  ResidueChannelCertificateLedger.importedRectangleCount_eq_length_importedRectangles
    (TraceCoherenceCell.residueChannelCertificateLedger source target)

/-- A Stokes-residue coherence certificate ledger count is the length of its rectangle list. -/
theorem TraceCoherenceCell.stokesResidueCertificateLedger_importedRectangleCount_eq_length
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.stokesResidueCertificateLedger
      source
      target).importedRectangleCount =
      (TraceCoherenceCell.stokesResidueCertificateLedger
        source
        target).importedRectangles.length :=
  ResidueChannelCertificateLedger.importedRectangleCount_eq_length_importedRectangles
    (TraceCoherenceCell.stokesResidueCertificateLedger source target)

/-- A refinement coherence certificate ledger count is the length of its rectangle list. -/
theorem TraceCoherenceCell.refinementCertificateLedger_importedRectangleCount_eq_length
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.refinementCertificateLedger
      source
      target).importedRectangleCount =
      (TraceCoherenceCell.refinementCertificateLedger
        source
        target).importedRectangles.length :=
  ResidueChannelCertificateLedger.importedRectangleCount_eq_length_importedRectangles
    (TraceCoherenceCell.refinementCertificateLedger source target)

/-- An associativity coherence certificate ledger count is the length of its rectangle list. -/
theorem TraceCoherenceCell.associativityCertificateLedger_importedRectangleCount_eq_length
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.associativityCertificateLedger
      source
      target).importedRectangleCount =
      (TraceCoherenceCell.associativityCertificateLedger
        source
        target).importedRectangles.length :=
  ResidueChannelCertificateLedger.importedRectangleCount_eq_length_importedRectangles
    (TraceCoherenceCell.associativityCertificateLedger source target)

/-- A left-identity coherence certificate ledger count is the length of its rectangle list. -/
theorem TraceCoherenceCell.leftIdentityCertificateLedger_importedRectangleCount_eq_length
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.leftIdentityCertificateLedger
      source
      target).importedRectangleCount =
      (TraceCoherenceCell.leftIdentityCertificateLedger
        source
        target).importedRectangles.length :=
  ResidueChannelCertificateLedger.importedRectangleCount_eq_length_importedRectangles
    (TraceCoherenceCell.leftIdentityCertificateLedger source target)

/-- A right-identity coherence certificate ledger count is the length of its rectangle list. -/
theorem TraceCoherenceCell.rightIdentityCertificateLedger_importedRectangleCount_eq_length
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.rightIdentityCertificateLedger
      source
      target).importedRectangleCount =
      (TraceCoherenceCell.rightIdentityCertificateLedger
        source
        target).importedRectangles.length :=
  ResidueChannelCertificateLedger.importedRectangleCount_eq_length_importedRectangles
    (TraceCoherenceCell.rightIdentityCertificateLedger source target)

/-- A Fubini coherence certificate ledger has source-path, target-path, and cell bookkeeping. -/
theorem TraceCoherenceCell.fubiniCertificateLedger_traceBookkeepingCount
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.fubiniCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + (1 + (1 + 0)) :=
  rfl

/-- A schedule-exchange coherence certificate ledger has source-path, target-path, and cell bookkeeping. -/
theorem TraceCoherenceCell.scheduleExchangeCertificateLedger_traceBookkeepingCount
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.scheduleExchangeCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + (1 + (1 + 0)) :=
  rfl

/-- A residue-channel coherence certificate ledger has source-path, target-path, and cell bookkeeping. -/
theorem TraceCoherenceCell.residueChannelCertificateLedger_traceBookkeepingCount
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.residueChannelCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + (1 + (1 + 0)) :=
  rfl

/-- A Stokes-residue coherence certificate ledger has source-path, target-path, and cell bookkeeping. -/
theorem TraceCoherenceCell.stokesResidueCertificateLedger_traceBookkeepingCount
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.stokesResidueCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + (1 + (1 + 0)) :=
  rfl

/-- A refinement coherence certificate ledger has source-path, target-path, and cell bookkeeping. -/
theorem TraceCoherenceCell.refinementCertificateLedger_traceBookkeepingCount
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.refinementCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + (1 + (1 + 0)) :=
  rfl

/-- An associativity coherence certificate ledger has source-path, target-path, and cell bookkeeping. -/
theorem TraceCoherenceCell.associativityCertificateLedger_traceBookkeepingCount
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.associativityCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + (1 + (1 + 0)) :=
  rfl

/-- A left-identity coherence certificate ledger has source-path, target-path, and cell bookkeeping. -/
theorem TraceCoherenceCell.leftIdentityCertificateLedger_traceBookkeepingCount
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.leftIdentityCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + (1 + (1 + 0)) :=
  rfl

/-- A right-identity coherence certificate ledger has source-path, target-path, and cell bookkeeping. -/
theorem TraceCoherenceCell.rightIdentityCertificateLedger_traceBookkeepingCount
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.rightIdentityCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + (1 + (1 + 0)) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

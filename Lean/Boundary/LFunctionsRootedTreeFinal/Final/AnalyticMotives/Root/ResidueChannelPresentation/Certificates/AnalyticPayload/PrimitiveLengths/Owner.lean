import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Certificates.AnalyticPayload.PrimitiveLengths.Owner

/-!
# Top-root primitive certificate-ledger length facts

This file exposes imported-rectangle count-as-length facts for primitive
analytic certificate ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes count-as-length for explicit-rectangle ledgers. -/
theorem AnalyticMotivesRoot.residueChannelCertificateLedger_ofExplicitFormulaRectangle_importedRectangleCount_eq_length
    (rectangle :
      ZetaAdmissibleFunction.ExplicitFormulaRectangle) :
    (ResidueChannelCertificateLedger.ofExplicitFormulaRectangle
      rectangle).importedRectangleCount =
      (ResidueChannelCertificateLedger.ofExplicitFormulaRectangle
        rectangle).importedRectangles.length :=
  ResidueChannelCertificateLedger.ofExplicitFormulaRectangle_importedRectangleCount_eq_length
    rectangle

/-- The top root exposes count-as-length for rewrite-path ledgers. -/
theorem AnalyticMotivesRoot.residueChannelCertificateLedger_ofRewritePath_importedRectangleCount_eq_length
    (path : TraceRewritePath) :
    (ResidueChannelCertificateLedger.ofRewritePath
      path).importedRectangleCount =
      (ResidueChannelCertificateLedger.ofRewritePath
        path).importedRectangles.length :=
  ResidueChannelCertificateLedger.ofRewritePath_importedRectangleCount_eq_length
    path

/-- The top root exposes count-as-length for certified-coherence-cell ledgers. -/
theorem AnalyticMotivesRoot.residueChannelCertificateLedger_ofCertifiedCoherenceCell_importedRectangleCount_eq_length
    (cell : TraceCoherenceCell) :
    (ResidueChannelCertificateLedger.ofCertifiedCoherenceCell
      cell).importedRectangleCount =
      (ResidueChannelCertificateLedger.ofCertifiedCoherenceCell
        cell).importedRectangles.length :=
  ResidueChannelCertificateLedger.ofCertifiedCoherenceCell_importedRectangleCount_eq_length
    cell

end AnalyticMotives
end LFunctions
end Boundary

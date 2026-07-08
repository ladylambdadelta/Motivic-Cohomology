import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Certificates.AnalyticPayload.Owner

/-!
# Primitive certificate-ledger length facts

This file owns the constructor-level length invariants for primitive analytic
certificate ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The explicit-rectangle ledger count is the length of its rectangle list. -/
theorem ResidueChannelCertificateLedger.ofExplicitFormulaRectangle_importedRectangleCount_eq_length
    (rectangle :
      ZetaAdmissibleFunction.ExplicitFormulaRectangle) :
    (ResidueChannelCertificateLedger.ofExplicitFormulaRectangle
      rectangle).importedRectangleCount =
      (ResidueChannelCertificateLedger.ofExplicitFormulaRectangle
        rectangle).importedRectangles.length :=
  ResidueChannelCertificateLedger.importedRectangleCount_eq_length_importedRectangles
    (ResidueChannelCertificateLedger.ofExplicitFormulaRectangle rectangle)

/-- The rewrite-path ledger count is the length of its empty rectangle list. -/
theorem ResidueChannelCertificateLedger.ofRewritePath_importedRectangleCount_eq_length
    (path : TraceRewritePath) :
    (ResidueChannelCertificateLedger.ofRewritePath
      path).importedRectangleCount =
      (ResidueChannelCertificateLedger.ofRewritePath
        path).importedRectangles.length :=
  ResidueChannelCertificateLedger.importedRectangleCount_eq_length_importedRectangles
    (ResidueChannelCertificateLedger.ofRewritePath path)

/-- The coherence-cell ledger count is the length of its empty rectangle list. -/
theorem ResidueChannelCertificateLedger.ofCertifiedCoherenceCell_importedRectangleCount_eq_length
    (cell : TraceCoherenceCell) :
    (ResidueChannelCertificateLedger.ofCertifiedCoherenceCell
      cell).importedRectangleCount =
      (ResidueChannelCertificateLedger.ofCertifiedCoherenceCell
        cell).importedRectangles.length :=
  ResidueChannelCertificateLedger.importedRectangleCount_eq_length_importedRectangles
    (ResidueChannelCertificateLedger.ofCertifiedCoherenceCell cell)

end AnalyticMotives
end LFunctions
end Boundary

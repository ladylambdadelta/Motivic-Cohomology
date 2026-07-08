import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Certificates.AnalyticPayload.Atoms.Owner

/-!
# Top-root analytic payload of certificate atoms

This file exposes imported-rectangle and trace-calculus payload accounting for
individual residue-channel certificate atoms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes imported rectangle counts for certificate atoms. -/
def AnalyticMotivesRoot.residueChannelCertificateAtom_importedRectangleCount
    (atom : ResidueChannelCertificateAtom) :
    Nat :=
  ResidueChannelCertificateAtom.importedRectangleCount atom

/-- The top root exposes trace-bookkeeping counts for certificate atoms. -/
def AnalyticMotivesRoot.residueChannelCertificateAtom_traceBookkeepingCount
    (atom : ResidueChannelCertificateAtom) :
    Nat :=
  ResidueChannelCertificateAtom.traceBookkeepingCount atom

/-- The top root exposes rewrite-step counts for certificate atoms. -/
def AnalyticMotivesRoot.residueChannelCertificateAtom_rewriteStepCount
    (atom : ResidueChannelCertificateAtom) :
    Nat :=
  ResidueChannelCertificateAtom.rewriteStepCount atom

/-- The top root exposes imported rectangles for certificate atoms. -/
def AnalyticMotivesRoot.residueChannelCertificateAtom_importedRectangles
    (atom : ResidueChannelCertificateAtom) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  ResidueChannelCertificateAtom.importedRectangles atom

/-- The top root exposes imported rectangle counts for explicit rectangle atoms. -/
theorem AnalyticMotivesRoot.residueChannelCertificateAtom_explicitFormulaRectangle_importedRectangleCount
    (rectangle :
      ZetaAdmissibleFunction.ExplicitFormulaRectangle) :
    (ResidueChannelCertificateAtom.explicitFormulaRectangle
      rectangle).importedRectangleCount =
      1 :=
  ResidueChannelCertificateAtom.explicitFormulaRectangle_importedRectangleCount
    rectangle

/-- The top root exposes bookkeeping counts for explicit rectangle atoms. -/
theorem AnalyticMotivesRoot.residueChannelCertificateAtom_explicitFormulaRectangle_traceBookkeepingCount
    (rectangle :
      ZetaAdmissibleFunction.ExplicitFormulaRectangle) :
    (ResidueChannelCertificateAtom.explicitFormulaRectangle
      rectangle).traceBookkeepingCount =
      0 :=
  ResidueChannelCertificateAtom.explicitFormulaRectangle_traceBookkeepingCount
    rectangle

/-- The top root exposes imported rectangle lists for explicit rectangle atoms. -/
theorem AnalyticMotivesRoot.residueChannelCertificateAtom_explicitFormulaRectangle_importedRectangles
    (rectangle :
      ZetaAdmissibleFunction.ExplicitFormulaRectangle) :
    (ResidueChannelCertificateAtom.explicitFormulaRectangle
      rectangle).importedRectangles =
      [rectangle] :=
  ResidueChannelCertificateAtom.explicitFormulaRectangle_importedRectangles
    rectangle

/-- The top root exposes bookkeeping counts for rewrite-path atoms. -/
theorem AnalyticMotivesRoot.residueChannelCertificateAtom_rewritePath_traceBookkeepingCount
    (path : TraceRewritePath) :
    (ResidueChannelCertificateAtom.rewritePath path).traceBookkeepingCount =
      1 :=
  ResidueChannelCertificateAtom.rewritePath_traceBookkeepingCount path

/-- The top root exposes rewrite-step counts for rewrite-path atoms. -/
theorem AnalyticMotivesRoot.residueChannelCertificateAtom_rewritePath_rewriteStepCount
    (path : TraceRewritePath) :
    (ResidueChannelCertificateAtom.rewritePath path).rewriteStepCount =
      path.stepCount :=
  ResidueChannelCertificateAtom.rewritePath_rewriteStepCount path

/-- The top root exposes imported rectangle counts for rewrite-path atoms. -/
theorem AnalyticMotivesRoot.residueChannelCertificateAtom_rewritePath_importedRectangleCount
    (path : TraceRewritePath) :
    (ResidueChannelCertificateAtom.rewritePath path).importedRectangleCount =
      0 :=
  ResidueChannelCertificateAtom.rewritePath_importedRectangleCount path

/-- The top root exposes imported rectangle lists for rewrite-path atoms. -/
theorem AnalyticMotivesRoot.residueChannelCertificateAtom_rewritePath_importedRectangles
    (path : TraceRewritePath) :
    (ResidueChannelCertificateAtom.rewritePath path).importedRectangles =
      [] :=
  ResidueChannelCertificateAtom.rewritePath_importedRectangles path

/-- The top root exposes atom imported rectangle count as rectangle-list length. -/
theorem AnalyticMotivesRoot.residueChannelCertificateAtom_importedRectangleCount_eq_length_importedRectangles
    (atom : ResidueChannelCertificateAtom) :
    atom.importedRectangleCount =
      atom.importedRectangles.length :=
  ResidueChannelCertificateAtom.importedRectangleCount_eq_length_importedRectangles
    atom

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Certificates.Owner

/-!
# Analytic payload of certificate atoms

This file separates imported analytic payload from internal trace-calculus
bookkeeping at the certificate-atom level.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The number of imported finite-rectangle analytic artifacts carried by one atom. -/
def ResidueChannelCertificateAtom.importedRectangleCount :
    ResidueChannelCertificateAtom → Nat
  | ResidueChannelCertificateAtom.sourceExpression _ => 0
  | ResidueChannelCertificateAtom.residueLedger _ => 0
  | ResidueChannelCertificateAtom.channelExpression _ => 0
  | ResidueChannelCertificateAtom.channelList _ => 0
  | ResidueChannelCertificateAtom.traceSchedule _ => 0
  | ResidueChannelCertificateAtom.rewritePath _ => 0
  | ResidueChannelCertificateAtom.coherenceCell _ => 0
  | ResidueChannelCertificateAtom.explicitFormulaRectangle _ => 1

/-- The number of internal trace-calculus bookkeeping atoms carried by one atom. -/
def ResidueChannelCertificateAtom.traceBookkeepingCount :
    ResidueChannelCertificateAtom → Nat
  | ResidueChannelCertificateAtom.sourceExpression _ => 1
  | ResidueChannelCertificateAtom.residueLedger _ => 1
  | ResidueChannelCertificateAtom.channelExpression _ => 1
  | ResidueChannelCertificateAtom.channelList _ => 1
  | ResidueChannelCertificateAtom.traceSchedule _ => 1
  | ResidueChannelCertificateAtom.rewritePath _ => 1
  | ResidueChannelCertificateAtom.coherenceCell _ => 1
  | ResidueChannelCertificateAtom.explicitFormulaRectangle _ => 0

/-- The number of one-step rewrite generators explicitly carried by one atom. -/
def ResidueChannelCertificateAtom.rewriteStepCount :
    ResidueChannelCertificateAtom → Nat
  | ResidueChannelCertificateAtom.sourceExpression _ => 0
  | ResidueChannelCertificateAtom.residueLedger _ => 0
  | ResidueChannelCertificateAtom.channelExpression _ => 0
  | ResidueChannelCertificateAtom.channelList _ => 0
  | ResidueChannelCertificateAtom.traceSchedule _ => 0
  | ResidueChannelCertificateAtom.rewritePath path => path.stepCount
  | ResidueChannelCertificateAtom.coherenceCell _ => 0
  | ResidueChannelCertificateAtom.explicitFormulaRectangle _ => 0

/-- The imported finite explicit-formula rectangles carried by one atom. -/
def ResidueChannelCertificateAtom.importedRectangles :
    ResidueChannelCertificateAtom →
      List ZetaAdmissibleFunction.ExplicitFormulaRectangle
  | ResidueChannelCertificateAtom.sourceExpression _ => []
  | ResidueChannelCertificateAtom.residueLedger _ => []
  | ResidueChannelCertificateAtom.channelExpression _ => []
  | ResidueChannelCertificateAtom.channelList _ => []
  | ResidueChannelCertificateAtom.traceSchedule _ => []
  | ResidueChannelCertificateAtom.rewritePath _ => []
  | ResidueChannelCertificateAtom.coherenceCell _ => []
  | ResidueChannelCertificateAtom.explicitFormulaRectangle rectangle =>
      [rectangle]

/-- A finite explicit-formula rectangle atom contributes one imported rectangle. -/
theorem ResidueChannelCertificateAtom.explicitFormulaRectangle_importedRectangleCount
    (rectangle :
      ZetaAdmissibleFunction.ExplicitFormulaRectangle) :
    (ResidueChannelCertificateAtom.explicitFormulaRectangle
      rectangle).importedRectangleCount =
      1 :=
  rfl

/-- A finite explicit-formula rectangle atom is not internal bookkeeping. -/
theorem ResidueChannelCertificateAtom.explicitFormulaRectangle_traceBookkeepingCount
    (rectangle :
      ZetaAdmissibleFunction.ExplicitFormulaRectangle) :
    (ResidueChannelCertificateAtom.explicitFormulaRectangle
      rectangle).traceBookkeepingCount =
      0 :=
  rfl

/-- A finite explicit-formula rectangle atom exposes exactly that rectangle. -/
theorem ResidueChannelCertificateAtom.explicitFormulaRectangle_importedRectangles
    (rectangle :
      ZetaAdmissibleFunction.ExplicitFormulaRectangle) :
    (ResidueChannelCertificateAtom.explicitFormulaRectangle
      rectangle).importedRectangles =
      [rectangle] :=
  rfl

/-- A rewrite-path atom is internal trace bookkeeping. -/
theorem ResidueChannelCertificateAtom.rewritePath_traceBookkeepingCount
    (path : TraceRewritePath) :
    (ResidueChannelCertificateAtom.rewritePath path).traceBookkeepingCount =
      1 :=
  rfl

/-- A rewrite-path atom carries the one-step generator count of its path. -/
theorem ResidueChannelCertificateAtom.rewritePath_rewriteStepCount
    (path : TraceRewritePath) :
    (ResidueChannelCertificateAtom.rewritePath path).rewriteStepCount =
      path.stepCount :=
  rfl

/-- A rewrite-path atom carries no imported finite rectangle. -/
theorem ResidueChannelCertificateAtom.rewritePath_importedRectangleCount
    (path : TraceRewritePath) :
    (ResidueChannelCertificateAtom.rewritePath path).importedRectangleCount =
      0 :=
  rfl

/-- A rewrite-path atom exposes no imported finite explicit-formula rectangles. -/
theorem ResidueChannelCertificateAtom.rewritePath_importedRectangles
    (path : TraceRewritePath) :
    (ResidueChannelCertificateAtom.rewritePath path).importedRectangles =
      [] :=
  rfl

/-- The number of imported rectangles in one atom is the length of its rectangle list. -/
theorem ResidueChannelCertificateAtom.importedRectangleCount_eq_length_importedRectangles
    (atom : ResidueChannelCertificateAtom) :
    atom.importedRectangleCount =
      atom.importedRectangles.length :=
  match atom with
  | ResidueChannelCertificateAtom.sourceExpression _ => rfl
  | ResidueChannelCertificateAtom.residueLedger _ => rfl
  | ResidueChannelCertificateAtom.channelExpression _ => rfl
  | ResidueChannelCertificateAtom.channelList _ => rfl
  | ResidueChannelCertificateAtom.traceSchedule _ => rfl
  | ResidueChannelCertificateAtom.rewritePath _ => rfl
  | ResidueChannelCertificateAtom.coherenceCell _ => rfl
  | ResidueChannelCertificateAtom.explicitFormulaRectangle _ => rfl

end AnalyticMotives
end LFunctions
end Boundary

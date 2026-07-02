import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Certificates.Owner

/-!
# Analytic payload of certificate ledgers

This file separates imported analytic payload from internal trace-calculus
bookkeeping inside a certificate ledger.

The current concrete imported analytic artifact is a finite explicit-formula
rectangle from the RH lane.  Other atoms are still useful ledger atoms, but
they are counted here as trace bookkeeping rather than as imported analytic
payload.
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

/-- Count imported finite-rectangle analytic artifacts in a certificate ledger. -/
def ResidueChannelCertificateLedger.importedRectangleCount :
    ResidueChannelCertificateLedger → Nat
  | [] => 0
  | atom :: tail =>
      atom.importedRectangleCount +
        tail.importedRectangleCount

/-- Count internal trace-calculus bookkeeping atoms in a certificate ledger. -/
def ResidueChannelCertificateLedger.traceBookkeepingCount :
    ResidueChannelCertificateLedger → Nat
  | [] => 0
  | atom :: tail =>
      atom.traceBookkeepingCount +
        tail.traceBookkeepingCount

/-- Count one-step rewrite generators explicitly carried by a certificate ledger. -/
def ResidueChannelCertificateLedger.rewriteStepCount :
    ResidueChannelCertificateLedger → Nat
  | [] => 0
  | atom :: tail =>
      atom.rewriteStepCount +
        tail.rewriteStepCount

/-- The empty ledger carries no imported finite rectangles. -/
theorem ResidueChannelCertificateLedger.empty_importedRectangleCount :
    ResidueChannelCertificateLedger.empty.importedRectangleCount =
      0 :=
  rfl

/-- The empty ledger carries no internal trace bookkeeping. -/
theorem ResidueChannelCertificateLedger.empty_traceBookkeepingCount :
    ResidueChannelCertificateLedger.empty.traceBookkeepingCount =
      0 :=
  rfl

/-- The empty ledger carries no explicit rewrite steps. -/
theorem ResidueChannelCertificateLedger.empty_rewriteStepCount :
    ResidueChannelCertificateLedger.empty.rewriteStepCount =
      0 :=
  rfl

/-- A cons ledger has imported-rectangle count equal to head plus tail. -/
theorem ResidueChannelCertificateLedger.cons_importedRectangleCount
    (atom : ResidueChannelCertificateAtom)
    (ledger : ResidueChannelCertificateLedger) :
    (ResidueChannelCertificateLedger.cons
      atom
      ledger).importedRectangleCount =
      atom.importedRectangleCount +
        ledger.importedRectangleCount :=
  rfl

/-- A cons ledger has bookkeeping count equal to head plus tail. -/
theorem ResidueChannelCertificateLedger.cons_traceBookkeepingCount
    (atom : ResidueChannelCertificateAtom)
    (ledger : ResidueChannelCertificateLedger) :
    (ResidueChannelCertificateLedger.cons
      atom
      ledger).traceBookkeepingCount =
      atom.traceBookkeepingCount +
        ledger.traceBookkeepingCount :=
  rfl

/-- A cons ledger has rewrite-step count equal to head plus tail. -/
theorem ResidueChannelCertificateLedger.cons_rewriteStepCount
    (atom : ResidueChannelCertificateAtom)
    (ledger : ResidueChannelCertificateLedger) :
    (ResidueChannelCertificateLedger.cons
      atom
      ledger).rewriteStepCount =
      atom.rewriteStepCount +
        ledger.rewriteStepCount :=
  rfl

/-- A singleton ledger has the imported-rectangle count of its atom. -/
theorem ResidueChannelCertificateLedger.singleton_importedRectangleCount
    (atom : ResidueChannelCertificateAtom) :
    (ResidueChannelCertificateLedger.singleton
      atom).importedRectangleCount =
      atom.importedRectangleCount +
        0 :=
  rfl

/-- A singleton ledger has the bookkeeping count of its atom. -/
theorem ResidueChannelCertificateLedger.singleton_traceBookkeepingCount
    (atom : ResidueChannelCertificateAtom) :
    (ResidueChannelCertificateLedger.singleton
      atom).traceBookkeepingCount =
      atom.traceBookkeepingCount +
        0 :=
  rfl

/-- A singleton ledger has the rewrite-step count of its atom. -/
theorem ResidueChannelCertificateLedger.singleton_rewriteStepCount
    (atom : ResidueChannelCertificateAtom) :
    (ResidueChannelCertificateLedger.singleton
      atom).rewriteStepCount =
      atom.rewriteStepCount +
        0 :=
  rfl

/-- Appending ledgers adds imported finite-rectangle counts. -/
theorem ResidueChannelCertificateLedger.append_importedRectangleCount
    (first second : ResidueChannelCertificateLedger) :
    (ResidueChannelCertificateLedger.append
      first
      second).importedRectangleCount =
      first.importedRectangleCount +
        second.importedRectangleCount :=
  match first with
  | [] => rfl
  | atom :: tail =>
      Eq.trans
        (congrArg
          (fun count =>
            atom.importedRectangleCount + count)
          (ResidueChannelCertificateLedger.append_importedRectangleCount
            tail
            second))
        (Eq.symm
          (Nat.add_assoc
          atom.importedRectangleCount
          tail.importedRectangleCount
            second.importedRectangleCount))

/-- Appending ledgers adds internal trace-bookkeeping counts. -/
theorem ResidueChannelCertificateLedger.append_traceBookkeepingCount
    (first second : ResidueChannelCertificateLedger) :
    (ResidueChannelCertificateLedger.append
      first
      second).traceBookkeepingCount =
      first.traceBookkeepingCount +
        second.traceBookkeepingCount :=
  match first with
  | [] => rfl
  | atom :: tail =>
      Eq.trans
        (congrArg
          (fun count =>
            atom.traceBookkeepingCount + count)
          (ResidueChannelCertificateLedger.append_traceBookkeepingCount
            tail
            second))
        (Eq.symm
          (Nat.add_assoc
          atom.traceBookkeepingCount
          tail.traceBookkeepingCount
            second.traceBookkeepingCount))

/-- Appending ledgers adds explicit rewrite-step counts. -/
theorem ResidueChannelCertificateLedger.append_rewriteStepCount
    (first second : ResidueChannelCertificateLedger) :
    (ResidueChannelCertificateLedger.append
      first
      second).rewriteStepCount =
      first.rewriteStepCount +
        second.rewriteStepCount :=
  match first with
  | [] => rfl
  | atom :: tail =>
      Eq.trans
        (congrArg
          (fun count =>
            atom.rewriteStepCount + count)
          (ResidueChannelCertificateLedger.append_rewriteStepCount
            tail
            second))
        (Eq.symm
          (Nat.add_assoc
          atom.rewriteStepCount
          tail.rewriteStepCount
            second.rewriteStepCount))

/-- The explicit-rectangle ledger carries exactly one imported rectangle. -/
theorem ResidueChannelCertificateLedger.ofExplicitFormulaRectangle_importedRectangleCount
    (rectangle :
      ZetaAdmissibleFunction.ExplicitFormulaRectangle) :
    (ResidueChannelCertificateLedger.ofExplicitFormulaRectangle
      rectangle).importedRectangleCount =
      1 + 0 :=
  rfl

/-- The explicit-rectangle ledger carries no internal bookkeeping atoms. -/
theorem ResidueChannelCertificateLedger.ofExplicitFormulaRectangle_traceBookkeepingCount
    (rectangle :
      ZetaAdmissibleFunction.ExplicitFormulaRectangle) :
    (ResidueChannelCertificateLedger.ofExplicitFormulaRectangle
      rectangle).traceBookkeepingCount =
      0 + 0 :=
  rfl

/-- The explicit-rectangle ledger carries no explicit rewrite steps. -/
theorem ResidueChannelCertificateLedger.ofExplicitFormulaRectangle_rewriteStepCount
    (rectangle :
      ZetaAdmissibleFunction.ExplicitFormulaRectangle) :
    (ResidueChannelCertificateLedger.ofExplicitFormulaRectangle
      rectangle).rewriteStepCount =
      0 + 0 :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

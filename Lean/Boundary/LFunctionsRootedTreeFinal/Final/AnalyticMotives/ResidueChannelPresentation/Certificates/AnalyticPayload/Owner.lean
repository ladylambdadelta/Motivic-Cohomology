import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Certificates.AnalyticPayload.Atoms.Owner

/-!
# Analytic payload of certificate ledgers

This file lifts imported analytic payload and internal trace-calculus
bookkeeping from certificate atoms to certificate ledgers.

The current concrete imported analytic artifact is a finite explicit-formula
rectangle from the RH lane.  Other atoms are still useful ledger atoms, but
they are counted here as trace bookkeeping rather than as imported analytic
payload.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Count imported finite-rectangle analytic artifacts in a certificate ledger. -/
def ResidueChannelCertificateLedger.importedRectangleCount :
    ResidueChannelCertificateLedger → Nat
  | [] => 0
  | atom :: tail =>
      atom.importedRectangleCount +
        ResidueChannelCertificateLedger.importedRectangleCount tail

/-- Count internal trace-calculus bookkeeping atoms in a certificate ledger. -/
def ResidueChannelCertificateLedger.traceBookkeepingCount :
    ResidueChannelCertificateLedger → Nat
  | [] => 0
  | atom :: tail =>
      atom.traceBookkeepingCount +
        ResidueChannelCertificateLedger.traceBookkeepingCount tail

/-- Count one-step rewrite generators explicitly carried by a certificate ledger. -/
def ResidueChannelCertificateLedger.rewriteStepCount :
    ResidueChannelCertificateLedger → Nat
  | [] => 0
  | atom :: tail =>
      atom.rewriteStepCount +
        ResidueChannelCertificateLedger.rewriteStepCount tail

/-- The imported finite explicit-formula rectangles carried by a certificate ledger. -/
def ResidueChannelCertificateLedger.importedRectangles :
    ResidueChannelCertificateLedger →
      List ZetaAdmissibleFunction.ExplicitFormulaRectangle
  | [] => []
  | atom :: tail =>
      atom.importedRectangles ++
        ResidueChannelCertificateLedger.importedRectangles tail

/-- The empty ledger carries no imported finite rectangles. -/
theorem ResidueChannelCertificateLedger.empty_importedRectangleCount :
    ResidueChannelCertificateLedger.empty.importedRectangleCount =
      0 :=
  rfl

/-- The empty ledger exposes no imported finite explicit-formula rectangles. -/
theorem ResidueChannelCertificateLedger.empty_importedRectangles :
    ResidueChannelCertificateLedger.empty.importedRectangles =
      [] :=
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

/-- A cons ledger exposes imported rectangles from the head followed by the tail. -/
theorem ResidueChannelCertificateLedger.cons_importedRectangles
    (atom : ResidueChannelCertificateAtom)
    (ledger : ResidueChannelCertificateLedger) :
    (ResidueChannelCertificateLedger.cons
      atom
      ledger).importedRectangles =
      atom.importedRectangles ++
        ledger.importedRectangles :=
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

/-- A singleton ledger exposes the imported rectangles of its atom. -/
theorem ResidueChannelCertificateLedger.singleton_importedRectangles
    (atom : ResidueChannelCertificateAtom) :
    (ResidueChannelCertificateLedger.singleton
      atom).importedRectangles =
      atom.importedRectangles ++
        [] :=
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
  | [] =>
      Eq.symm
        (Nat.zero_add
          second.importedRectangleCount)
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
          (ResidueChannelCertificateLedger.importedRectangleCount tail)
            second.importedRectangleCount))

/-- Appending ledgers concatenates their imported finite explicit-formula rectangles. -/
theorem ResidueChannelCertificateLedger.append_importedRectangles
    (first second : ResidueChannelCertificateLedger) :
    (ResidueChannelCertificateLedger.append
      first
      second).importedRectangles =
      first.importedRectangles ++
        second.importedRectangles :=
  match first with
  | [] => rfl
  | atom :: tail =>
      Eq.trans
        (congrArg
          (fun rectangles =>
            atom.importedRectangles ++ rectangles)
          (ResidueChannelCertificateLedger.append_importedRectangles
            tail
            second))
        (Eq.symm
          (List.append_assoc
            atom.importedRectangles
            (ResidueChannelCertificateLedger.importedRectangles tail)
            second.importedRectangles))

/-- Imported-rectangle count is the length of the extracted rectangle list. -/
theorem ResidueChannelCertificateLedger.importedRectangleCount_eq_length_importedRectangles
    (ledger : ResidueChannelCertificateLedger) :
    ledger.importedRectangleCount =
      ledger.importedRectangles.length :=
  match ledger with
  | [] => rfl
  | atom :: tail =>
      Eq.trans
        (congrArg
          (fun count =>
            count +
              ResidueChannelCertificateLedger.importedRectangleCount tail)
          (ResidueChannelCertificateAtom.importedRectangleCount_eq_length_importedRectangles
            atom))
        (Eq.trans
          (congrArg
            (fun count =>
            atom.importedRectangles.length + count)
            (ResidueChannelCertificateLedger.importedRectangleCount_eq_length_importedRectangles
              tail))
          (Eq.symm
            (List.length_append
              atom.importedRectangles
              (ResidueChannelCertificateLedger.importedRectangles tail))))

/-- Appending ledgers adds internal trace-bookkeeping counts. -/
theorem ResidueChannelCertificateLedger.append_traceBookkeepingCount
    (first second : ResidueChannelCertificateLedger) :
    (ResidueChannelCertificateLedger.append
      first
      second).traceBookkeepingCount =
      first.traceBookkeepingCount +
        second.traceBookkeepingCount :=
  match first with
  | [] =>
      Eq.symm
        (Nat.zero_add
          second.traceBookkeepingCount)
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
          (ResidueChannelCertificateLedger.traceBookkeepingCount tail)
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
  | [] =>
      Eq.symm
        (Nat.zero_add
          second.rewriteStepCount)
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
          (ResidueChannelCertificateLedger.rewriteStepCount tail)
            second.rewriteStepCount))

/-- The explicit-rectangle ledger carries exactly one imported rectangle. -/
theorem ResidueChannelCertificateLedger.ofExplicitFormulaRectangle_importedRectangleCount
    (rectangle :
      ZetaAdmissibleFunction.ExplicitFormulaRectangle) :
    (ResidueChannelCertificateLedger.ofExplicitFormulaRectangle
      rectangle).importedRectangleCount =
      1 + 0 :=
  rfl

/-- The explicit-rectangle ledger exposes exactly that imported rectangle. -/
theorem ResidueChannelCertificateLedger.ofExplicitFormulaRectangle_importedRectangles
    (rectangle :
      ZetaAdmissibleFunction.ExplicitFormulaRectangle) :
    (ResidueChannelCertificateLedger.ofExplicitFormulaRectangle
      rectangle).importedRectangles =
      [rectangle] ++ [] :=
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

/-- A rewrite-path certificate ledger carries no imported finite rectangles. -/
theorem ResidueChannelCertificateLedger.ofRewritePath_importedRectangleCount
    (path : TraceRewritePath) :
    (ResidueChannelCertificateLedger.ofRewritePath
      path).importedRectangleCount =
      0 + 0 :=
  rfl

/-- A rewrite-path certificate ledger exposes no imported finite rectangles. -/
theorem ResidueChannelCertificateLedger.ofRewritePath_importedRectangles
    (path : TraceRewritePath) :
    (ResidueChannelCertificateLedger.ofRewritePath
      path).importedRectangles =
      [] ++ [] :=
  rfl

/-- A rewrite-path certificate ledger is one internal bookkeeping atom. -/
theorem ResidueChannelCertificateLedger.ofRewritePath_traceBookkeepingCount
    (path : TraceRewritePath) :
    (ResidueChannelCertificateLedger.ofRewritePath
      path).traceBookkeepingCount =
      1 + 0 :=
  rfl

/-- A rewrite-path certificate ledger counts the path's rewrite steps. -/
theorem ResidueChannelCertificateLedger.ofRewritePath_rewriteStepCount
    (path : TraceRewritePath) :
    (ResidueChannelCertificateLedger.ofRewritePath
      path).rewriteStepCount =
      path.stepCount + 0 :=
  rfl

/-- A certified coherence-cell ledger carries no imported finite rectangles. -/
theorem ResidueChannelCertificateLedger.ofCertifiedCoherenceCell_importedRectangleCount
    (cell : TraceCoherenceCell) :
    (ResidueChannelCertificateLedger.ofCertifiedCoherenceCell
      cell).importedRectangleCount =
      0 + (0 + (0 + 0)) :=
  rfl

/-- A certified coherence-cell ledger exposes no imported finite rectangles. -/
theorem ResidueChannelCertificateLedger.ofCertifiedCoherenceCell_importedRectangles
    (cell : TraceCoherenceCell) :
    (ResidueChannelCertificateLedger.ofCertifiedCoherenceCell
      cell).importedRectangles =
      [] ++ ([] ++ ([] ++ [])) :=
  rfl

/-- A certified coherence-cell ledger counts source path, target path, and cell. -/
theorem ResidueChannelCertificateLedger.ofCertifiedCoherenceCell_traceBookkeepingCount
    (cell : TraceCoherenceCell) :
    (ResidueChannelCertificateLedger.ofCertifiedCoherenceCell
      cell).traceBookkeepingCount =
      1 + (1 + (1 + 0)) :=
  rfl

/-- A certified coherence-cell ledger counts rewrite steps from both compared paths. -/
theorem ResidueChannelCertificateLedger.ofCertifiedCoherenceCell_rewriteStepCount
    (cell : TraceCoherenceCell) :
    (ResidueChannelCertificateLedger.ofCertifiedCoherenceCell
      cell).rewriteStepCount =
      cell.source.stepCount + (cell.target.stepCount + (0 + 0)) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

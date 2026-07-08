import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.FormalSums.Composition.TermRight.Owner

/-!
# Top-root term-right formal-sum payloads

This file exposes term-right singleton and cons payload splits through the
top-level `AnalyticMotivesRoot` namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes term-right singleton certificate ledgers. -/
theorem AnalyticMotivesRoot.traceCorQTerm_compRight_singleton_certificateLedger
    (leftTerm : TraceCorQTerm)
    (rightCoefficient : Rat)
    (rightGenerator : TraceCorQGenerator) :
    (TraceCorQTerm.compRight
      leftTerm
      (TraceCorQFormalSum.singleton
        rightCoefficient
        rightGenerator)).certificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceCorQTerm.comp
          leftTerm
          (rightCoefficient, rightGenerator)).certificateLedger
        ResidueChannelCertificateLedger.empty :=
  TraceCorQ.term_compRight_singleton_certificateLedger
    leftTerm
    rightCoefficient
    rightGenerator

/-- The top root exposes term-right singleton imported payload. -/
theorem AnalyticMotivesRoot.traceCorQTerm_compRight_singleton_importedRectangleCount
    (leftTerm : TraceCorQTerm)
    (rightCoefficient : Rat)
    (rightGenerator : TraceCorQGenerator) :
    (TraceCorQTerm.compRight
      leftTerm
      (TraceCorQFormalSum.singleton
        rightCoefficient
        rightGenerator)).importedRectangleCount =
      (TraceCorQTerm.comp
        leftTerm
        (rightCoefficient, rightGenerator)).importedRectangleCount +
        ResidueChannelCertificateLedger.empty.importedRectangleCount :=
  TraceCorQ.term_compRight_singleton_importedRectangleCount
    leftTerm
    rightCoefficient
    rightGenerator

/-- The top root exposes term-right singleton imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQTerm_compRight_singleton_importedRectangles
    (leftTerm : TraceCorQTerm)
    (rightCoefficient : Rat)
    (rightGenerator : TraceCorQGenerator) :
    (TraceCorQTerm.compRight
      leftTerm
      (TraceCorQFormalSum.singleton
        rightCoefficient
        rightGenerator)).importedRectangles =
      (TraceCorQTerm.comp
        leftTerm
        (rightCoefficient, rightGenerator)).importedRectangles ++
        ResidueChannelCertificateLedger.empty.importedRectangles :=
  TraceCorQ.term_compRight_singleton_importedRectangles
    leftTerm
    rightCoefficient
    rightGenerator

/-- The top root exposes term-right singleton rewrite-step payload. -/
theorem AnalyticMotivesRoot.traceCorQTerm_compRight_singleton_rewriteStepCount
    (leftTerm : TraceCorQTerm)
    (rightCoefficient : Rat)
    (rightGenerator : TraceCorQGenerator) :
    (TraceCorQTerm.compRight
      leftTerm
      (TraceCorQFormalSum.singleton
        rightCoefficient
        rightGenerator)).rewriteStepCount =
      (TraceCorQTerm.comp
        leftTerm
        (rightCoefficient, rightGenerator)).rewriteStepCount +
        ResidueChannelCertificateLedger.empty.rewriteStepCount :=
  TraceCorQ.term_compRight_singleton_rewriteStepCount
    leftTerm
    rightCoefficient
    rightGenerator

/-- The top root exposes term-right cons certificate ledgers. -/
theorem AnalyticMotivesRoot.traceCorQTerm_compRight_cons_certificateLedger
    (leftTerm rightTerm : TraceCorQTerm)
    (rightTail : TraceCorQFormalSum) :
    (TraceCorQTerm.compRight
      leftTerm
      (rightTerm :: rightTail)).certificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceCorQTerm.comp leftTerm rightTerm).certificateLedger
        (TraceCorQTerm.compRight leftTerm rightTail).certificateLedger :=
  TraceCorQ.term_compRight_cons_certificateLedger
    leftTerm
    rightTerm
    rightTail

/-- The top root exposes term-right cons imported payload. -/
theorem AnalyticMotivesRoot.traceCorQTerm_compRight_cons_importedRectangleCount
    (leftTerm rightTerm : TraceCorQTerm)
    (rightTail : TraceCorQFormalSum) :
    (TraceCorQTerm.compRight
      leftTerm
      (rightTerm :: rightTail)).importedRectangleCount =
      (TraceCorQTerm.comp leftTerm rightTerm).importedRectangleCount +
        (TraceCorQTerm.compRight leftTerm rightTail).importedRectangleCount :=
  TraceCorQ.term_compRight_cons_importedRectangleCount
    leftTerm
    rightTerm
    rightTail

/-- The top root exposes term-right cons imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQTerm_compRight_cons_importedRectangles
    (leftTerm rightTerm : TraceCorQTerm)
    (rightTail : TraceCorQFormalSum) :
    (TraceCorQTerm.compRight
      leftTerm
      (rightTerm :: rightTail)).importedRectangles =
      (TraceCorQTerm.comp leftTerm rightTerm).importedRectangles ++
        (TraceCorQTerm.compRight leftTerm rightTail).importedRectangles :=
  TraceCorQ.term_compRight_cons_importedRectangles
    leftTerm
    rightTerm
    rightTail

/-- The top root exposes term-right cons rewrite-step payload. -/
theorem AnalyticMotivesRoot.traceCorQTerm_compRight_cons_rewriteStepCount
    (leftTerm rightTerm : TraceCorQTerm)
    (rightTail : TraceCorQFormalSum) :
    (TraceCorQTerm.compRight
      leftTerm
      (rightTerm :: rightTail)).rewriteStepCount =
      (TraceCorQTerm.comp leftTerm rightTerm).rewriteStepCount +
        (TraceCorQTerm.compRight leftTerm rightTail).rewriteStepCount :=
  TraceCorQ.term_compRight_cons_rewriteStepCount
    leftTerm
    rightTerm
    rightTail

/-- The top root exposes term-right composition with the zero formal sum. -/
theorem AnalyticMotivesRoot.traceCorQTerm_compRight_zero
    (term : TraceCorQTerm) :
    TraceCorQTerm.compRight
      term
      TraceCorQFormalSum.zero =
      TraceCorQFormalSum.zero :=
  TraceCorQ.term_compRight_zero
    term

/-- The top root exposes term-right distribution over addition. -/
theorem AnalyticMotivesRoot.traceCorQTerm_compRight_add
    (term : TraceCorQTerm)
    (left right : TraceCorQFormalSum) :
    TraceCorQTerm.compRight
      term
      (TraceCorQFormalSum.add left right) =
      TraceCorQFormalSum.add
        (TraceCorQTerm.compRight term left)
        (TraceCorQTerm.compRight term right) :=
  TraceCorQ.term_compRight_add
    term
    left
    right

/-- The top root exposes scaling the left term in term-right composition. -/
theorem AnalyticMotivesRoot.traceCorQTerm_smul_compRight
    (coefficient : Rat)
    (term : TraceCorQTerm)
    (formalSum : TraceCorQFormalSum) :
    TraceCorQTerm.compRight
      (coefficient * term.1, term.2)
      formalSum =
      TraceCorQFormalSum.smul
        coefficient
        (TraceCorQTerm.compRight term formalSum) :=
  TraceCorQ.term_smul_compRight
    coefficient
    term
    formalSum

/-- The top root exposes scaling the right formal sum in term-right composition. -/
theorem AnalyticMotivesRoot.traceCorQTerm_compRight_smul
    (coefficient : Rat)
    (term : TraceCorQTerm)
    (formalSum : TraceCorQFormalSum) :
    TraceCorQTerm.compRight
      term
      (TraceCorQFormalSum.smul coefficient formalSum) =
      TraceCorQFormalSum.smul
        coefficient
        (TraceCorQTerm.compRight term formalSum) :=
  TraceCorQ.term_compRight_smul
    coefficient
    term
    formalSum

end AnalyticMotives
end LFunctions
end Boundary

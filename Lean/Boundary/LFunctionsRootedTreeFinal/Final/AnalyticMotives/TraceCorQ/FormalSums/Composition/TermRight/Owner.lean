import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.FormalSums.Composition.Payload.Owner

/-!
# Public term-right composition payloads

This file exposes term-right singleton and cons payload splits under the
`TraceCorQ` aggregate namespace, while keeping the main aggregate owner below
the line cap.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes term-right singleton certificate ledgers. -/
theorem TraceCorQ.term_compRight_singleton_certificateLedger
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
  TraceCorQTerm.compRight_singleton_certificateLedger
    leftTerm
    rightCoefficient
    rightGenerator

/-- The trace-correspondence root exposes term-right singleton imported payload. -/
theorem TraceCorQ.term_compRight_singleton_importedRectangleCount
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
  TraceCorQTerm.compRight_singleton_importedRectangleCount
    leftTerm
    rightCoefficient
    rightGenerator

/-- The trace-correspondence root exposes term-right singleton imported rectangles. -/
theorem TraceCorQ.term_compRight_singleton_importedRectangles
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
  TraceCorQTerm.compRight_singleton_importedRectangles
    leftTerm
    rightCoefficient
    rightGenerator

/-- The trace-correspondence root exposes term-right singleton rewrite-step payload. -/
theorem TraceCorQ.term_compRight_singleton_rewriteStepCount
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
  TraceCorQTerm.compRight_singleton_rewriteStepCount
    leftTerm
    rightCoefficient
    rightGenerator

/-- The trace-correspondence root exposes term-right cons certificate ledgers. -/
theorem TraceCorQ.term_compRight_cons_certificateLedger
    (leftTerm rightTerm : TraceCorQTerm)
    (rightTail : TraceCorQFormalSum) :
    (TraceCorQTerm.compRight
      leftTerm
      (rightTerm :: rightTail)).certificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceCorQTerm.comp leftTerm rightTerm).certificateLedger
        (TraceCorQTerm.compRight leftTerm rightTail).certificateLedger :=
  TraceCorQTerm.compRight_cons_certificateLedger
    leftTerm
    rightTerm
    rightTail

/-- The trace-correspondence root exposes term-right cons imported payload. -/
theorem TraceCorQ.term_compRight_cons_importedRectangleCount
    (leftTerm rightTerm : TraceCorQTerm)
    (rightTail : TraceCorQFormalSum) :
    (TraceCorQTerm.compRight
      leftTerm
      (rightTerm :: rightTail)).importedRectangleCount =
      (TraceCorQTerm.comp leftTerm rightTerm).importedRectangleCount +
        (TraceCorQTerm.compRight leftTerm rightTail).importedRectangleCount :=
  TraceCorQTerm.compRight_cons_importedRectangleCount
    leftTerm
    rightTerm
    rightTail

/-- The trace-correspondence root exposes term-right cons imported rectangles. -/
theorem TraceCorQ.term_compRight_cons_importedRectangles
    (leftTerm rightTerm : TraceCorQTerm)
    (rightTail : TraceCorQFormalSum) :
    (TraceCorQTerm.compRight
      leftTerm
      (rightTerm :: rightTail)).importedRectangles =
      (TraceCorQTerm.comp leftTerm rightTerm).importedRectangles ++
        (TraceCorQTerm.compRight leftTerm rightTail).importedRectangles :=
  TraceCorQTerm.compRight_cons_importedRectangles
    leftTerm
    rightTerm
    rightTail

/-- The trace-correspondence root exposes term-right cons rewrite-step payload. -/
theorem TraceCorQ.term_compRight_cons_rewriteStepCount
    (leftTerm rightTerm : TraceCorQTerm)
    (rightTail : TraceCorQFormalSum) :
    (TraceCorQTerm.compRight
      leftTerm
      (rightTerm :: rightTail)).rewriteStepCount =
      (TraceCorQTerm.comp leftTerm rightTerm).rewriteStepCount +
        (TraceCorQTerm.compRight leftTerm rightTail).rewriteStepCount :=
  TraceCorQTerm.compRight_cons_rewriteStepCount
    leftTerm
    rightTerm
    rightTail

/-- The trace-correspondence root exposes term-right composition with the zero formal sum. -/
theorem TraceCorQ.term_compRight_zero
    (term : TraceCorQTerm) :
    TraceCorQTerm.compRight
      term
      TraceCorQFormalSum.zero =
      TraceCorQFormalSum.zero :=
  TraceCorQTerm.compRight_zero
    term

/-- The trace-correspondence root exposes term-right distribution over addition. -/
theorem TraceCorQ.term_compRight_add
    (term : TraceCorQTerm)
    (left right : TraceCorQFormalSum) :
    TraceCorQTerm.compRight
      term
      (TraceCorQFormalSum.add left right) =
      TraceCorQFormalSum.add
        (TraceCorQTerm.compRight term left)
        (TraceCorQTerm.compRight term right) :=
  TraceCorQTerm.compRight_add
    term
    left
    right

/-- The trace-correspondence root exposes scaling the left term in term-right composition. -/
theorem TraceCorQ.term_smul_compRight
    (coefficient : Rat)
    (term : TraceCorQTerm)
    (formalSum : TraceCorQFormalSum) :
    TraceCorQTerm.compRight
      (coefficient * term.1, term.2)
      formalSum =
      TraceCorQFormalSum.smul
        coefficient
        (TraceCorQTerm.compRight term formalSum) :=
  TraceCorQTerm.smul_compRight
    coefficient
    term
    formalSum

/-- The trace-correspondence root exposes scaling the right formal sum in term-right composition. -/
theorem TraceCorQ.term_compRight_smul
    (coefficient : Rat)
    (term : TraceCorQTerm)
    (formalSum : TraceCorQFormalSum) :
    TraceCorQTerm.compRight
      term
      (TraceCorQFormalSum.smul coefficient formalSum) =
      TraceCorQFormalSum.smul
        coefficient
        (TraceCorQTerm.compRight term formalSum) :=
  TraceCorQTerm.compRight_smul
    coefficient
    term
    formalSum

end AnalyticMotives
end LFunctions
end Boundary

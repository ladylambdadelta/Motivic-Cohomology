import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Facade.Generators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.FormalSums.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.FormalSums.Constructors.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.FormalSums.Terms.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.FormalSums.Additive.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.FormalSums.Scalars.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.FormalSums.Composition.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.FormalSums.Composition.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.FormalSums.Composition.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.FormalSums.Composition.TermRight.Owner

/-!
# Trace-correspondence formal-sum facade

This file exposes public `TraceCorQ` wrappers for formal-sum and term payload
facts used by the root trace-correspondence surface.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes formal-sum imported-rectangle counts as lengths. -/
theorem TraceCorQ.formalSum_importedRectangleCount_eq_length
    (formalSum : TraceCorQFormalSum) :
    formalSum.importedRectangleCount =
      formalSum.importedRectangles.length :=
  TraceCorQFormalSum.importedRectangleCount_eq_length_importedRectangles
    formalSum

/-- The trace-correspondence root exposes formal-sum addition certificate ledgers. -/
theorem TraceCorQ.formalSum_add_certificateLedger
    (left right : TraceCorQFormalSum) :
    (TraceCorQFormalSum.add left right).certificateLedger =
      ResidueChannelCertificateLedger.append
        left.certificateLedger
        right.certificateLedger :=
  TraceCorQFormalSum.add_certificateLedger
    left
    right

/-- The trace-correspondence root exposes formal-sum addition imported payload. -/
theorem TraceCorQ.formalSum_add_importedRectangleCount
    (left right : TraceCorQFormalSum) :
    (TraceCorQFormalSum.add left right).importedRectangleCount =
      left.importedRectangleCount +
        right.importedRectangleCount :=
  TraceCorQFormalSum.add_importedRectangleCount
    left
    right

/-- The trace-correspondence root exposes formal-sum addition imported rectangles. -/
theorem TraceCorQ.formalSum_add_importedRectangles
    (left right : TraceCorQFormalSum) :
    (TraceCorQFormalSum.add left right).importedRectangles =
      left.importedRectangles ++
        right.importedRectangles :=
  TraceCorQFormalSum.add_importedRectangles
    left
    right

/-- The trace-correspondence root exposes formal-sum addition bookkeeping payload. -/
theorem TraceCorQ.formalSum_add_traceBookkeepingCount
    (left right : TraceCorQFormalSum) :
    (TraceCorQFormalSum.add left right).traceBookkeepingCount =
      left.traceBookkeepingCount +
        right.traceBookkeepingCount :=
  TraceCorQFormalSum.add_traceBookkeepingCount
    left
    right

/-- The trace-correspondence root exposes formal-sum addition rewrite-step payload. -/
theorem TraceCorQ.formalSum_add_rewriteStepCount
    (left right : TraceCorQFormalSum) :
    (TraceCorQFormalSum.add left right).rewriteStepCount =
      left.rewriteStepCount +
        right.rewriteStepCount :=
  TraceCorQFormalSum.add_rewriteStepCount
    left
    right

/-- The trace-correspondence root exposes scalar preservation of formal-sum ledgers. -/
theorem TraceCorQ.formalSum_smul_certificateLedger
    (coefficient : Rat)
    (formalSum : TraceCorQFormalSum) :
    (TraceCorQFormalSum.smul coefficient formalSum).certificateLedger =
      formalSum.certificateLedger :=
  TraceCorQFormalSum.smul_certificateLedger
    coefficient
    formalSum

/-- The trace-correspondence root exposes scalar preservation of imported payload. -/
theorem TraceCorQ.formalSum_smul_importedRectangleCount
    (coefficient : Rat)
    (formalSum : TraceCorQFormalSum) :
    (TraceCorQFormalSum.smul coefficient formalSum).importedRectangleCount =
      formalSum.importedRectangleCount :=
  TraceCorQFormalSum.smul_importedRectangleCount
    coefficient
    formalSum

/-- The trace-correspondence root exposes scalar preservation of imported rectangles. -/
theorem TraceCorQ.formalSum_smul_importedRectangles
    (coefficient : Rat)
    (formalSum : TraceCorQFormalSum) :
    (TraceCorQFormalSum.smul coefficient formalSum).importedRectangles =
      formalSum.importedRectangles :=
  TraceCorQFormalSum.smul_importedRectangles
    coefficient
    formalSum

/-- The trace-correspondence root exposes scalar preservation of bookkeeping payload. -/
theorem TraceCorQ.formalSum_smul_traceBookkeepingCount
    (coefficient : Rat)
    (formalSum : TraceCorQFormalSum) :
    (TraceCorQFormalSum.smul coefficient formalSum).traceBookkeepingCount =
      formalSum.traceBookkeepingCount :=
  TraceCorQFormalSum.smul_traceBookkeepingCount
    coefficient
    formalSum

/-- The trace-correspondence root exposes scalar preservation of rewrite-step payload. -/
theorem TraceCorQ.formalSum_smul_rewriteStepCount
    (coefficient : Rat)
    (formalSum : TraceCorQFormalSum) :
    (TraceCorQFormalSum.smul coefficient formalSum).rewriteStepCount =
      formalSum.rewriteStepCount :=
  TraceCorQFormalSum.smul_rewriteStepCount
    coefficient
    formalSum

/-- The trace-correspondence root exposes right-zero composition imported payload. -/
theorem TraceCorQ.formalSum_comp_zero_importedRectangleCount
    (formalSum : TraceCorQFormalSum) :
    (TraceCorQFormalSum.comp
      formalSum
      TraceCorQFormalSum.zero).importedRectangleCount =
      0 :=
  TraceCorQFormalSum.comp_zero_importedRectangleCount
    formalSum

/-- The trace-correspondence root exposes right-zero composition imported rectangles. -/
theorem TraceCorQ.formalSum_comp_zero_importedRectangles
    (formalSum : TraceCorQFormalSum) :
    (TraceCorQFormalSum.comp
      formalSum
      TraceCorQFormalSum.zero).importedRectangles =
      [] :=
  TraceCorQFormalSum.comp_zero_importedRectangles
    formalSum

/-- The trace-correspondence root exposes right-zero composition rewrite-step payload. -/
theorem TraceCorQ.formalSum_comp_zero_rewriteStepCount
    (formalSum : TraceCorQFormalSum) :
    (TraceCorQFormalSum.comp
      formalSum
      TraceCorQFormalSum.zero).rewriteStepCount =
      0 :=
  TraceCorQFormalSum.comp_zero_rewriteStepCount
    formalSum

/-- The trace-correspondence root exposes cons-left composition imported payload. -/
theorem TraceCorQ.formalSum_comp_cons_left_recursive_importedRectangleCount
    (leftTerm : TraceCorQTerm)
    (leftTail right : TraceCorQFormalSum) :
    (TraceCorQFormalSum.comp
      (leftTerm :: leftTail)
      right).importedRectangleCount =
      (TraceCorQTerm.compRight leftTerm right).importedRectangleCount +
        (TraceCorQFormalSum.comp leftTail right).importedRectangleCount :=
  TraceCorQFormalSum.comp_cons_left_recursive_importedRectangleCount
    leftTerm
    leftTail
    right

/-- The trace-correspondence root exposes cons-left composition imported rectangles. -/
theorem TraceCorQ.formalSum_comp_cons_left_recursive_importedRectangles
    (leftTerm : TraceCorQTerm)
    (leftTail right : TraceCorQFormalSum) :
    (TraceCorQFormalSum.comp
      (leftTerm :: leftTail)
      right).importedRectangles =
      (TraceCorQTerm.compRight leftTerm right).importedRectangles ++
        (TraceCorQFormalSum.comp leftTail right).importedRectangles :=
  TraceCorQFormalSum.comp_cons_left_recursive_importedRectangles
    leftTerm
    leftTail
    right

/-- The trace-correspondence root exposes cons-left composition rewrite-step payload. -/
theorem TraceCorQ.formalSum_comp_cons_left_recursive_rewriteStepCount
    (leftTerm : TraceCorQTerm)
    (leftTail right : TraceCorQFormalSum) :
    (TraceCorQFormalSum.comp
      (leftTerm :: leftTail)
      right).rewriteStepCount =
      (TraceCorQTerm.compRight leftTerm right).rewriteStepCount +
        (TraceCorQFormalSum.comp leftTail right).rewriteStepCount :=
  TraceCorQFormalSum.comp_cons_left_recursive_rewriteStepCount
    leftTerm
    leftTail
    right

/-- The trace-correspondence root exposes left-additive composition imported payload. -/
theorem TraceCorQ.formalSum_add_comp_importedRectangleCount
    (left right tail : TraceCorQFormalSum) :
    (TraceCorQFormalSum.comp
      (TraceCorQFormalSum.add left right)
      tail).importedRectangleCount =
      (TraceCorQFormalSum.comp left tail).importedRectangleCount +
        (TraceCorQFormalSum.comp right tail).importedRectangleCount :=
  TraceCorQFormalSum.add_comp_importedRectangleCount
    left
    right
    tail

/-- The trace-correspondence root exposes left-additive composition imported rectangles. -/
theorem TraceCorQ.formalSum_add_comp_importedRectangles
    (left right tail : TraceCorQFormalSum) :
    (TraceCorQFormalSum.comp
      (TraceCorQFormalSum.add left right)
      tail).importedRectangles =
      (TraceCorQFormalSum.comp left tail).importedRectangles ++
        (TraceCorQFormalSum.comp right tail).importedRectangles :=
  TraceCorQFormalSum.add_comp_importedRectangles
    left
    right
    tail

/-- The trace-correspondence root exposes left-additive composition rewrite-step payload. -/
theorem TraceCorQ.formalSum_add_comp_rewriteStepCount
    (left right tail : TraceCorQFormalSum) :
    (TraceCorQFormalSum.comp
      (TraceCorQFormalSum.add left right)
      tail).rewriteStepCount =
      (TraceCorQFormalSum.comp left tail).rewriteStepCount +
        (TraceCorQFormalSum.comp right tail).rewriteStepCount :=
  TraceCorQFormalSum.add_comp_rewriteStepCount
    left
    right
    tail

/-- The trace-correspondence root exposes left-scalar composition imported payload. -/
theorem TraceCorQ.formalSum_smul_comp_importedRectangleCount
    (coefficient : Rat)
    (left right : TraceCorQFormalSum) :
    (TraceCorQFormalSum.comp
      (TraceCorQFormalSum.smul coefficient left)
      right).importedRectangleCount =
      (TraceCorQFormalSum.comp left right).importedRectangleCount :=
  TraceCorQFormalSum.smul_comp_importedRectangleCount
    coefficient
    left
    right

/-- The trace-correspondence root exposes left-scalar composition imported rectangles. -/
theorem TraceCorQ.formalSum_smul_comp_importedRectangles
    (coefficient : Rat)
    (left right : TraceCorQFormalSum) :
    (TraceCorQFormalSum.comp
      (TraceCorQFormalSum.smul coefficient left)
      right).importedRectangles =
      (TraceCorQFormalSum.comp left right).importedRectangles :=
  TraceCorQFormalSum.smul_comp_importedRectangles
    coefficient
    left
    right

/-- The trace-correspondence root exposes left-scalar composition rewrite-step payload. -/
theorem TraceCorQ.formalSum_smul_comp_rewriteStepCount
    (coefficient : Rat)
    (left right : TraceCorQFormalSum) :
    (TraceCorQFormalSum.comp
      (TraceCorQFormalSum.smul coefficient left)
      right).rewriteStepCount =
      (TraceCorQFormalSum.comp left right).rewriteStepCount :=
  TraceCorQFormalSum.smul_comp_rewriteStepCount
    coefficient
    left
    right

/-- The trace-correspondence root exposes right-scalar composition imported payload. -/
theorem TraceCorQ.formalSum_comp_smul_importedRectangleCount
    (coefficient : Rat)
    (left right : TraceCorQFormalSum) :
    (TraceCorQFormalSum.comp
      left
      (TraceCorQFormalSum.smul coefficient right)).importedRectangleCount =
      (TraceCorQFormalSum.comp left right).importedRectangleCount :=
  TraceCorQFormalSum.comp_smul_importedRectangleCount
    coefficient
    left
    right

/-- The trace-correspondence root exposes right-scalar composition imported rectangles. -/
theorem TraceCorQ.formalSum_comp_smul_importedRectangles
    (coefficient : Rat)
    (left right : TraceCorQFormalSum) :
    (TraceCorQFormalSum.comp
      left
      (TraceCorQFormalSum.smul coefficient right)).importedRectangles =
      (TraceCorQFormalSum.comp left right).importedRectangles :=
  TraceCorQFormalSum.comp_smul_importedRectangles
    coefficient
    left
    right

/-- The trace-correspondence root exposes right-scalar composition rewrite-step payload. -/
theorem TraceCorQ.formalSum_comp_smul_rewriteStepCount
    (coefficient : Rat)
    (left right : TraceCorQFormalSum) :
    (TraceCorQFormalSum.comp
      left
      (TraceCorQFormalSum.smul coefficient right)).rewriteStepCount =
      (TraceCorQFormalSum.comp left right).rewriteStepCount :=
  TraceCorQFormalSum.comp_smul_rewriteStepCount
    coefficient
    left
    right

/-- The trace-correspondence root exposes composed-term certificate ledgers. -/
theorem TraceCorQ.term_comp_certificateLedger
    (leftTerm rightTerm : TraceCorQTerm) :
    (TraceCorQTerm.comp leftTerm rightTerm).certificateLedger =
      (TraceCorQGenerator.comp leftTerm.2 rightTerm.2).certificateLedger :=
  TraceCorQTerm.comp_certificateLedger
    leftTerm
    rightTerm

/-- The trace-correspondence root exposes composed-term imported payload. -/
theorem TraceCorQ.term_comp_importedRectangleCount
    (leftTerm rightTerm : TraceCorQTerm) :
    (TraceCorQTerm.comp leftTerm rightTerm).importedRectangleCount =
      (TraceCorQGenerator.comp leftTerm.2 rightTerm.2).importedRectangleCount :=
  TraceCorQTerm.comp_importedRectangleCount
    leftTerm
    rightTerm

/-- The trace-correspondence root exposes composed-term imported rectangles. -/
theorem TraceCorQ.term_comp_importedRectangles
    (leftTerm rightTerm : TraceCorQTerm) :
    (TraceCorQTerm.comp leftTerm rightTerm).importedRectangles =
      (TraceCorQGenerator.comp leftTerm.2 rightTerm.2).importedRectangles :=
  TraceCorQTerm.comp_importedRectangles
    leftTerm
    rightTerm

/-- The trace-correspondence root exposes composed-term rewrite-step payload. -/
theorem TraceCorQ.term_comp_rewriteStepCount
    (leftTerm rightTerm : TraceCorQTerm) :
    (TraceCorQTerm.comp leftTerm rightTerm).rewriteStepCount =
      (TraceCorQGenerator.comp leftTerm.2 rightTerm.2).rewriteStepCount :=
  TraceCorQTerm.comp_rewriteStepCount
    leftTerm
    rightTerm

/-- The trace-correspondence root exposes term-right zero certificate ledgers. -/
theorem TraceCorQ.term_compRight_zero_certificateLedger
    (term : TraceCorQTerm) :
    (TraceCorQTerm.compRight term TraceCorQFormalSum.zero).certificateLedger =
      ResidueChannelCertificateLedger.empty :=
  TraceCorQTerm.compRight_zero_certificateLedger
    term

/-- The trace-correspondence root exposes term-right zero imported payload. -/
theorem TraceCorQ.term_compRight_zero_importedRectangleCount
    (term : TraceCorQTerm) :
    (TraceCorQTerm.compRight term TraceCorQFormalSum.zero).importedRectangleCount =
      0 :=
  TraceCorQTerm.compRight_zero_importedRectangleCount
    term

/-- The trace-correspondence root exposes term-right zero imported rectangles. -/
theorem TraceCorQ.term_compRight_zero_importedRectangles
    (term : TraceCorQTerm) :
    (TraceCorQTerm.compRight term TraceCorQFormalSum.zero).importedRectangles =
      [] :=
  TraceCorQTerm.compRight_zero_importedRectangles
    term

/-- The trace-correspondence root exposes term-right zero rewrite-step payload. -/
theorem TraceCorQ.term_compRight_zero_rewriteStepCount
    (term : TraceCorQTerm) :
    (TraceCorQTerm.compRight term TraceCorQFormalSum.zero).rewriteStepCount =
      0 :=
  TraceCorQTerm.compRight_zero_rewriteStepCount
    term

end AnalyticMotives
end LFunctions
end Boundary

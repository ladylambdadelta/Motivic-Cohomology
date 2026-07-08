import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.FormalSums.Composition.Basic.Scalar.Owner

/-!
# Term-level formal-sum composition

This file owns composition of one weighted trace-correspondence term with
another term, and right composition of one term over a formal sum.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Compose two weighted trace-correspondence terms. -/
def TraceCorQTerm.comp
    (leftTerm rightTerm : TraceCorQTerm) :
    TraceCorQTerm :=
  (leftTerm.1 * rightTerm.1,
    TraceCorQGenerator.comp leftTerm.2 rightTerm.2)

/-- The certificate ledger of a composed term is the ledger of its composed generator. -/
theorem TraceCorQTerm.comp_certificateLedger
    (leftTerm rightTerm : TraceCorQTerm) :
    (TraceCorQTerm.comp leftTerm rightTerm).certificateLedger =
      (TraceCorQGenerator.comp leftTerm.2 rightTerm.2).certificateLedger :=
  rfl

/-- The rewrite-step payload of a composed term is the payload of its composed generator. -/
theorem TraceCorQTerm.comp_rewriteStepCount
    (leftTerm rightTerm : TraceCorQTerm) :
    (TraceCorQTerm.comp leftTerm rightTerm).rewriteStepCount =
      (TraceCorQGenerator.comp leftTerm.2 rightTerm.2).rewriteStepCount :=
  rfl

/-- Compose one formal term on the right with every term in a formal sum. -/
def TraceCorQTerm.compRight
    (leftTerm : TraceCorQTerm)
    (rightFormalSum : TraceCorQFormalSum) :
    TraceCorQFormalSum :=
  rightFormalSum.map
    (fun rightTerm => TraceCorQTerm.comp leftTerm rightTerm)

/-- Composing one term on the right of the empty formal sum carries no certificates. -/
theorem TraceCorQTerm.compRight_zero_certificateLedger
    (term : TraceCorQTerm) :
    (TraceCorQTerm.compRight term TraceCorQFormalSum.zero).certificateLedger =
      ResidueChannelCertificateLedger.empty :=
  rfl

/-- Composing one term on the right of the empty formal sum carries no rewrite-step payload. -/
theorem TraceCorQTerm.compRight_zero_rewriteStepCount
    (term : TraceCorQTerm) :
    (TraceCorQTerm.compRight term TraceCorQFormalSum.zero).rewriteStepCount =
      0 :=
  rfl

/-- The certificate ledger of one-term right composition is the composed term ledger. -/
theorem TraceCorQTerm.compRight_singleton_certificateLedger
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
  rfl

/-- The rewrite-step payload of one-term right composition is the composed term payload. -/
theorem TraceCorQTerm.compRight_singleton_rewriteStepCount
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
  ResidueChannelCertificateLedger.append_rewriteStepCount
    (TraceCorQTerm.comp
      leftTerm
      (rightCoefficient, rightGenerator)).certificateLedger
    ResidueChannelCertificateLedger.empty

/-- The certificate ledger of right composition over a cons splits into head and tail. -/
theorem TraceCorQTerm.compRight_cons_certificateLedger
    (leftTerm rightTerm : TraceCorQTerm)
    (rightTail : TraceCorQFormalSum) :
    (TraceCorQTerm.compRight
      leftTerm
      (rightTerm :: rightTail)).certificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceCorQTerm.comp leftTerm rightTerm).certificateLedger
        (TraceCorQTerm.compRight leftTerm rightTail).certificateLedger :=
  rfl

/-- The rewrite-step payload of right composition over a cons splits into head and tail. -/
theorem TraceCorQTerm.compRight_cons_rewriteStepCount
    (leftTerm rightTerm : TraceCorQTerm)
    (rightTail : TraceCorQFormalSum) :
    (TraceCorQTerm.compRight
      leftTerm
      (rightTerm :: rightTail)).rewriteStepCount =
      (TraceCorQTerm.comp leftTerm rightTerm).rewriteStepCount +
        (TraceCorQTerm.compRight leftTerm rightTail).rewriteStepCount :=
  ResidueChannelCertificateLedger.append_rewriteStepCount
    (TraceCorQTerm.comp leftTerm rightTerm).certificateLedger
    (TraceCorQTerm.compRight leftTerm rightTail).certificateLedger

/-- Composing one formal term on the right distributes over formal-sum addition. -/
theorem TraceCorQTerm.compRight_add
    (term : TraceCorQTerm)
    (left right : TraceCorQFormalSum) :
    TraceCorQTerm.compRight
      term
      (TraceCorQFormalSum.add left right) =
      TraceCorQFormalSum.add
        (TraceCorQTerm.compRight term left)
        (TraceCorQTerm.compRight term right) :=
  List.map_append
    (fun rightTerm => TraceCorQTerm.comp term rightTerm)
    left
    right

end AnalyticMotives
end LFunctions
end Boundary

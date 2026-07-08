import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.FormalSums.Composition.Basic.Owner

/-!
# Payload accounting for formal-sum composition

This file owns downstream certificate-payload lemmas for composition of raw
formal `Q`-linear trace correspondences.

The base formal-sum owner file defines composition and the first recursive
certificate splits.  This file keeps further composition payload accounting out
of that owner file so it stays below the line cap.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A composed term carries the imported payload of its composed generator. -/
theorem TraceCorQTerm.comp_importedRectangleCount
    (leftTerm rightTerm : TraceCorQTerm) :
    (TraceCorQTerm.comp leftTerm rightTerm).importedRectangleCount =
      (TraceCorQGenerator.comp leftTerm.2 rightTerm.2).importedRectangleCount :=
  rfl

/-- A composed term exposes the imported rectangles of its composed generator. -/
theorem TraceCorQTerm.comp_importedRectangles
    (leftTerm rightTerm : TraceCorQTerm) :
    (TraceCorQTerm.comp leftTerm rightTerm).importedRectangles =
      (TraceCorQGenerator.comp leftTerm.2 rightTerm.2).importedRectangles :=
  rfl

/-- Composing one term on the right of the empty formal sum carries no imported payload. -/
theorem TraceCorQTerm.compRight_zero_importedRectangleCount
    (term : TraceCorQTerm) :
    (TraceCorQTerm.compRight term TraceCorQFormalSum.zero).importedRectangleCount =
      0 :=
  rfl

/-- Composing one term on the right of the empty formal sum exposes no imported rectangles. -/
theorem TraceCorQTerm.compRight_zero_importedRectangles
    (term : TraceCorQTerm) :
    (TraceCorQTerm.compRight term TraceCorQFormalSum.zero).importedRectangles =
      [] :=
  rfl

/-- The imported payload of one-term right composition is the composed term payload. -/
theorem TraceCorQTerm.compRight_singleton_importedRectangleCount
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
  ResidueChannelCertificateLedger.append_importedRectangleCount
    (TraceCorQTerm.comp
      leftTerm
      (rightCoefficient, rightGenerator)).certificateLedger
    ResidueChannelCertificateLedger.empty

/-- One-term right composition exposes the composed term rectangles. -/
theorem TraceCorQTerm.compRight_singleton_importedRectangles
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
  ResidueChannelCertificateLedger.append_importedRectangles
    (TraceCorQTerm.comp
      leftTerm
      (rightCoefficient, rightGenerator)).certificateLedger
    ResidueChannelCertificateLedger.empty

/-- The imported payload of right composition over a cons splits into head and tail. -/
theorem TraceCorQTerm.compRight_cons_importedRectangleCount
    (leftTerm rightTerm : TraceCorQTerm)
    (rightTail : TraceCorQFormalSum) :
    (TraceCorQTerm.compRight
      leftTerm
      (rightTerm :: rightTail)).importedRectangleCount =
      (TraceCorQTerm.comp leftTerm rightTerm).importedRectangleCount +
        (TraceCorQTerm.compRight leftTerm rightTail).importedRectangleCount :=
  ResidueChannelCertificateLedger.append_importedRectangleCount
    (TraceCorQTerm.comp leftTerm rightTerm).certificateLedger
    (TraceCorQTerm.compRight leftTerm rightTail).certificateLedger

/-- The imported rectangles of right composition over a cons split into head and tail. -/
theorem TraceCorQTerm.compRight_cons_importedRectangles
    (leftTerm rightTerm : TraceCorQTerm)
    (rightTail : TraceCorQFormalSum) :
    (TraceCorQTerm.compRight
      leftTerm
      (rightTerm :: rightTail)).importedRectangles =
      (TraceCorQTerm.comp leftTerm rightTerm).importedRectangles ++
        (TraceCorQTerm.compRight leftTerm rightTail).importedRectangles :=
  ResidueChannelCertificateLedger.append_importedRectangles
    (TraceCorQTerm.comp leftTerm rightTerm).certificateLedger
    (TraceCorQTerm.compRight leftTerm rightTail).certificateLedger

/-- Composing the zero formal sum on the right carries no imported payload. -/
theorem TraceCorQFormalSum.comp_zero_importedRectangleCount
    (formalSum : TraceCorQFormalSum) :
    (TraceCorQFormalSum.comp
      formalSum
      TraceCorQFormalSum.zero).importedRectangleCount =
      0 :=
  Eq.trans
    (congrArg
      TraceCorQFormalSum.importedRectangleCount
      (TraceCorQFormalSum.comp_zero formalSum))
    TraceCorQFormalSum.zero_importedRectangleCount

/-- Composing the zero formal sum on the right exposes no imported rectangles. -/
theorem TraceCorQFormalSum.comp_zero_importedRectangles
    (formalSum : TraceCorQFormalSum) :
    (TraceCorQFormalSum.comp
      formalSum
      TraceCorQFormalSum.zero).importedRectangles =
      [] :=
  Eq.trans
    (congrArg
      TraceCorQFormalSum.importedRectangles
      (TraceCorQFormalSum.comp_zero formalSum))
    TraceCorQFormalSum.zero_importedRectangles

/-- Composing the zero formal sum on the right carries no rewrite-step payload. -/
theorem TraceCorQFormalSum.comp_zero_rewriteStepCount
    (formalSum : TraceCorQFormalSum) :
    (TraceCorQFormalSum.comp
      formalSum
      TraceCorQFormalSum.zero).rewriteStepCount =
      0 :=
  Eq.trans
    (congrArg
      TraceCorQFormalSum.rewriteStepCount
      (TraceCorQFormalSum.comp_zero formalSum))
    TraceCorQFormalSum.zero_rewriteStepCount

/-- Formal composition with a cons left side has the recursive rewrite-step split. -/
theorem TraceCorQFormalSum.comp_cons_left_recursive_rewriteStepCount
    (leftTerm : TraceCorQTerm)
    (leftTail right : TraceCorQFormalSum) :
    (TraceCorQFormalSum.comp
      (leftTerm :: leftTail)
      right).rewriteStepCount =
      (TraceCorQTerm.compRight leftTerm right).rewriteStepCount +
        (TraceCorQFormalSum.comp leftTail right).rewriteStepCount :=
  TraceCorQFormalSum.comp_cons_left_rewriteStepCount
    leftTerm
    leftTail
    right

/-- Formal composition with a cons left side has the recursive imported-payload split. -/
theorem TraceCorQFormalSum.comp_cons_left_recursive_importedRectangleCount
    (leftTerm : TraceCorQTerm)
    (leftTail right : TraceCorQFormalSum) :
    (TraceCorQFormalSum.comp
      (leftTerm :: leftTail)
      right).importedRectangleCount =
      (TraceCorQTerm.compRight leftTerm right).importedRectangleCount +
        (TraceCorQFormalSum.comp leftTail right).importedRectangleCount :=
  Eq.trans
    (congrArg
      ResidueChannelCertificateLedger.importedRectangleCount
      (TraceCorQFormalSum.comp_cons_left_certificateLedger
        leftTerm
        leftTail
        right))
    (ResidueChannelCertificateLedger.append_importedRectangleCount
      (TraceCorQTerm.compRight leftTerm right).certificateLedger
      (TraceCorQFormalSum.comp leftTail right).certificateLedger)

/-- Formal composition with a cons left side has the recursive imported-rectangle split. -/
theorem TraceCorQFormalSum.comp_cons_left_recursive_importedRectangles
    (leftTerm : TraceCorQTerm)
    (leftTail right : TraceCorQFormalSum) :
    (TraceCorQFormalSum.comp
      (leftTerm :: leftTail)
      right).importedRectangles =
      (TraceCorQTerm.compRight leftTerm right).importedRectangles ++
        (TraceCorQFormalSum.comp leftTail right).importedRectangles :=
  Eq.trans
    (congrArg
      ResidueChannelCertificateLedger.importedRectangles
      (TraceCorQFormalSum.comp_cons_left_certificateLedger
        leftTerm
        leftTail
        right))
    (ResidueChannelCertificateLedger.append_importedRectangles
      (TraceCorQTerm.compRight leftTerm right).certificateLedger
      (TraceCorQFormalSum.comp leftTail right).certificateLedger)

/-- Left distributivity of composition adds imported payload after transport by equality. -/
theorem TraceCorQFormalSum.add_comp_importedRectangleCount
    (left right tail : TraceCorQFormalSum) :
    (TraceCorQFormalSum.comp
      (TraceCorQFormalSum.add left right)
      tail).importedRectangleCount =
      (TraceCorQFormalSum.comp left tail).importedRectangleCount +
        (TraceCorQFormalSum.comp right tail).importedRectangleCount :=
  Eq.trans
    (congrArg
      TraceCorQFormalSum.importedRectangleCount
      (TraceCorQFormalSum.add_comp left right tail))
    (TraceCorQFormalSum.add_importedRectangleCount
      (TraceCorQFormalSum.comp left tail)
      (TraceCorQFormalSum.comp right tail))

/-- Left distributivity of composition appends imported rectangles after transport by equality. -/
theorem TraceCorQFormalSum.add_comp_importedRectangles
    (left right tail : TraceCorQFormalSum) :
    (TraceCorQFormalSum.comp
      (TraceCorQFormalSum.add left right)
      tail).importedRectangles =
      (TraceCorQFormalSum.comp left tail).importedRectangles ++
        (TraceCorQFormalSum.comp right tail).importedRectangles :=
  Eq.trans
    (congrArg
      TraceCorQFormalSum.importedRectangles
      (TraceCorQFormalSum.add_comp left right tail))
    (TraceCorQFormalSum.add_importedRectangles
      (TraceCorQFormalSum.comp left tail)
      (TraceCorQFormalSum.comp right tail))

/-- Left distributivity of composition adds rewrite-step payload after transport by equality. -/
theorem TraceCorQFormalSum.add_comp_rewriteStepCount
    (left right tail : TraceCorQFormalSum) :
    (TraceCorQFormalSum.comp
      (TraceCorQFormalSum.add left right)
      tail).rewriteStepCount =
      (TraceCorQFormalSum.comp left tail).rewriteStepCount +
        (TraceCorQFormalSum.comp right tail).rewriteStepCount :=
  Eq.trans
    (congrArg
      TraceCorQFormalSum.rewriteStepCount
      (TraceCorQFormalSum.add_comp left right tail))
    (TraceCorQFormalSum.add_rewriteStepCount
      (TraceCorQFormalSum.comp left tail)
      (TraceCorQFormalSum.comp right tail))

/-- Scaling the left formal sum preserves composition rewrite-step payload. -/
theorem TraceCorQFormalSum.smul_comp_rewriteStepCount
    (coefficient : Rat)
    (left right : TraceCorQFormalSum) :
    (TraceCorQFormalSum.comp
      (TraceCorQFormalSum.smul coefficient left)
      right).rewriteStepCount =
      (TraceCorQFormalSum.comp left right).rewriteStepCount :=
  Eq.trans
    (congrArg
      TraceCorQFormalSum.rewriteStepCount
      (TraceCorQFormalSum.smul_comp coefficient left right))
    (TraceCorQFormalSum.smul_rewriteStepCount
      coefficient
      (TraceCorQFormalSum.comp left right))

/-- Scaling the left formal sum preserves composition imported payload. -/
theorem TraceCorQFormalSum.smul_comp_importedRectangleCount
    (coefficient : Rat)
    (left right : TraceCorQFormalSum) :
    (TraceCorQFormalSum.comp
      (TraceCorQFormalSum.smul coefficient left)
      right).importedRectangleCount =
      (TraceCorQFormalSum.comp left right).importedRectangleCount :=
  Eq.trans
    (congrArg
      TraceCorQFormalSum.importedRectangleCount
      (TraceCorQFormalSum.smul_comp coefficient left right))
    (TraceCorQFormalSum.smul_importedRectangleCount
      coefficient
      (TraceCorQFormalSum.comp left right))

/-- Scaling the left formal sum preserves composition imported rectangles. -/
theorem TraceCorQFormalSum.smul_comp_importedRectangles
    (coefficient : Rat)
    (left right : TraceCorQFormalSum) :
    (TraceCorQFormalSum.comp
      (TraceCorQFormalSum.smul coefficient left)
      right).importedRectangles =
      (TraceCorQFormalSum.comp left right).importedRectangles :=
  Eq.trans
    (congrArg
      TraceCorQFormalSum.importedRectangles
      (TraceCorQFormalSum.smul_comp coefficient left right))
    (TraceCorQFormalSum.smul_importedRectangles
      coefficient
      (TraceCorQFormalSum.comp left right))

/-- Scaling the right formal sum preserves composition rewrite-step payload. -/
theorem TraceCorQFormalSum.comp_smul_rewriteStepCount
    (coefficient : Rat)
    (left right : TraceCorQFormalSum) :
    (TraceCorQFormalSum.comp
      left
      (TraceCorQFormalSum.smul coefficient right)).rewriteStepCount =
      (TraceCorQFormalSum.comp left right).rewriteStepCount :=
  Eq.trans
    (congrArg
      TraceCorQFormalSum.rewriteStepCount
      (TraceCorQFormalSum.comp_smul coefficient left right))
    (TraceCorQFormalSum.smul_rewriteStepCount
      coefficient
      (TraceCorQFormalSum.comp left right))

/-- Scaling the right formal sum preserves composition imported payload. -/
theorem TraceCorQFormalSum.comp_smul_importedRectangleCount
    (coefficient : Rat)
    (left right : TraceCorQFormalSum) :
    (TraceCorQFormalSum.comp
      left
      (TraceCorQFormalSum.smul coefficient right)).importedRectangleCount =
      (TraceCorQFormalSum.comp left right).importedRectangleCount :=
  Eq.trans
    (congrArg
      TraceCorQFormalSum.importedRectangleCount
      (TraceCorQFormalSum.comp_smul coefficient left right))
    (TraceCorQFormalSum.smul_importedRectangleCount
      coefficient
      (TraceCorQFormalSum.comp left right))

/-- Scaling the right formal sum preserves composition imported rectangles. -/
theorem TraceCorQFormalSum.comp_smul_importedRectangles
    (coefficient : Rat)
    (left right : TraceCorQFormalSum) :
    (TraceCorQFormalSum.comp
      left
      (TraceCorQFormalSum.smul coefficient right)).importedRectangles =
      (TraceCorQFormalSum.comp left right).importedRectangles :=
  Eq.trans
    (congrArg
      TraceCorQFormalSum.importedRectangles
      (TraceCorQFormalSum.comp_smul coefficient left right))
    (TraceCorQFormalSum.smul_importedRectangles
      coefficient
      (TraceCorQFormalSum.comp left right))

end AnalyticMotives
end LFunctions
end Boundary

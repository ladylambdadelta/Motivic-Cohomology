import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Composition.Terms.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.FormalSums.Owner

/-!
# Composition of typed hom formal sums

This file owns finite bilinear composition of typed formal sums.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Compose one typed term on the right with every term in a typed formal sum. -/
def TraceCorQHomTerm.compRight
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomTerm source middle)
    (right : TraceCorQHomFormalSum middle target) :
    TraceCorQHomFormalSum source target :=
  right.map (fun rightTerm => TraceCorQHomTerm.comp left rightTerm)

/-- Compose typed formal sums by finite bilinear expansion. -/
def TraceCorQHomFormalSum.comp
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomFormalSum source middle)
    (right : TraceCorQHomFormalSum middle target) :
    TraceCorQHomFormalSum source target :=
  left.bind (fun leftTerm => TraceCorQHomTerm.compRight leftTerm right)

/-- Raw forgetful map sends typed term-right composition to raw term-right composition. -/
theorem TraceCorQHomTerm.compRight_raw
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomTerm source middle)
    (right : TraceCorQHomFormalSum middle target) :
    (TraceCorQHomTerm.compRight left right).raw =
      TraceCorQTerm.compRight left.raw right.raw :=
  match right with
  | [] => rfl
  | rightTerm :: rightTail =>
      congrArg
        (fun tailRaw =>
          (left.raw.1 * rightTerm.raw.1,
            TraceCorQGenerator.comp left.raw.2 rightTerm.raw.2) ::
            tailRaw)
        (TraceCorQHomTerm.compRight_raw left rightTail)

/-- Typed term-right composition carries the raw term-right composition certificate ledger. -/
theorem TraceCorQHomTerm.compRight_certificateLedger
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomTerm source middle)
    (right : TraceCorQHomFormalSum middle target) :
    (TraceCorQHomTerm.compRight left right).certificateLedger =
      (TraceCorQTerm.compRight left.raw right.raw).certificateLedger :=
  congrArg
    TraceCorQFormalSum.certificateLedger
    (TraceCorQHomTerm.compRight_raw left right)

/-- Typed term-right composition carries the raw term-right composition imported payload. -/
theorem TraceCorQHomTerm.compRight_importedRectangleCount
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomTerm source middle)
    (right : TraceCorQHomFormalSum middle target) :
    (TraceCorQHomTerm.compRight left right).importedRectangleCount =
      (TraceCorQTerm.compRight left.raw right.raw).importedRectangleCount :=
  congrArg
    ResidueChannelCertificateLedger.importedRectangleCount
    (TraceCorQHomTerm.compRight_certificateLedger left right)

/-- Typed term-right composition exposes the raw term-right composition imported rectangles. -/
theorem TraceCorQHomTerm.compRight_importedRectangles
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomTerm source middle)
    (right : TraceCorQHomFormalSum middle target) :
    (TraceCorQHomTerm.compRight left right).importedRectangles =
      (TraceCorQTerm.compRight left.raw right.raw).importedRectangles :=
  congrArg
    ResidueChannelCertificateLedger.importedRectangles
    (TraceCorQHomTerm.compRight_certificateLedger left right)

/-- Typed term-right composition carries the raw term-right composition bookkeeping payload. -/
theorem TraceCorQHomTerm.compRight_traceBookkeepingCount
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomTerm source middle)
    (right : TraceCorQHomFormalSum middle target) :
    (TraceCorQHomTerm.compRight left right).traceBookkeepingCount =
      (TraceCorQTerm.compRight left.raw right.raw).traceBookkeepingCount :=
  congrArg
    ResidueChannelCertificateLedger.traceBookkeepingCount
    (TraceCorQHomTerm.compRight_certificateLedger left right)

/-- Typed term-right composition carries the raw term-right composition rewrite-step payload. -/
theorem TraceCorQHomTerm.compRight_rewriteStepCount
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomTerm source middle)
    (right : TraceCorQHomFormalSum middle target) :
    (TraceCorQHomTerm.compRight left right).rewriteStepCount =
      (TraceCorQTerm.compRight left.raw right.raw).rewriteStepCount :=
  congrArg
    ResidueChannelCertificateLedger.rewriteStepCount
    (TraceCorQHomTerm.compRight_certificateLedger left right)

/-- Raw forgetful map sends typed formal-sum composition to raw composition. -/
theorem TraceCorQHomFormalSum.comp_raw
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomFormalSum source middle)
    (right : TraceCorQHomFormalSum middle target) :
    (TraceCorQHomFormalSum.comp left right).raw =
      TraceCorQFormalSum.comp left.raw right.raw :=
  match left with
  | [] => rfl
  | leftTerm :: leftTail =>
      Eq.trans
        (TraceCorQHomFormalSum.add_raw
          (TraceCorQHomTerm.compRight leftTerm right)
          (TraceCorQHomFormalSum.comp leftTail right))
        (Eq.trans
          (congrArg
            (fun tailRaw =>
              TraceCorQFormalSum.add
                (TraceCorQHomTerm.compRight leftTerm right).raw
                tailRaw)
            (TraceCorQHomFormalSum.comp_raw leftTail right))
          (congrArg
            (fun headRaw =>
              TraceCorQFormalSum.add
                headRaw
                (TraceCorQFormalSum.comp
                  (TraceCorQHomFormalSum.raw leftTail)
                  right.raw))
            (TraceCorQHomTerm.compRight_raw leftTerm right)))

/-- Typed formal-sum composition carries the raw formal composition certificate ledger. -/
theorem TraceCorQHomFormalSum.comp_certificateLedger
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomFormalSum source middle)
    (right : TraceCorQHomFormalSum middle target) :
    (TraceCorQHomFormalSum.comp left right).certificateLedger =
      (TraceCorQFormalSum.comp left.raw right.raw).certificateLedger :=
  congrArg
    TraceCorQFormalSum.certificateLedger
    (TraceCorQHomFormalSum.comp_raw left right)

/-- Typed formal-sum composition carries the raw formal composition imported payload. -/
theorem TraceCorQHomFormalSum.comp_importedRectangleCount
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomFormalSum source middle)
    (right : TraceCorQHomFormalSum middle target) :
    (TraceCorQHomFormalSum.comp left right).importedRectangleCount =
      (TraceCorQFormalSum.comp left.raw right.raw).importedRectangleCount :=
  congrArg
    ResidueChannelCertificateLedger.importedRectangleCount
    (TraceCorQHomFormalSum.comp_certificateLedger left right)

/-- Typed formal-sum composition exposes the raw formal composition imported rectangles. -/
theorem TraceCorQHomFormalSum.comp_importedRectangles
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomFormalSum source middle)
    (right : TraceCorQHomFormalSum middle target) :
    (TraceCorQHomFormalSum.comp left right).importedRectangles =
      (TraceCorQFormalSum.comp left.raw right.raw).importedRectangles :=
  congrArg
    ResidueChannelCertificateLedger.importedRectangles
    (TraceCorQHomFormalSum.comp_certificateLedger left right)

/-- Typed formal-sum composition carries the raw formal composition bookkeeping payload. -/
theorem TraceCorQHomFormalSum.comp_traceBookkeepingCount
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomFormalSum source middle)
    (right : TraceCorQHomFormalSum middle target) :
    (TraceCorQHomFormalSum.comp left right).traceBookkeepingCount =
      (TraceCorQFormalSum.comp left.raw right.raw).traceBookkeepingCount :=
  congrArg
    ResidueChannelCertificateLedger.traceBookkeepingCount
    (TraceCorQHomFormalSum.comp_certificateLedger left right)

/-- Typed formal-sum composition carries the raw formal composition rewrite-step payload. -/
theorem TraceCorQHomFormalSum.comp_rewriteStepCount
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomFormalSum source middle)
    (right : TraceCorQHomFormalSum middle target) :
    (TraceCorQHomFormalSum.comp left right).rewriteStepCount =
      (TraceCorQFormalSum.comp left.raw right.raw).rewriteStepCount :=
  congrArg
    ResidueChannelCertificateLedger.rewriteStepCount
    (TraceCorQHomFormalSum.comp_certificateLedger left right)

end AnalyticMotives
end LFunctions
end Boundary

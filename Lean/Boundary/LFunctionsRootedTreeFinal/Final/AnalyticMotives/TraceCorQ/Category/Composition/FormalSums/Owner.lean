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
                (TraceCorQFormalSum.comp leftTail.raw right.raw))
            (TraceCorQHomTerm.compRight_raw leftTerm right)))

end AnalyticMotives
end LFunctions
end Boundary

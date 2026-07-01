import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Terms.Owner

/-!
# Typed trace-correspondence formal sums

This file owns finite Q-linear sums of trace-correspondence terms with a
common source and target.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A finite formal sum of typed hom terms with common source and target. -/
abbrev TraceCorQHomFormalSum
    (source target : TraceCorQObject) :=
  List (TraceCorQHomTerm source target)

/-- Forget endpoint proofs and recover the raw formal sum. -/
def TraceCorQHomFormalSum.raw
    {source target : TraceCorQObject}
    (formalSum : TraceCorQHomFormalSum source target) :
    TraceCorQFormalSum :=
  formalSum.map TraceCorQHomTerm.raw

/-- The empty typed formal sum. -/
def TraceCorQHomFormalSum.zero
    (source target : TraceCorQObject) :
    TraceCorQHomFormalSum source target :=
  []

/-- The singleton typed formal sum. -/
def TraceCorQHomFormalSum.singleton
    (source target : TraceCorQObject)
    (coefficient : Rat)
    (generator : TraceCorQGenerator)
    (source_eq : generator.source = source)
    (target_eq : generator.target = target) :
    TraceCorQHomFormalSum source target :=
  [TraceCorQHomTerm.ofGenerator
    source
    target
    coefficient
    generator
    source_eq
    target_eq]

/-- Add typed formal sums by list concatenation. -/
def TraceCorQHomFormalSum.add
    {source target : TraceCorQObject}
    (left right : TraceCorQHomFormalSum source target) :
    TraceCorQHomFormalSum source target :=
  left ++ right

/-- The raw formal sum of a typed zero is the raw zero. -/
theorem TraceCorQHomFormalSum.zero_raw
    (source target : TraceCorQObject) :
    (TraceCorQHomFormalSum.zero source target).raw =
      TraceCorQFormalSum.zero :=
  rfl

/-- The raw formal sum of a typed singleton is the raw singleton. -/
theorem TraceCorQHomFormalSum.singleton_raw
    (source target : TraceCorQObject)
    (coefficient : Rat)
    (generator : TraceCorQGenerator)
    (source_eq : generator.source = source)
    (target_eq : generator.target = target) :
    (TraceCorQHomFormalSum.singleton
      source
      target
      coefficient
      generator
      source_eq
      target_eq).raw =
      TraceCorQFormalSum.singleton coefficient generator :=
  rfl

/-- Raw forgetful map sends typed addition to raw formal-sum addition. -/
theorem TraceCorQHomFormalSum.add_raw
    {source target : TraceCorQObject}
    (left right : TraceCorQHomFormalSum source target) :
    (TraceCorQHomFormalSum.add left right).raw =
      TraceCorQFormalSum.add left.raw right.raw :=
  List.map_append TraceCorQHomTerm.raw left right

end AnalyticMotives
end LFunctions
end Boundary

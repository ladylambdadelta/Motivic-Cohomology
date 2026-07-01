import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Instances.Owner

/-!
# Operation-instance bridge laws for quotient trace correspondences

This file records that standard operation notation unfolds to the concrete
quotient operations owned earlier in the tree.

Standard-notation wrappers for proved algebraic laws live in
`Quotient/Operations/Instances/Laws/Algebra`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Standard zero notation unfolds to the concrete quotient zero. -/
theorem TraceCorQQuotient.inst_zero_eq :
    (0 : TraceCorQQuotient) =
      TraceCorQQuotient.zero :=
  rfl

/-- Standard addition notation unfolds to concrete quotient addition. -/
theorem TraceCorQQuotient.inst_add_eq
    (left right : TraceCorQQuotient) :
    left + right =
      TraceCorQQuotient.add left right :=
  rfl

/-- Standard negation notation unfolds to concrete quotient negation. -/
theorem TraceCorQQuotient.inst_neg_eq
    (candidateClass : TraceCorQQuotient) :
    -candidateClass =
      TraceCorQQuotient.neg candidateClass :=
  rfl

/-- Standard subtraction notation unfolds to concrete quotient subtraction. -/
theorem TraceCorQQuotient.inst_sub_eq
    (left right : TraceCorQQuotient) :
    left - right =
      TraceCorQQuotient.sub left right :=
  rfl

/-- Standard rational scalar notation unfolds to concrete quotient scalar multiplication. -/
theorem TraceCorQQuotient.inst_smul_eq
    (coefficient : Rat)
    (candidateClass : TraceCorQQuotient) :
    coefficient • candidateClass =
      TraceCorQQuotient.smul coefficient candidateClass :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

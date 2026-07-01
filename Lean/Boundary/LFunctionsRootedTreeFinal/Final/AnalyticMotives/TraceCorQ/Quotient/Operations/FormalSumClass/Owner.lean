import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Zero.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Singleton.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Add.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.Owner

/-!
# Quotient classes represented by formal sums

This file names the quotient class represented by a concrete formal
Q-linear trace-correspondence sum and proves the cons decomposition used by
finite induction arguments.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The quotient class represented by a formal sum with an explicit ledger. -/
def TraceCorQQuotient.ofFormalSumLedger
    (formalSum : TraceCorQFormalSum)
    (ledger : TraceCorQRelationLedger) :
    TraceCorQQuotient :=
  TraceCorQQuotient.ofCandidate
    (TraceCorQQuotientInput.ofFormalSumLedger formalSum ledger)

/-- The quotient class represented by a formal sum with empty ledger. -/
def TraceCorQQuotient.ofFormalSum
    (formalSum : TraceCorQFormalSum) :
    TraceCorQQuotient :=
  TraceCorQQuotient.ofFormalSumLedger
    formalSum
    TraceCorQRelationLedger.empty

/-- Folding a formal sum into a quotient class by adding singleton classes. -/
def TraceCorQQuotient.foldFormalSum :
    TraceCorQFormalSum → TraceCorQQuotient
  | [] => TraceCorQQuotient.zero
  | (coefficient, generator) :: tail =>
      TraceCorQQuotient.add
        (TraceCorQQuotient.singleton coefficient generator)
        (TraceCorQQuotient.foldFormalSum tail)

/-- The empty formal sum represents the zero quotient class. -/
theorem TraceCorQQuotient.ofFormalSum_nil :
    TraceCorQQuotient.ofFormalSum [] =
      TraceCorQQuotient.zero :=
  rfl

/-- Folding the empty formal sum gives zero. -/
theorem TraceCorQQuotient.foldFormalSum_nil :
    TraceCorQQuotient.foldFormalSum [] =
      TraceCorQQuotient.zero :=
  rfl

/-- Folding a cons formal sum adds its singleton head to the folded tail. -/
theorem TraceCorQQuotient.foldFormalSum_cons
    (coefficient : Rat)
    (generator : TraceCorQGenerator)
    (tail : TraceCorQFormalSum) :
    TraceCorQQuotient.foldFormalSum
      ((coefficient, generator) :: tail) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.singleton coefficient generator)
        (TraceCorQQuotient.foldFormalSum tail) :=
  rfl

/-- A cons formal sum is the sum of its singleton head and formal-sum tail. -/
theorem TraceCorQQuotient.ofFormalSum_cons
    (coefficient : Rat)
    (generator : TraceCorQGenerator)
    (tail : TraceCorQFormalSum) :
    TraceCorQQuotient.ofFormalSum
      ((coefficient, generator) :: tail) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.singleton coefficient generator)
        (TraceCorQQuotient.ofFormalSum tail) :=
  Eq.symm
    (Eq.trans
      (TraceCorQQuotient.add_ofCandidate
        (TraceCorQQuotient.singletonCandidate
          coefficient
          generator
          TraceCorQRelationLedger.empty)
        (TraceCorQQuotientInput.ofFormalSumLedger
          tail
          TraceCorQRelationLedger.empty))
      (TraceCorQQuotient.sound_sameFormalSum
        TraceCorQRelationLedger.empty
        rfl))

/-- Folding a formal sum gives the same quotient class as its direct representative. -/
theorem TraceCorQQuotient.foldFormalSum_eq_ofFormalSum
    (formalSum : TraceCorQFormalSum) :
    TraceCorQQuotient.foldFormalSum formalSum =
      TraceCorQQuotient.ofFormalSum formalSum :=
  match formalSum with
  | [] => rfl
  | (coefficient, generator) :: tail =>
      Eq.trans
        (congrArg
          (fun tailClass =>
            TraceCorQQuotient.add
              (TraceCorQQuotient.singleton coefficient generator)
              tailClass)
          (TraceCorQQuotient.foldFormalSum_eq_ofFormalSum tail))
        (Eq.symm
          (TraceCorQQuotient.ofFormalSum_cons
            coefficient
            generator
            tail))

/-- Composition of direct formal-sum representatives is represented by formal composition. -/
theorem TraceCorQQuotient.comp_ofFormalSum
    (left right : TraceCorQFormalSum) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.ofFormalSum left)
      (TraceCorQQuotient.ofFormalSum right) =
      TraceCorQQuotient.ofFormalSum
        (TraceCorQFormalSum.comp left right) :=
  Eq.trans
    (TraceCorQQuotient.comp_ofCandidate
      (TraceCorQQuotientInput.ofFormalSumLedger
        left
        TraceCorQRelationLedger.empty)
      (TraceCorQQuotientInput.ofFormalSumLedger
        right
        TraceCorQRelationLedger.empty))
    (TraceCorQQuotient.sound_sameFormalSum
      TraceCorQRelationLedger.empty
      rfl)

/-- A quotient candidate equals the direct class of its formal sum. -/
theorem TraceCorQQuotient.ofCandidate_eq_ofFormalSum
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQQuotient.ofCandidate candidate =
      TraceCorQQuotient.ofFormalSum candidate.formalSum :=
  TraceCorQQuotient.sound_sameFormalSum
    candidate.ledger
    rfl

end AnalyticMotives
end LFunctions
end Boundary

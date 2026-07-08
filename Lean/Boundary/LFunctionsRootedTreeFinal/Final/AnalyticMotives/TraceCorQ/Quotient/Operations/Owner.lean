import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Zero.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Zero.Support.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Singleton.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Singleton.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.FormalSumClass.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.FormalSumClass.NamedCoherence.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Add.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Add.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Add.Laws.Derived.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Smul.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Smul.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Smul.Laws.Derived.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Neg.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Neg.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Neg.Laws.Derived.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Sub.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Sub.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Sub.Laws.Derived.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.Derived.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Instances.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Instances.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Instances.Laws.Algebra.Owner

/-!
# Operations on quotient trace correspondences

This file re-exports operations that have been proved to descend from raw
quotient candidates to quotient classes.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The quotient-operations root exposes the zero class. -/
theorem TraceCorQQuotientOperations.zero_eq_ofCandidate_empty :
    TraceCorQQuotient.zero =
      TraceCorQQuotient.ofCandidate TraceCorQQuotientCandidate.empty :=
  TraceCorQQuotient.zero_eq_ofCandidate_empty

/-- The quotient-operations root exposes addition on representatives. -/
theorem TraceCorQQuotientOperations.add_ofCandidate
    (left right : TraceCorQQuotientCandidate) :
    TraceCorQQuotient.add
        (TraceCorQQuotient.ofCandidate left)
        (TraceCorQQuotient.ofCandidate right) =
      TraceCorQQuotient.ofCandidate
        (TraceCorQQuotientCandidate.add left right) :=
  TraceCorQQuotient.add_ofCandidate
    left
    right

/-- The quotient-operations root exposes scalar multiplication on representatives. -/
theorem TraceCorQQuotientOperations.smul_ofCandidate
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQQuotient.smul
        coefficient
        (TraceCorQQuotient.ofCandidate candidate) =
      TraceCorQQuotient.ofCandidate
        (TraceCorQQuotientCandidate.smul coefficient candidate) :=
  TraceCorQQuotient.smul_ofCandidate
    coefficient
    candidate

/-- The quotient-operations root exposes composition on representatives. -/
theorem TraceCorQQuotientOperations.comp_ofCandidate
    (left right : TraceCorQQuotientCandidate) :
    TraceCorQQuotient.comp
        (TraceCorQQuotient.ofCandidate left)
        (TraceCorQQuotient.ofCandidate right) =
      TraceCorQQuotient.ofCandidate
        (TraceCorQQuotientCandidate.comp left right) :=
  TraceCorQQuotient.comp_ofCandidate
    left
    right

/-- The quotient-operations root exposes additive associativity. -/
theorem TraceCorQQuotientOperations.add_assoc
    (left middle right : TraceCorQQuotient) :
    TraceCorQQuotient.add
        (TraceCorQQuotient.add left middle)
        right =
      TraceCorQQuotient.add
        left
        (TraceCorQQuotient.add middle right) :=
  TraceCorQQuotient.add_assoc
    left
    middle
    right

/-- The quotient-operations root exposes composition associativity. -/
theorem TraceCorQQuotientOperations.comp_assoc
    (left middle right : TraceCorQQuotient) :
    TraceCorQQuotient.comp
        (TraceCorQQuotient.comp left middle)
        right =
      TraceCorQQuotient.comp
        left
        (TraceCorQQuotient.comp middle right) :=
  TraceCorQQuotient.comp_assoc
    left
    middle
    right

/-- The quotient-operations root exposes formal-sum representative composition. -/
theorem TraceCorQQuotientOperations.comp_ofFormalSum
    (left right : TraceCorQFormalSum) :
    TraceCorQQuotient.comp
        (TraceCorQQuotient.ofFormalSum left)
        (TraceCorQQuotient.ofFormalSum right) =
      TraceCorQQuotient.ofFormalSum
        (TraceCorQFormalSum.comp left right) :=
  TraceCorQQuotient.comp_ofFormalSum
    left
    right

/-- The quotient-operations root exposes candidate reduction to a formal-sum class. -/
theorem TraceCorQQuotientOperations.ofCandidate_eq_ofFormalSum
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQQuotient.ofCandidate candidate =
      TraceCorQQuotient.ofFormalSum candidate.formalSum :=
  TraceCorQQuotient.ofCandidate_eq_ofFormalSum
    candidate

/-- The quotient-operations root exposes zero-coefficient singleton erasure. -/
theorem TraceCorQQuotientOperations.singleton_zero
    (generator : TraceCorQGenerator) :
    TraceCorQQuotient.singleton 0 generator =
      TraceCorQQuotient.zero :=
  TraceCorQQuotient.singleton_zero
    generator

/-- The quotient-operations root exposes same-generator coefficient combination. -/
theorem TraceCorQQuotientOperations.singleton_add_singleton_same_generator
    (leftCoefficient rightCoefficient : Rat)
    (generator : TraceCorQGenerator) :
    TraceCorQQuotient.add
      (TraceCorQQuotient.singleton leftCoefficient generator)
      (TraceCorQQuotient.singleton rightCoefficient generator) =
      TraceCorQQuotient.singleton
        (leftCoefficient + rightCoefficient)
        generator :=
  TraceCorQQuotient.singleton_add_singleton_same_generator
    leftCoefficient
    rightCoefficient
    generator

/-- The quotient-operations root exposes negation as scalar multiplication by `-1`. -/
theorem TraceCorQQuotientOperations.neg_eq_smul_neg_one
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.neg candidateClass =
      TraceCorQQuotient.smul (-1) candidateClass :=
  TraceCorQQuotient.neg_eq_smul_neg_one
    candidateClass

/-- The quotient-operations root exposes subtraction as addition of the negative. -/
theorem TraceCorQQuotientOperations.sub_eq_add_neg
    (left right : TraceCorQQuotient) :
    TraceCorQQuotient.sub left right =
      TraceCorQQuotient.add left (TraceCorQQuotient.neg right) :=
  TraceCorQQuotient.sub_eq_add_neg
    left
    right

/-- The quotient-operations root exposes scalar distribution over addition. -/
theorem TraceCorQQuotientOperations.smul_add
    (coefficient : Rat)
    (left right : TraceCorQQuotient) :
    TraceCorQQuotient.smul
      coefficient
      (TraceCorQQuotient.add left right) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.smul coefficient left)
        (TraceCorQQuotient.smul coefficient right) :=
  TraceCorQQuotient.smul_add
    coefficient
    left
    right

/-- The quotient-operations root exposes composition left-distribution over addition. -/
theorem TraceCorQQuotientOperations.add_comp
    (left right tail : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.add left right)
      tail =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp left tail)
        (TraceCorQQuotient.comp right tail) :=
  TraceCorQQuotient.add_comp
    left
    right
    tail

/-- The quotient-operations root exposes composition right-distribution over addition. -/
theorem TraceCorQQuotientOperations.comp_add
    (left right tail : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      left
      (TraceCorQQuotient.add right tail) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp left right)
        (TraceCorQQuotient.comp left tail) :=
  TraceCorQQuotient.comp_add
    left
    right
    tail

/-- The quotient-operations root exposes Fubini support cancellation. -/
theorem TraceCorQQuotientOperations.ofFormalSumLedger_fubini_eq_zero
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotient.ofFormalSumLedger
      support
      (TraceCorQRelationLedger.fubini source target support) =
      TraceCorQQuotient.zero :=
  TraceCorQQuotient.ofFormalSumLedger_fubini_eq_zero
    source
    target
    support

/-- The quotient-operations root exposes residue-channel support cancellation. -/
theorem TraceCorQQuotientOperations.ofFormalSumLedger_residueChannel_eq_zero
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotient.ofFormalSumLedger
      support
      (TraceCorQRelationLedger.residueChannel source target support) =
      TraceCorQQuotient.zero :=
  TraceCorQQuotient.ofFormalSumLedger_residueChannel_eq_zero
    source
    target
    support

/-- The quotient-operations root exposes Stokes-residue support cancellation. -/
theorem TraceCorQQuotientOperations.ofFormalSumLedger_stokesResidue_eq_zero
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotient.ofFormalSumLedger
      support
      (TraceCorQRelationLedger.stokesResidue source target support) =
      TraceCorQQuotient.zero :=
  TraceCorQQuotient.ofFormalSumLedger_stokesResidue_eq_zero
    source
    target
    support

end AnalyticMotives
end LFunctions
end Boundary

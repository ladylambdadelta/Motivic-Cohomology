import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.FormalSums.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Relations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Preparation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Preparation.Algebra.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Preparation.Composition.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Candidates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationClosure.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationClosure.Derived.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationClosure.Public.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Derived.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Public.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Certificates.Endpoint.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Candidates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Relation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Relation.NamedCoherence.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Setoid.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Setoid.NamedCoherence.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Owner

/-!
# Quotient trace correspondences

This file owns the quotient of formal Q-linear trace correspondences by the
analytic rewrite relations.

The quotient is where analytic equality of traces becomes categorical equality
of morphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The quotient root exposes relation soundness. -/
theorem TraceCorQQuotientRoot.sound
    {left right : TraceCorQQuotientCandidate}
    (relation : TraceCorQQuotientRelation left right) :
    TraceCorQQuotient.ofCandidate left =
      TraceCorQQuotient.ofCandidate right :=
  TraceCorQQuotient.sound
    relation

/-- The quotient root exposes same-formal-sum soundness. -/
theorem TraceCorQQuotientRoot.sound_sameFormalSum
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (same : left.formalSum = right.formalSum) :
    TraceCorQQuotient.ofCandidate left =
      TraceCorQQuotient.ofCandidate right :=
  TraceCorQQuotient.sound_sameFormalSum
    ledger
    same

/-- The quotient root exposes zero as the empty candidate class. -/
theorem TraceCorQQuotientRoot.zero_eq_ofCandidate_empty :
    TraceCorQQuotient.zero =
      TraceCorQQuotient.ofCandidate TraceCorQQuotientCandidate.empty :=
  TraceCorQQuotientOperations.zero_eq_ofCandidate_empty

/-- The quotient root exposes additive associativity. -/
theorem TraceCorQQuotientRoot.add_assoc
    (left middle right : TraceCorQQuotient) :
    TraceCorQQuotient.add
        (TraceCorQQuotient.add left middle)
        right =
      TraceCorQQuotient.add
        left
        (TraceCorQQuotient.add middle right) :=
  TraceCorQQuotientOperations.add_assoc
    left
    middle
    right

/-- The quotient root exposes additive commutativity. -/
theorem TraceCorQQuotientRoot.add_comm
    (left right : TraceCorQQuotient) :
    TraceCorQQuotient.add left right =
      TraceCorQQuotient.add right left :=
  TraceCorQQuotient.add_comm
    left
    right

/-- The quotient root exposes the named-zero left additive law. -/
theorem TraceCorQQuotientRoot.zero_add
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.add
      TraceCorQQuotient.zero
      candidateClass =
      candidateClass :=
  TraceCorQQuotient.zero_add
    candidateClass

/-- The quotient root exposes the named-zero right additive law. -/
theorem TraceCorQQuotientRoot.add_zero
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.add
      candidateClass
      TraceCorQQuotient.zero =
      candidateClass :=
  TraceCorQQuotient.add_zero
    candidateClass

/-- The quotient root exposes scalar multiplication on representatives. -/
theorem TraceCorQQuotientRoot.smul_ofCandidate
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQQuotient.smul
        coefficient
        (TraceCorQQuotient.ofCandidate candidate) =
      TraceCorQQuotient.ofCandidate
        (TraceCorQQuotientCandidate.smul coefficient candidate) :=
  TraceCorQQuotientOperations.smul_ofCandidate
    coefficient
    candidate

/-- The quotient root exposes that scalar multiplication preserves zero. -/
theorem TraceCorQQuotientRoot.smul_zero
    (coefficient : Rat) :
    TraceCorQQuotient.smul
      coefficient
      TraceCorQQuotient.zero =
      TraceCorQQuotient.zero :=
  TraceCorQQuotient.smul_zero
    coefficient

/-- The quotient root exposes scalar distributivity over addition. -/
theorem TraceCorQQuotientRoot.smul_add
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

/-- The quotient root exposes the scalar identity law. -/
theorem TraceCorQQuotientRoot.one_smul
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.smul 1 candidateClass =
      candidateClass :=
  TraceCorQQuotient.one_smul
    candidateClass

/-- The quotient root exposes scalar multiplication composition. -/
theorem TraceCorQQuotientRoot.smul_smul
    (leftCoefficient rightCoefficient : Rat)
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.smul
      leftCoefficient
      (TraceCorQQuotient.smul rightCoefficient candidateClass) =
      TraceCorQQuotient.smul
        (leftCoefficient * rightCoefficient)
        candidateClass :=
  TraceCorQQuotient.smul_smul
    leftCoefficient
    rightCoefficient
    candidateClass

/-- The quotient root exposes composition on representatives. -/
theorem TraceCorQQuotientRoot.comp_ofCandidate
    (left right : TraceCorQQuotientCandidate) :
    TraceCorQQuotient.comp
        (TraceCorQQuotient.ofCandidate left)
        (TraceCorQQuotient.ofCandidate right) =
      TraceCorQQuotient.ofCandidate
        (TraceCorQQuotientCandidate.comp left right) :=
  TraceCorQQuotientOperations.comp_ofCandidate
    left
    right

/-- The quotient root exposes composition associativity. -/
theorem TraceCorQQuotientRoot.comp_assoc
    (left middle right : TraceCorQQuotient) :
    TraceCorQQuotient.comp
        (TraceCorQQuotient.comp left middle)
        right =
      TraceCorQQuotient.comp
        left
        (TraceCorQQuotient.comp middle right) :=
  TraceCorQQuotientOperations.comp_assoc
    left
    middle
    right

/-- Standard zero notation unfolds to the concrete quotient zero at the quotient root. -/
theorem TraceCorQQuotientRoot.inst_zero_eq :
    (0 : TraceCorQQuotient) =
      TraceCorQQuotient.zero :=
  TraceCorQQuotient.inst_zero_eq

/-- Standard addition notation unfolds to concrete quotient addition at the quotient root. -/
theorem TraceCorQQuotientRoot.inst_add_eq
    (left right : TraceCorQQuotient) :
    left + right =
      TraceCorQQuotient.add left right :=
  TraceCorQQuotient.inst_add_eq
    left
    right

/-- Standard rational scalar notation unfolds to concrete quotient scalar multiplication. -/
theorem TraceCorQQuotientRoot.inst_smul_eq
    (coefficient : Rat)
    (candidateClass : TraceCorQQuotient) :
    coefficient • candidateClass =
      TraceCorQQuotient.smul coefficient candidateClass :=
  TraceCorQQuotient.inst_smul_eq
    coefficient
    candidateClass

end AnalyticMotives
end LFunctions
end Boundary

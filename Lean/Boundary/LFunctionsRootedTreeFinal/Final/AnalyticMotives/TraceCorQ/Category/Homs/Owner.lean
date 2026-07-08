import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Terms.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.FormalSums.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Classes.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Certificates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.RelationWitnesses.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.RelationWitnesses.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.RelationWitnesses.Payload.Lengths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.RelationWitnesses.Payload.OperationLengths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Ambient.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.NamedCoherence.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Add.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.RelationWitnesses.Add.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Add.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Add.Laws.Derived.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Smul.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.RelationWitnesses.Smul.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Smul.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Smul.Laws.Derived.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Neg.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Neg.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Neg.Laws.Derived.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Sub.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Sub.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Sub.Laws.Derived.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Instances.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Instances.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Instances.Laws.Algebra.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Instances.Algebraic.Owner

/-!
# Typed hom classes for trace correspondences

This file owns the typed hom layer for the trace-correspondence category.

The ambient quotient `TraceCorQQuotient` is an untyped Q-linear span of trace
correspondence generators.  The category layer must refine it to hom classes
whose formal representatives have a common source and target object.  This is
the layer where identity laws become meaningful.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The hom root exposes typed-term source endpoints. -/
theorem TraceCorQHoms.term_generator_source
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target) :
    term.generator.source =
      source :=
  TraceCorQHomTerm.generator_source
    term

/-- The hom root exposes typed-term target endpoints. -/
theorem TraceCorQHoms.term_generator_target
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target) :
    term.generator.target =
      target :=
  TraceCorQHomTerm.generator_target
    term

/-- The hom root exposes typed-term imported-rectangle counts. -/
theorem TraceCorQHoms.term_importedRectangleCount_eq_length
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target) :
    term.importedRectangleCount =
      term.importedRectangles.length :=
  TraceCorQHomTerm.importedRectangleCount_eq_length_importedRectangles
    term

/-- The hom root exposes representative certificate ledgers. -/
theorem TraceCorQHoms.representative_certificateLedger_eq
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    representative.certificateLedger =
      ResidueChannelCertificateLedger.append
        representative.formalSum.certificateLedger
        representative.ledger.certificateLedger :=
  TraceCorQHomRepresentative.certificateLedger_eq
    representative

/-- The hom root exposes the zero typed hom representative. -/
theorem TraceCorQHoms.zero_eq_ofFormalSum_zero
    (source target : TraceCorQObject) :
    TraceCorQHom.zero source target =
      TraceCorQHom.ofFormalSum
        (TraceCorQHomFormalSum.zero source target) :=
  TraceCorQHom.zero_eq_ofFormalSum_zero
    source
    target

/-- The hom root exposes singleton typed hom representatives. -/
theorem TraceCorQHoms.singleton_eq_ofFormalSum_singleton
    (source target : TraceCorQObject)
    (coefficient : Rat)
    (generator : TraceCorQGenerator)
    (source_eq : generator.source = source)
    (target_eq : generator.target = target) :
    TraceCorQHom.singleton
      source
      target
      coefficient
      generator
      source_eq
      target_eq =
      TraceCorQHom.ofFormalSum
        (TraceCorQHomFormalSum.singleton
          source
          target
          coefficient
          generator
          source_eq
          target_eq) :=
  TraceCorQHom.singleton_eq_ofFormalSum_singleton
    source
    target
    coefficient
    generator
    source_eq
    target_eq

/-- The hom root exposes the fixed-endpoint additive group structure. -/
def TraceCorQHoms.addCommGroupStructure
    {source target : TraceCorQObject} :
    AddCommGroup (TraceCorQHom source target) :=
  traceCorQHomAddCommGroup

/-- The hom root exposes the fixed-endpoint rational module structure. -/
def TraceCorQHoms.ratModuleStructure
    {source target : TraceCorQObject} :
    Module Rat (TraceCorQHom source target) :=
  traceCorQHomRatModule

end AnalyticMotives
end LFunctions
end Boundary

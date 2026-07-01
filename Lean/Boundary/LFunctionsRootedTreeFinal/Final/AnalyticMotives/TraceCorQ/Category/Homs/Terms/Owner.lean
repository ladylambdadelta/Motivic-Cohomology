import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.FormalSums.Owner

/-!
# Typed trace-correspondence terms

This file owns one weighted trace-correspondence generator with fixed source
and target objects.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A weighted generator whose transport has the declared source and target. -/
abbrev TraceCorQHomTerm
    (source target : TraceCorQObject) :=
  { term : TraceCorQTerm //
    term.2.source = source ∧ term.2.target = target }

/-- The raw weighted term underlying a typed hom term. -/
def TraceCorQHomTerm.raw
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target) :
    TraceCorQTerm :=
  term.1

/-- The rational coefficient of a typed hom term. -/
def TraceCorQHomTerm.coefficient
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target) :
    Rat :=
  term.raw.1

/-- The trace-correspondence generator of a typed hom term. -/
def TraceCorQHomTerm.generator
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target) :
    TraceCorQGenerator :=
  term.raw.2

/-- The analytic certificate ledger carried by a typed hom term. -/
def TraceCorQHomTerm.certificateLedger
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target) :
    ResidueChannelCertificateLedger :=
  term.raw.certificateLedger

/-- Build a typed hom term from a coefficient, generator, and endpoint equalities. -/
def TraceCorQHomTerm.ofGenerator
    (source target : TraceCorQObject)
    (coefficient : Rat)
    (generator : TraceCorQGenerator)
    (source_eq : generator.source = source)
    (target_eq : generator.target = target) :
    TraceCorQHomTerm source target :=
  ⟨(coefficient, generator), And.intro source_eq target_eq⟩

/-- The raw term of a built typed hom term is the supplied weighted generator. -/
theorem TraceCorQHomTerm.ofGenerator_raw
    (source target : TraceCorQObject)
    (coefficient : Rat)
    (generator : TraceCorQGenerator)
    (source_eq : generator.source = source)
    (target_eq : generator.target = target) :
    (TraceCorQHomTerm.ofGenerator
      source
      target
      coefficient
      generator
      source_eq
      target_eq).raw =
      (coefficient, generator) :=
  rfl

/-- The certificate ledger of a built typed hom term is the generator certificate ledger. -/
theorem TraceCorQHomTerm.ofGenerator_certificateLedger
    (source target : TraceCorQObject)
    (coefficient : Rat)
    (generator : TraceCorQGenerator)
    (source_eq : generator.source = source)
    (target_eq : generator.target = target) :
    (TraceCorQHomTerm.ofGenerator
      source
      target
      coefficient
      generator
      source_eq
      target_eq).certificateLedger =
      generator.certificateLedger :=
  rfl

/-- The source endpoint proof carried by a typed hom term. -/
theorem TraceCorQHomTerm.generator_source
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target) :
    term.generator.source = source :=
  term.2.1

/-- The target endpoint proof carried by a typed hom term. -/
theorem TraceCorQHomTerm.generator_target
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target) :
    term.generator.target = target :=
  term.2.2

end AnalyticMotives
end LFunctions
end Boundary

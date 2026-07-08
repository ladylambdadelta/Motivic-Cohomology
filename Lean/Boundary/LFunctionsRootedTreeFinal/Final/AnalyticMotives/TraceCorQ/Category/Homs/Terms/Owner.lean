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

/-- The imported finite-rectangle payload carried by a typed hom term. -/
def TraceCorQHomTerm.importedRectangleCount
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target) :
    Nat :=
  term.certificateLedger.importedRectangleCount

/-- The imported finite explicit-formula rectangles carried by a typed hom term. -/
def TraceCorQHomTerm.importedRectangles
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  term.certificateLedger.importedRectangles

/-- The internal trace-bookkeeping payload carried by a typed hom term. -/
def TraceCorQHomTerm.traceBookkeepingCount
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target) :
    Nat :=
  term.certificateLedger.traceBookkeepingCount

/-- The explicit rewrite-step payload carried by a typed hom term. -/
def TraceCorQHomTerm.rewriteStepCount
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target) :
    Nat :=
  term.certificateLedger.rewriteStepCount

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

/-- The imported payload of a built typed hom term is the generator imported payload. -/
theorem TraceCorQHomTerm.ofGenerator_importedRectangleCount
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
      target_eq).importedRectangleCount =
      generator.importedRectangleCount :=
  rfl

/-- The imported rectangles of a built typed hom term are the generator rectangles. -/
theorem TraceCorQHomTerm.ofGenerator_importedRectangles
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
      target_eq).importedRectangles =
      generator.importedRectangles :=
  rfl

/-- The bookkeeping payload of a built typed hom term is the generator bookkeeping payload. -/
theorem TraceCorQHomTerm.ofGenerator_traceBookkeepingCount
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
      target_eq).traceBookkeepingCount =
      generator.traceBookkeepingCount :=
  rfl

/-- The rewrite-step payload of a built typed hom term is the generator rewrite-step payload. -/
theorem TraceCorQHomTerm.ofGenerator_rewriteStepCount
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
      target_eq).rewriteStepCount =
      generator.rewriteStepCount :=
  rfl

/-- A typed hom term has the same rewrite-step payload as its raw term. -/
theorem TraceCorQHomTerm.rewriteStepCount_eq_raw
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target) :
    term.rewriteStepCount =
      term.raw.rewriteStepCount :=
  rfl

/-- A typed hom term has the same imported rectangles as its raw term. -/
theorem TraceCorQHomTerm.importedRectangles_eq_raw
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target) :
    term.importedRectangles =
      term.raw.importedRectangles :=
  rfl

/-- A typed hom term's imported-rectangle count is the length of its rectangle list. -/
theorem TraceCorQHomTerm.importedRectangleCount_eq_length_importedRectangles
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target) :
    term.importedRectangleCount =
      term.importedRectangles.length :=
  ResidueChannelCertificateLedger.importedRectangleCount_eq_length_importedRectangles
    term.certificateLedger

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

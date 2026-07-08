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

/-- The analytic certificate ledger carried by a typed formal sum. -/
def TraceCorQHomFormalSum.certificateLedger
    {source target : TraceCorQObject}
    (formalSum : TraceCorQHomFormalSum source target) :
    ResidueChannelCertificateLedger :=
  formalSum.raw.certificateLedger

/-- The imported finite-rectangle payload carried by a typed formal sum. -/
def TraceCorQHomFormalSum.importedRectangleCount
    {source target : TraceCorQObject}
    (formalSum : TraceCorQHomFormalSum source target) :
    Nat :=
  formalSum.certificateLedger.importedRectangleCount

/-- The imported finite explicit-formula rectangles carried by a typed formal sum. -/
def TraceCorQHomFormalSum.importedRectangles
    {source target : TraceCorQObject}
    (formalSum : TraceCorQHomFormalSum source target) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  formalSum.certificateLedger.importedRectangles

/-- The internal trace-bookkeeping payload carried by a typed formal sum. -/
def TraceCorQHomFormalSum.traceBookkeepingCount
    {source target : TraceCorQObject}
    (formalSum : TraceCorQHomFormalSum source target) :
    Nat :=
  formalSum.certificateLedger.traceBookkeepingCount

/-- The explicit rewrite-step payload carried by a typed formal sum. -/
def TraceCorQHomFormalSum.rewriteStepCount
    {source target : TraceCorQObject}
    (formalSum : TraceCorQHomFormalSum source target) :
    Nat :=
  formalSum.certificateLedger.rewriteStepCount

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

/-- The empty typed formal sum carries the empty analytic certificate ledger. -/
theorem TraceCorQHomFormalSum.zero_certificateLedger
    (source target : TraceCorQObject) :
    (TraceCorQHomFormalSum.zero source target).certificateLedger =
      ResidueChannelCertificateLedger.empty :=
  rfl

/-- The empty typed formal sum carries no imported finite-rectangle payload. -/
theorem TraceCorQHomFormalSum.zero_importedRectangleCount
    (source target : TraceCorQObject) :
    (TraceCorQHomFormalSum.zero source target).importedRectangleCount =
      0 :=
  rfl

/-- The empty typed formal sum exposes no imported finite explicit-formula rectangles. -/
theorem TraceCorQHomFormalSum.zero_importedRectangles
    (source target : TraceCorQObject) :
    (TraceCorQHomFormalSum.zero source target).importedRectangles =
      [] :=
  rfl

/-- The empty typed formal sum carries no internal trace-bookkeeping payload. -/
theorem TraceCorQHomFormalSum.zero_traceBookkeepingCount
    (source target : TraceCorQObject) :
    (TraceCorQHomFormalSum.zero source target).traceBookkeepingCount =
      0 :=
  rfl

/-- The empty typed formal sum carries no explicit rewrite-step payload. -/
theorem TraceCorQHomFormalSum.zero_rewriteStepCount
    (source target : TraceCorQObject) :
    (TraceCorQHomFormalSum.zero source target).rewriteStepCount =
      0 :=
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

/-- The certificate ledger of a typed singleton is the generator certificate ledger. -/
theorem TraceCorQHomFormalSum.singleton_certificateLedger
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
      target_eq).certificateLedger =
      ResidueChannelCertificateLedger.append
        generator.certificateLedger
        ResidueChannelCertificateLedger.empty :=
  rfl

/-- The imported payload of a typed singleton is the generator payload plus the empty tail. -/
theorem TraceCorQHomFormalSum.singleton_importedRectangleCount
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
      target_eq).importedRectangleCount =
      generator.importedRectangleCount +
        ResidueChannelCertificateLedger.empty.importedRectangleCount :=
  ResidueChannelCertificateLedger.append_importedRectangleCount
    generator.certificateLedger
    ResidueChannelCertificateLedger.empty

/-- The imported rectangles of a typed singleton are the generator rectangles. -/
theorem TraceCorQHomFormalSum.singleton_importedRectangles
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
      target_eq).importedRectangles =
      generator.importedRectangles ++
        ResidueChannelCertificateLedger.empty.importedRectangles :=
  ResidueChannelCertificateLedger.append_importedRectangles
    generator.certificateLedger
    ResidueChannelCertificateLedger.empty

/-- The bookkeeping payload of a typed singleton is the generator payload plus the empty tail. -/
theorem TraceCorQHomFormalSum.singleton_traceBookkeepingCount
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
      target_eq).traceBookkeepingCount =
      generator.traceBookkeepingCount +
        ResidueChannelCertificateLedger.empty.traceBookkeepingCount :=
  ResidueChannelCertificateLedger.append_traceBookkeepingCount
    generator.certificateLedger
    ResidueChannelCertificateLedger.empty

/-- The rewrite-step payload of a typed singleton is the generator payload plus the empty tail. -/
theorem TraceCorQHomFormalSum.singleton_rewriteStepCount
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
      target_eq).rewriteStepCount =
      generator.rewriteStepCount +
        ResidueChannelCertificateLedger.empty.rewriteStepCount :=
  ResidueChannelCertificateLedger.append_rewriteStepCount
    generator.certificateLedger
    ResidueChannelCertificateLedger.empty

/-- Raw forgetful map sends typed addition to raw formal-sum addition. -/
theorem TraceCorQHomFormalSum.add_raw
    {source target : TraceCorQObject}
    (left right : TraceCorQHomFormalSum source target) :
    (TraceCorQHomFormalSum.add left right).raw =
      TraceCorQFormalSum.add left.raw right.raw :=
  List.map_append TraceCorQHomTerm.raw left right

/-- Typed formal-sum addition appends analytic certificate ledgers. -/
theorem TraceCorQHomFormalSum.add_certificateLedger
    {source target : TraceCorQObject}
    (left right : TraceCorQHomFormalSum source target) :
    (TraceCorQHomFormalSum.add left right).certificateLedger =
      ResidueChannelCertificateLedger.append
        left.certificateLedger
        right.certificateLedger :=
  Eq.trans
    (congrArg
      TraceCorQFormalSum.certificateLedger
      (TraceCorQHomFormalSum.add_raw left right))
    (TraceCorQFormalSum.add_certificateLedger left.raw right.raw)

/-- Typed formal-sum addition adds imported finite-rectangle payload. -/
theorem TraceCorQHomFormalSum.add_importedRectangleCount
    {source target : TraceCorQObject}
    (left right : TraceCorQHomFormalSum source target) :
    (TraceCorQHomFormalSum.add left right).importedRectangleCount =
      left.importedRectangleCount +
        right.importedRectangleCount :=
  Eq.trans
    (congrArg
      ResidueChannelCertificateLedger.importedRectangleCount
      (TraceCorQHomFormalSum.add_certificateLedger left right))
    (ResidueChannelCertificateLedger.append_importedRectangleCount
      left.certificateLedger
      right.certificateLedger)

/-- Typed formal-sum addition concatenates imported finite explicit-formula rectangles. -/
theorem TraceCorQHomFormalSum.add_importedRectangles
    {source target : TraceCorQObject}
    (left right : TraceCorQHomFormalSum source target) :
    (TraceCorQHomFormalSum.add left right).importedRectangles =
      left.importedRectangles ++
        right.importedRectangles :=
  Eq.trans
    (congrArg
      ResidueChannelCertificateLedger.importedRectangles
      (TraceCorQHomFormalSum.add_certificateLedger left right))
    (ResidueChannelCertificateLedger.append_importedRectangles
      left.certificateLedger
      right.certificateLedger)

/-- A typed formal sum's imported-rectangle count is the length of its rectangle list. -/
theorem TraceCorQHomFormalSum.importedRectangleCount_eq_length_importedRectangles
    {source target : TraceCorQObject}
    (formalSum : TraceCorQHomFormalSum source target) :
    formalSum.importedRectangleCount =
      formalSum.importedRectangles.length :=
  ResidueChannelCertificateLedger.importedRectangleCount_eq_length_importedRectangles
    formalSum.certificateLedger

/-- Typed formal-sum addition adds internal trace-bookkeeping payload. -/
theorem TraceCorQHomFormalSum.add_traceBookkeepingCount
    {source target : TraceCorQObject}
    (left right : TraceCorQHomFormalSum source target) :
    (TraceCorQHomFormalSum.add left right).traceBookkeepingCount =
      left.traceBookkeepingCount +
        right.traceBookkeepingCount :=
  Eq.trans
    (congrArg
      ResidueChannelCertificateLedger.traceBookkeepingCount
      (TraceCorQHomFormalSum.add_certificateLedger left right))
    (ResidueChannelCertificateLedger.append_traceBookkeepingCount
      left.certificateLedger
      right.certificateLedger)

/-- Typed formal-sum addition adds explicit rewrite-step payload. -/
theorem TraceCorQHomFormalSum.add_rewriteStepCount
    {source target : TraceCorQObject}
    (left right : TraceCorQHomFormalSum source target) :
    (TraceCorQHomFormalSum.add left right).rewriteStepCount =
      left.rewriteStepCount +
        right.rewriteStepCount :=
  Eq.trans
    (congrArg
      ResidueChannelCertificateLedger.rewriteStepCount
      (TraceCorQHomFormalSum.add_certificateLedger left right))
    (ResidueChannelCertificateLedger.append_rewriteStepCount
      left.certificateLedger
      right.certificateLedger)

end AnalyticMotives
end LFunctions
end Boundary

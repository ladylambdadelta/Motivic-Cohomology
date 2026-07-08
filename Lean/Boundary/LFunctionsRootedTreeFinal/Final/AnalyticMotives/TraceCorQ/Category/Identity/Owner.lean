import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.IdentitySupport.Owner

/-!
# Identities for typed trace-correspondence homs

This file owns identity morphisms for the typed hom layer.

The implementation is to use `TraceCorQGenerator.id` as the singleton identity
representative and the ledgered identity-support theorems as the proof source
for left and right identity laws.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The canonical identity representative on a trace-correspondence object. -/
def TraceCorQHomRepresentative.id
    (object : TraceCorQObject) :
    TraceCorQHomRepresentative object object :=
  TraceCorQHomRepresentative.ofFormalSumLedger
    (TraceCorQHomFormalSum.singleton
      object
      object
      1
      (TraceCorQGenerator.id object)
      (TraceCorQGenerator.id_source object)
      (TraceCorQGenerator.id_target object))
    TraceCorQRelationLedger.empty

/-- The identity representative has empty relation ledger. -/
theorem TraceCorQHomRepresentative.id_ledger
    (object : TraceCorQObject) :
    (TraceCorQHomRepresentative.id object).ledger =
      TraceCorQRelationLedger.empty :=
  rfl

/-- The identity representative certificate ledger is the singleton identity generator ledger. -/
theorem TraceCorQHomRepresentative.id_certificateLedger
    (object : TraceCorQObject) :
    (TraceCorQHomRepresentative.id object).certificateLedger =
      ResidueChannelCertificateLedger.append
        (ResidueChannelCertificateLedger.append
          (TraceCorQGenerator.id object).certificateLedger
          ResidueChannelCertificateLedger.empty)
        TraceCorQRelationLedger.empty.certificateLedger :=
  rfl

/-- The identity representative imports the identity generator payload. -/
theorem TraceCorQHomRepresentative.id_importedRectangleCount
    (object : TraceCorQObject) :
    (TraceCorQHomRepresentative.id object).importedRectangleCount =
      (TraceCorQGenerator.id object).importedRectangleCount +
        ResidueChannelCertificateLedger.empty.importedRectangleCount +
          TraceCorQRelationLedger.empty.importedRectangleCount :=
  Eq.trans
    (TraceCorQHomRepresentative.importedRectangleCount_eq
      (TraceCorQHomRepresentative.id object))
    (congrArg
      (fun count =>
        count + TraceCorQRelationLedger.empty.importedRectangleCount)
      (TraceCorQHomFormalSum.singleton_importedRectangleCount
        object
        object
        1
        (TraceCorQGenerator.id object)
        (TraceCorQGenerator.id_source object)
        (TraceCorQGenerator.id_target object)))

/-- The identity representative exposes the identity generator imported rectangles. -/
theorem TraceCorQHomRepresentative.id_importedRectangles
    (object : TraceCorQObject) :
    (TraceCorQHomRepresentative.id object).importedRectangles =
      ((TraceCorQGenerator.id object).importedRectangles ++
        ResidueChannelCertificateLedger.empty.importedRectangles) ++
          TraceCorQRelationLedger.empty.importedRectangles :=
  Eq.trans
    (TraceCorQHomRepresentative.importedRectangles_eq
      (TraceCorQHomRepresentative.id object))
    (congrArg
      (fun rectangles =>
        rectangles ++ TraceCorQRelationLedger.empty.importedRectangles)
      (TraceCorQHomFormalSum.singleton_importedRectangles
        object
        object
        1
        (TraceCorQGenerator.id object)
        (TraceCorQGenerator.id_source object)
        (TraceCorQGenerator.id_target object)))

/-- The identity representative keeps the identity generator bookkeeping payload. -/
theorem TraceCorQHomRepresentative.id_traceBookkeepingCount
    (object : TraceCorQObject) :
    (TraceCorQHomRepresentative.id object).traceBookkeepingCount =
      (TraceCorQGenerator.id object).traceBookkeepingCount +
        ResidueChannelCertificateLedger.empty.traceBookkeepingCount +
          TraceCorQRelationLedger.empty.traceBookkeepingCount :=
  Eq.trans
    (TraceCorQHomRepresentative.traceBookkeepingCount_eq
      (TraceCorQHomRepresentative.id object))
    (congrArg
      (fun count =>
        count + TraceCorQRelationLedger.empty.traceBookkeepingCount)
      (TraceCorQHomFormalSum.singleton_traceBookkeepingCount
        object
        object
        1
        (TraceCorQGenerator.id object)
        (TraceCorQGenerator.id_source object)
        (TraceCorQGenerator.id_target object)))

/-- The identity representative keeps the identity generator rewrite-step payload. -/
theorem TraceCorQHomRepresentative.id_rewriteStepCount
    (object : TraceCorQObject) :
    (TraceCorQHomRepresentative.id object).rewriteStepCount =
      (TraceCorQGenerator.id object).rewriteStepCount +
        ResidueChannelCertificateLedger.empty.rewriteStepCount +
          TraceCorQRelationLedger.empty.rewriteStepCount :=
  Eq.trans
    (TraceCorQHomRepresentative.rewriteStepCount_eq
      (TraceCorQHomRepresentative.id object))
    (congrArg
      (fun count =>
        count + TraceCorQRelationLedger.empty.rewriteStepCount)
      (TraceCorQHomFormalSum.singleton_rewriteStepCount
        object
        object
        1
        (TraceCorQGenerator.id object)
        (TraceCorQGenerator.id_source object)
        (TraceCorQGenerator.id_target object)))

/-- The identity typed hom class on a trace-correspondence object. -/
def TraceCorQHom.id
    (object : TraceCorQObject) :
    TraceCorQHom object object :=
  TraceCorQHom.ofRepresentative
    (TraceCorQHomRepresentative.id object)

/-- The identity class is represented by the canonical identity representative. -/
theorem TraceCorQHom.id_eq_ofRepresentative_id
    (object : TraceCorQObject) :
    TraceCorQHom.id object =
      TraceCorQHom.ofRepresentative
        (TraceCorQHomRepresentative.id object) :=
  rfl

/-- The ambient class of a typed identity is the ambient singleton identity. -/
theorem TraceCorQHom.ambient_id
    (object : TraceCorQObject) :
    TraceCorQHom.ambient
      (TraceCorQHom.id object) =
      TraceCorQQuotient.singleton
        1
        (TraceCorQGenerator.id object) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

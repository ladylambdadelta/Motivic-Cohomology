import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Carrier.TraceHom.TypedOperations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Identity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Identity.Owner

/-!
# Typed hom identity carriers for analytic effective realization

This file exposes the fixed-endpoint identity morphisms for the typed
trace-correspondence category, their representatives, payload formulas, and
the typed left/right identity laws.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The canonical identity representative on a trace object. -/
def TraceAnalyticEffectiveRealization.traceHomIdentityRepresentative
    (object : TraceCorQObject) :
    TraceCorQHomRepresentative object object :=
  TraceCorQHomRepresentative.id object

/-- The typed identity hom on a trace object. -/
def TraceAnalyticEffectiveRealization.traceHomTypedIdentity
    (object : TraceCorQObject) :
    TraceCorQHom object object :=
  TraceCorQHom.id object

/-- The identity representative is the existing canonical representative. -/
theorem TraceAnalyticEffectiveRealization.traceHomIdentityRepresentative_eq
    (object : TraceCorQObject) :
    TraceAnalyticEffectiveRealization.traceHomIdentityRepresentative object =
      TraceCorQHomRepresentative.id object :=
  rfl

/-- The typed identity is represented by the canonical identity representative. -/
theorem TraceAnalyticEffectiveRealization.traceHomTypedIdentity_eq_ofRepresentative
    (object : TraceCorQObject) :
    TraceAnalyticEffectiveRealization.traceHomTypedIdentity object =
      TraceCorQHom.ofRepresentative
        (TraceAnalyticEffectiveRealization.traceHomIdentityRepresentative
          object) :=
  TraceCorQHom.id_eq_ofRepresentative_id
    object

/-- The identity representative has empty relation ledger. -/
theorem TraceAnalyticEffectiveRealization.traceHomIdentityRepresentative_ledger
    (object : TraceCorQObject) :
    (TraceAnalyticEffectiveRealization.traceHomIdentityRepresentative
      object).ledger =
      TraceCorQRelationLedger.empty :=
  TraceCorQHomRepresentative.id_ledger
    object

/-- The identity representative certificate ledger is the singleton identity generator ledger. -/
theorem TraceAnalyticEffectiveRealization.traceHomIdentityRepresentative_certificateLedger
    (object : TraceCorQObject) :
    (TraceAnalyticEffectiveRealization.traceHomIdentityRepresentative
      object).certificateLedger =
      ResidueChannelCertificateLedger.append
        (ResidueChannelCertificateLedger.append
          (TraceCorQGenerator.id object).certificateLedger
          ResidueChannelCertificateLedger.empty)
        TraceCorQRelationLedger.empty.certificateLedger :=
  TraceCorQHomRepresentative.id_certificateLedger
    object

/-- The identity representative imported count is the identity generator count plus empty tails. -/
theorem TraceAnalyticEffectiveRealization.traceHomIdentityRepresentative_importedRectangleCount
    (object : TraceCorQObject) :
    (TraceAnalyticEffectiveRealization.traceHomIdentityRepresentative
      object).importedRectangleCount =
      (TraceCorQGenerator.id object).importedRectangleCount +
        ResidueChannelCertificateLedger.empty.importedRectangleCount +
          TraceCorQRelationLedger.empty.importedRectangleCount :=
  TraceCorQHomRepresentative.id_importedRectangleCount
    object

/-- The ambient class of a typed identity is the ambient singleton identity. -/
theorem TraceAnalyticEffectiveRealization.traceHomTypedIdentity_ambient
    (object : TraceCorQObject) :
    TraceCorQHom.ambient
      (TraceAnalyticEffectiveRealization.traceHomTypedIdentity object) =
      TraceCorQQuotient.singleton
        1
        (TraceCorQGenerator.id object) :=
  TraceCorQHom.ambient_id
    object

/-- Left identity for typed trace homs. -/
theorem TraceAnalyticEffectiveRealization.traceHomTypedIdentity_left
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceAnalyticEffectiveRealization.traceHomTypedComp
      (TraceAnalyticEffectiveRealization.traceHomTypedIdentity source)
      hom =
      hom :=
  TraceCorQCategoryIdentity.left_id
    hom

/-- Right identity for typed trace homs. -/
theorem TraceAnalyticEffectiveRealization.traceHomTypedIdentity_right
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceAnalyticEffectiveRealization.traceHomTypedComp
      hom
      (TraceAnalyticEffectiveRealization.traceHomTypedIdentity target) =
      hom :=
  TraceCorQCategoryIdentity.right_id
    hom

/-- The identity composed with itself is the identity. -/
theorem TraceAnalyticEffectiveRealization.traceHomTypedIdentity_comp_self
    (object : TraceCorQObject) :
    TraceAnalyticEffectiveRealization.traceHomTypedComp
      (TraceAnalyticEffectiveRealization.traceHomTypedIdentity object)
      (TraceAnalyticEffectiveRealization.traceHomTypedIdentity object) =
      TraceAnalyticEffectiveRealization.traceHomTypedIdentity object :=
  TraceCorQCategoryIdentity.id_comp_id
    object

end AnalyticMotives
end LFunctions
end Boundary

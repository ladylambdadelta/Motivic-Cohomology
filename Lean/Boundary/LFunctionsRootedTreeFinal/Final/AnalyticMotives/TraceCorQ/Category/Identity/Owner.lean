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

/-- The identity typed hom class on a trace-correspondence object. -/
def TraceCorQHom.id
    (object : TraceCorQObject) :
    TraceCorQHom object object :=
  TraceCorQHom.singleton
    object
    object
    1
    (TraceCorQGenerator.id object)
    (TraceCorQGenerator.id_source object)
    (TraceCorQGenerator.id_target object)

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

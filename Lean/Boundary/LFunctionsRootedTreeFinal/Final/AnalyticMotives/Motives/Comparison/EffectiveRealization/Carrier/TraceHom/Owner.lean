import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Carrier.TraceHom.Representative.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Carrier.TraceHom.RelationWitness.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Carrier.TraceHom.QuotientOperations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Carrier.TraceHom.TypedOperations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Carrier.TraceHom.TypedIdentity.Owner

/-!
# Trace hom carriers for analytic effective realization

This file exposes the concrete morphism-side carriers used by the analytic
effective-realization comparison.  A quotient hom contributes its ambient
quotient class; a chosen representative contributes the certificate-bearing
trace calculus data; a relation witness contributes the certificate-bearing
ledger data needed for quotient descent.  The ambient quotient class and its
descended operations, together with fixed-endpoint typed operations and
identities, are re-exported here as well.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The comparison boundary keeps the actual typed trace hom as its quotient carrier. -/
def TraceAnalyticEffectiveRealization.traceHomCarrier
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom source target :=
  hom

/-- The ambient untyped quotient class carried by a typed trace hom. -/
def TraceAnalyticEffectiveRealization.traceHomAmbient
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQQuotient :=
  TraceCorQHom.ambient hom

/-- A representative determines a typed quotient hom. -/
def TraceAnalyticEffectiveRealization.traceHomOfRepresentative
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    TraceCorQHom source target :=
  TraceCorQHom.ofRepresentative representative

/-- A typed formal sum determines a typed quotient hom. -/
def TraceAnalyticEffectiveRealization.traceHomOfFormalSum
    {source target : TraceCorQObject}
    (formalSum : TraceCorQHomFormalSum source target) :
    TraceCorQHom source target :=
  TraceCorQHom.ofFormalSum formalSum

/-- The zero typed quotient hom between two trace objects. -/
def TraceAnalyticEffectiveRealization.traceHomZero
    (source target : TraceCorQObject) :
    TraceCorQHom source target :=
  TraceCorQHom.zero source target

/-- The typed trace hom carrier is definitionally the supplied quotient hom. -/
theorem TraceAnalyticEffectiveRealization.traceHomCarrier_eq
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceAnalyticEffectiveRealization.traceHomCarrier hom =
      hom :=
  rfl

/-- The ambient quotient carried by a representative hom is the representative ambient class. -/
theorem TraceAnalyticEffectiveRealization.traceHomAmbient_ofRepresentative
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    TraceAnalyticEffectiveRealization.traceHomAmbient
      (TraceAnalyticEffectiveRealization.traceHomOfRepresentative representative) =
      TraceAnalyticEffectiveRealization.traceHomRepresentativeAmbientClass
        representative :=
  TraceCorQHom.ambient_ofRepresentative
    representative

/-- The ambient quotient carried by a formal-sum hom is its raw formal-sum class. -/
theorem TraceAnalyticEffectiveRealization.traceHomAmbient_ofFormalSum
    {source target : TraceCorQObject}
    (formalSum : TraceCorQHomFormalSum source target) :
    TraceAnalyticEffectiveRealization.traceHomAmbient
      (TraceAnalyticEffectiveRealization.traceHomOfFormalSum formalSum) =
      TraceCorQQuotient.ofFormalSum formalSum.raw :=
  TraceCorQHom.ambient_ofFormalSum
    formalSum

/-- The ambient quotient carried by the zero typed hom is the ambient zero class. -/
theorem TraceAnalyticEffectiveRealization.traceHomAmbient_zero
    (source target : TraceCorQObject) :
    TraceAnalyticEffectiveRealization.traceHomAmbient
      (TraceAnalyticEffectiveRealization.traceHomZero source target) =
      TraceCorQQuotient.zero :=
  TraceCorQHom.ambient_zero
    source
    target

/-- Ambient equality reflects equality for fixed-endpoint typed quotient homs. -/
theorem TraceAnalyticEffectiveRealization.traceHom_eq_of_ambient_eq
    {source target : TraceCorQObject}
    {left right : TraceCorQHom source target}
    (ambient_eq :
      TraceAnalyticEffectiveRealization.traceHomAmbient left =
        TraceAnalyticEffectiveRealization.traceHomAmbient right) :
    left = right :=
  TraceCorQHom.eq_of_ambient_eq
    ambient_eq

end AnalyticMotives
end LFunctions
end Boundary

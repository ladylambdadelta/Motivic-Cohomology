import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Carrier.TraceHom.QuotientOperations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Carrier.TraceHom.Representative.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Add.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Smul.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Composition.Owner

/-!
# Typed hom operation carriers for analytic effective realization

This file exposes the fixed-endpoint typed hom operations and their projection
to the ambient raw trace-correspondence quotient.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Addition in a fixed typed trace hom space. -/
def TraceAnalyticEffectiveRealization.traceHomTypedAdd
    {source target : TraceCorQObject}
    (left right : TraceCorQHom source target) :
    TraceCorQHom source target :=
  TraceCorQHom.add left right

/-- Rational scalar multiplication in a fixed typed trace hom space. -/
def TraceAnalyticEffectiveRealization.traceHomTypedSmul
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (hom : TraceCorQHom source target) :
    TraceCorQHom source target :=
  TraceCorQHom.smul coefficient hom

/-- Composition of fixed-endpoint typed trace homs. -/
def TraceAnalyticEffectiveRealization.traceHomTypedComp
    {source middle target : TraceCorQObject}
    (left : TraceCorQHom source middle)
    (right : TraceCorQHom middle target) :
    TraceCorQHom source target :=
  TraceCorQHom.comp left right

/-- Typed addition agrees with representative addition. -/
theorem TraceAnalyticEffectiveRealization.traceHomTypedAdd_ofRepresentative
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :
    TraceAnalyticEffectiveRealization.traceHomTypedAdd
      (TraceCorQHom.ofRepresentative left)
      (TraceCorQHom.ofRepresentative right) =
      TraceCorQHom.ofRepresentative
        (TraceCorQHomRepresentative.add left right) :=
  TraceCorQHom.add_ofRepresentative
    left
    right

/-- Typed scalar multiplication agrees with representative scalar multiplication. -/
theorem TraceAnalyticEffectiveRealization.traceHomTypedSmul_ofRepresentative
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    TraceAnalyticEffectiveRealization.traceHomTypedSmul
      coefficient
      (TraceCorQHom.ofRepresentative representative) =
      TraceCorQHom.ofRepresentative
        (TraceCorQHomRepresentative.smul coefficient representative) :=
  TraceCorQHom.smul_ofRepresentative
    coefficient
    representative

/-- Typed composition agrees with representative composition. -/
theorem TraceAnalyticEffectiveRealization.traceHomTypedComp_ofRepresentative
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomRepresentative source middle)
    (right : TraceCorQHomRepresentative middle target) :
    TraceAnalyticEffectiveRealization.traceHomTypedComp
      (TraceCorQHom.ofRepresentative left)
      (TraceCorQHom.ofRepresentative right) =
      TraceCorQHom.ofRepresentative
        (TraceCorQHomRepresentative.comp left right) :=
  TraceCorQHom.comp_ofRepresentative
    left
    right

/-- The ambient map sends typed addition to ambient quotient addition. -/
theorem TraceAnalyticEffectiveRealization.traceHomTypedAmbient_add
    {source target : TraceCorQObject}
    (left right : TraceCorQHom source target) :
    TraceCorQHom.ambient
      (TraceAnalyticEffectiveRealization.traceHomTypedAdd left right) =
      TraceAnalyticEffectiveRealization.traceHomQuotientAdd
        (TraceCorQHom.ambient left)
        (TraceCorQHom.ambient right) :=
  TraceCorQHom.ambient_add
    left
    right

/-- The ambient map sends typed scalar multiplication to ambient quotient scaling. -/
theorem TraceAnalyticEffectiveRealization.traceHomTypedAmbient_smul
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (hom : TraceCorQHom source target) :
    TraceCorQHom.ambient
      (TraceAnalyticEffectiveRealization.traceHomTypedSmul coefficient hom) =
      TraceAnalyticEffectiveRealization.traceHomQuotientSmul
        coefficient
        (TraceCorQHom.ambient hom) :=
  TraceCorQHom.ambient_smul
    coefficient
    hom

/-- The ambient map sends typed composition to ambient quotient composition. -/
theorem TraceAnalyticEffectiveRealization.traceHomTypedAmbient_comp
    {source middle target : TraceCorQObject}
    (left : TraceCorQHom source middle)
    (right : TraceCorQHom middle target) :
    TraceCorQHom.ambient
      (TraceAnalyticEffectiveRealization.traceHomTypedComp left right) =
      TraceAnalyticEffectiveRealization.traceHomQuotientComp
        (TraceCorQHom.ambient left)
        (TraceCorQHom.ambient right) :=
  TraceCorQHom.ambient_comp
    left
    right

end AnalyticMotives
end LFunctions
end Boundary

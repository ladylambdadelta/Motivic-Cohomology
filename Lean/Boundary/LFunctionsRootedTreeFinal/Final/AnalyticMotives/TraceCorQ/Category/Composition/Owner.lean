import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.Associativity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Composition.Terms.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Composition.FormalSums.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Composition.Representatives.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Composition.RelationWitnesses.Owner

/-!
# Composition for typed trace-correspondence homs

This file owns composition of typed hom classes.

The implementation is to restrict the already constructed quotient
composition to source/target-compatible hom classes.  Associativity is powered
by `TraceCorQQuotient.comp_assoc`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The composition root exposes typed hom composition on representatives. -/
theorem TraceCorQComposition.comp_ofRepresentative
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomRepresentative source middle)
    (right : TraceCorQHomRepresentative middle target) :
    TraceCorQHom.comp
        (TraceCorQHom.ofRepresentative left)
        (TraceCorQHom.ofRepresentative right) =
      TraceCorQHom.ofRepresentative
        (TraceCorQHomRepresentative.comp left right) :=
  TraceCorQHom.comp_ofRepresentative
    left
    right

/-- The composition root exposes typed hom composition before the category instance is assembled. -/
theorem TraceCorQComposition.comp_eq
    {source middle target : TraceCorQObject}
    (left : TraceCorQHom source middle)
    (right : TraceCorQHom middle target) :
    TraceCorQHom.comp left right =
      TraceCorQHom.comp left right :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

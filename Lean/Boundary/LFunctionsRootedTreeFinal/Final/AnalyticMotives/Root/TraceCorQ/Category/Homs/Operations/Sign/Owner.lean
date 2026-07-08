import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Sub.Owner

/-!
# Public sign and subtraction operations for typed trace homs

This file exposes negation and subtraction of typed trace-correspondence hom
classes and their ambient compatibility.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes negation as scalar multiplication by `-1`. -/
theorem AnalyticMotivesRoot.traceCorQHom_neg_eq_smul_neg_one
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.neg hom =
      TraceCorQHom.smul (-1) hom :=
  TraceCorQHom.neg_eq_smul_neg_one
    hom

/-- The top root exposes ambient compatibility for typed negation. -/
theorem AnalyticMotivesRoot.traceCorQHom_ambient_neg
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.ambient
      (TraceCorQHom.neg hom) =
      TraceCorQQuotient.neg
        (TraceCorQHom.ambient hom) :=
  TraceCorQHom.ambient_neg
    hom

/-- The top root exposes subtraction as addition of the negative. -/
theorem AnalyticMotivesRoot.traceCorQHom_sub_eq_add_neg
    {source target : TraceCorQObject}
    (left right : TraceCorQHom source target) :
    TraceCorQHom.sub left right =
      TraceCorQHom.add left (TraceCorQHom.neg right) :=
  TraceCorQHom.sub_eq_add_neg
    left
    right

/-- The top root exposes ambient compatibility for typed subtraction. -/
theorem AnalyticMotivesRoot.traceCorQHom_ambient_sub
    {source target : TraceCorQObject}
    (left right : TraceCorQHom source target) :
    TraceCorQHom.ambient
      (TraceCorQHom.sub left right) =
      TraceCorQQuotient.sub
        (TraceCorQHom.ambient left)
        (TraceCorQHom.ambient right) :=
  TraceCorQHom.ambient_sub
    left
    right

end AnalyticMotives
end LFunctions
end Boundary

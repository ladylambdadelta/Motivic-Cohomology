import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Smul.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Neg.Owner

/-!
# Negation of typed trace-correspondence hom classes

This file owns negation in each fixed-endpoint typed hom quotient.  Negation is
the endpoint-preserving rational scalar action by `-1`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Negation of typed hom classes. -/
def TraceCorQHom.neg
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom source target :=
  TraceCorQHom.smul (-1) hom

/-- Typed hom negation is scalar multiplication by `-1`. -/
theorem TraceCorQHom.neg_eq_smul_neg_one
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.neg hom =
      TraceCorQHom.smul (-1) hom :=
  rfl

/-- The ambient map sends typed negation to quotient negation. -/
theorem TraceCorQHom.ambient_neg
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.ambient
      (TraceCorQHom.neg hom) =
      TraceCorQQuotient.neg
        (TraceCorQHom.ambient hom) :=
  TraceCorQHom.ambient_smul (-1) hom

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Add.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Neg.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Sub.Owner

/-!
# Subtraction of typed trace-correspondence hom classes

This file owns subtraction in each fixed-endpoint typed hom quotient as the
derived operation `left + neg right`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Subtraction of typed hom classes. -/
def TraceCorQHom.sub
    {source target : TraceCorQObject}
    (left right : TraceCorQHom source target) :
    TraceCorQHom source target :=
  TraceCorQHom.add left (TraceCorQHom.neg right)

/-- Typed hom subtraction unfolds to addition of the negative. -/
theorem TraceCorQHom.sub_eq_add_neg
    {source target : TraceCorQObject}
    (left right : TraceCorQHom source target) :
    TraceCorQHom.sub left right =
      TraceCorQHom.add left (TraceCorQHom.neg right) :=
  rfl

/-- The ambient map sends typed subtraction to quotient subtraction. -/
theorem TraceCorQHom.ambient_sub
    {source target : TraceCorQObject}
    (left right : TraceCorQHom source target) :
    TraceCorQHom.ambient
      (TraceCorQHom.sub left right) =
      TraceCorQQuotient.sub
        (TraceCorQHom.ambient left)
        (TraceCorQHom.ambient right) :=
  Eq.trans
    (TraceCorQHom.ambient_add left (TraceCorQHom.neg right))
    (Eq.trans
      (congrArg
        (TraceCorQQuotient.add (TraceCorQHom.ambient left))
        (TraceCorQHom.ambient_neg right))
      (Eq.symm
        (TraceCorQQuotient.sub_eq_add_neg
          (TraceCorQHom.ambient left)
          (TraceCorQHom.ambient right))))

end AnalyticMotives
end LFunctions
end Boundary

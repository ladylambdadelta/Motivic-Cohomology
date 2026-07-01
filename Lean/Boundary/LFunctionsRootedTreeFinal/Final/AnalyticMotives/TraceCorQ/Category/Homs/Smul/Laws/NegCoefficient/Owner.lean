import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Smul.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Smul.Laws.NegCoefficient.Owner

/-!
# Negative scalar coefficient laws for typed homs

This file lifts quotient negation in the scalar coefficient to fixed-endpoint
typed hom classes through the ambient quotient map.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Negating the scalar coefficient negates the scaled typed hom. -/
theorem TraceCorQHom.neg_smul
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (hom : TraceCorQHom source target) :
    TraceCorQHom.smul
      (-coefficient)
      hom =
      TraceCorQHom.neg
        (TraceCorQHom.smul coefficient hom) :=
  TraceCorQHom.eq_of_ambient_eq
    (Eq.trans
      (TraceCorQHom.ambient_smul (-coefficient) hom)
      (Eq.trans
        (TraceCorQQuotient.neg_smul
          coefficient
          (TraceCorQHom.ambient hom))
        (Eq.symm
          (Eq.trans
            (TraceCorQHom.ambient_neg
              (TraceCorQHom.smul coefficient hom))
            (congrArg
              TraceCorQQuotient.neg
              (TraceCorQHom.ambient_smul coefficient hom))))))

end AnalyticMotives
end LFunctions
end Boundary

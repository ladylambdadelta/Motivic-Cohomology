import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Smul.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Smul.Laws.ZeroCoefficient.Owner

/-!
# Zero-coefficient scalar laws for typed homs

This file lifts quotient zero-scalar normalization to fixed-endpoint typed hom
classes through the ambient quotient map.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Scaling any typed hom class by zero gives the zero typed hom. -/
theorem TraceCorQHom.zero_smul
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.smul 0 hom =
      TraceCorQHom.zero source target :=
  TraceCorQHom.eq_of_ambient_eq
    (Eq.trans
      (TraceCorQHom.ambient_smul 0 hom)
      (Eq.trans
        (TraceCorQQuotient.zero_smul
          (TraceCorQHom.ambient hom))
        (Eq.symm
          (TraceCorQHom.ambient_zero source target))))

end AnalyticMotives
end LFunctions
end Boundary

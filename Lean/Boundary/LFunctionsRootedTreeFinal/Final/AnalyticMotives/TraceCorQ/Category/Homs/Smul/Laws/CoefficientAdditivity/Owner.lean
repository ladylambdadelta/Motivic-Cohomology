import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Smul.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Smul.Laws.CoefficientAdditivity.Owner

/-!
# Scalar-coefficient additivity for typed homs

This file lifts quotient scalar-coefficient additivity to fixed-endpoint typed
hom classes through the ambient quotient map.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Scalar multiplication of typed homs is additive in the scalar coefficient. -/
theorem TraceCorQHom.add_smul
    {source target : TraceCorQObject}
    (leftCoefficient rightCoefficient : Rat)
    (hom : TraceCorQHom source target) :
    TraceCorQHom.smul
      (leftCoefficient + rightCoefficient)
      hom =
      TraceCorQHom.add
        (TraceCorQHom.smul leftCoefficient hom)
        (TraceCorQHom.smul rightCoefficient hom) :=
  TraceCorQHom.eq_of_ambient_eq
    (Eq.trans
      (TraceCorQHom.ambient_smul
        (leftCoefficient + rightCoefficient)
        hom)
      (Eq.trans
        (TraceCorQQuotient.add_smul
          leftCoefficient
          rightCoefficient
          (TraceCorQHom.ambient hom))
        (Eq.symm
          (Eq.trans
            (TraceCorQHom.ambient_add
              (TraceCorQHom.smul leftCoefficient hom)
              (TraceCorQHom.smul rightCoefficient hom))
            (Eq.trans
              (congrArg
                (fun leftClass =>
                  TraceCorQQuotient.add
                    leftClass
                    (TraceCorQHom.ambient
                      (TraceCorQHom.smul rightCoefficient hom)))
                (TraceCorQHom.ambient_smul leftCoefficient hom))
              (congrArg
                (fun rightClass =>
                  TraceCorQQuotient.add
                    (TraceCorQQuotient.smul
                      leftCoefficient
                      (TraceCorQHom.ambient hom))
                    rightClass)
                (TraceCorQHom.ambient_smul rightCoefficient hom)))))))

end AnalyticMotives
end LFunctions
end Boundary

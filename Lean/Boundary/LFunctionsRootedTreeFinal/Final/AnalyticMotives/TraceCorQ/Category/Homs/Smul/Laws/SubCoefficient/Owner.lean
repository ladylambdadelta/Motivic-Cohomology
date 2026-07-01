import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Sub.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Smul.Laws.CoefficientAdditivity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Smul.Laws.NegCoefficient.Owner

/-!
# Subtraction in scalar coefficients for typed homs

This file owns subtraction in the scalar coefficient for fixed-endpoint typed
hom classes.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Scalar multiplication of typed homs is subtractive in the scalar coefficient. -/
theorem TraceCorQHom.sub_smul
    {source target : TraceCorQObject}
    (leftCoefficient rightCoefficient : Rat)
    (hom : TraceCorQHom source target) :
    TraceCorQHom.smul
      (leftCoefficient - rightCoefficient)
      hom =
      TraceCorQHom.sub
        (TraceCorQHom.smul leftCoefficient hom)
        (TraceCorQHom.smul rightCoefficient hom) :=
  Eq.trans
    (congrArg
      (fun coefficient =>
        TraceCorQHom.smul coefficient hom)
      (sub_eq_add_neg leftCoefficient rightCoefficient))
    (Eq.trans
      (TraceCorQHom.add_smul
        leftCoefficient
        (-rightCoefficient)
        hom)
      (Eq.trans
        (congrArg
          (TraceCorQHom.add
            (TraceCorQHom.smul leftCoefficient hom))
          (TraceCorQHom.neg_smul
            rightCoefficient
            hom))
        (Eq.symm
          (TraceCorQHom.sub_eq_add_neg
            (TraceCorQHom.smul leftCoefficient hom)
            (TraceCorQHom.smul rightCoefficient hom)))))

end AnalyticMotives
end LFunctions
end Boundary

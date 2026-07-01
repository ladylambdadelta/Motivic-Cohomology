import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Add.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Neg.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Smul.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Smul.Laws.Owner

/-!
# Scalar laws for typed trace-correspondence hom classes

This file proves the typed hom scalar laws by reflecting the already-proved
ambient quotient scalar laws back through the fixed-endpoint hom quotient.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Scaling the zero typed hom gives the zero typed hom. -/
theorem TraceCorQHom.smul_zero
    (source target : TraceCorQObject)
    (coefficient : Rat) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.zero source target) =
      TraceCorQHom.zero source target :=
  TraceCorQHom.eq_of_ambient_eq
    (Eq.trans
      (TraceCorQHom.ambient_smul
        coefficient
        (TraceCorQHom.zero source target))
      (Eq.trans
        (congrArg
          (TraceCorQQuotient.smul coefficient)
          (TraceCorQHom.ambient_zero source target))
        (Eq.trans
          (TraceCorQQuotient.smul_zero coefficient)
          (Eq.symm
            (TraceCorQHom.ambient_zero source target)))))

/-- Scalar multiplication distributes over typed hom addition. -/
theorem TraceCorQHom.smul_add
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (left right : TraceCorQHom source target) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.add left right) =
      TraceCorQHom.add
        (TraceCorQHom.smul coefficient left)
        (TraceCorQHom.smul coefficient right) :=
  TraceCorQHom.eq_of_ambient_eq
    (Eq.trans
      (TraceCorQHom.ambient_smul
        coefficient
        (TraceCorQHom.add left right))
      (Eq.trans
        (congrArg
          (TraceCorQQuotient.smul coefficient)
          (TraceCorQHom.ambient_add left right))
        (Eq.trans
          (TraceCorQQuotient.smul_add
            coefficient
            (TraceCorQHom.ambient left)
            (TraceCorQHom.ambient right))
          (Eq.symm
            (Eq.trans
              (TraceCorQHom.ambient_add
                (TraceCorQHom.smul coefficient left)
                (TraceCorQHom.smul coefficient right))
              (Eq.trans
                (congrArg
                  (fun leftClass =>
                    TraceCorQQuotient.add
                      leftClass
                      (TraceCorQHom.ambient
                        (TraceCorQHom.smul coefficient right)))
                  (TraceCorQHom.ambient_smul coefficient left))
                (congrArg
                  (fun rightClass =>
                    TraceCorQQuotient.add
                      (TraceCorQQuotient.smul
                        coefficient
                        (TraceCorQHom.ambient left))
                      rightClass)
                  (TraceCorQHom.ambient_smul coefficient right))))))))

/-- Scaling a typed hom by one leaves it unchanged. -/
theorem TraceCorQHom.one_smul
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.smul 1 hom =
      hom :=
  TraceCorQHom.eq_of_ambient_eq
    (Eq.trans
      (TraceCorQHom.ambient_smul 1 hom)
      (TraceCorQQuotient.one_smul (TraceCorQHom.ambient hom)))

/-- Successive scalar multiplications compose by multiplying scalars. -/
theorem TraceCorQHom.smul_smul
    {source target : TraceCorQObject}
    (leftCoefficient rightCoefficient : Rat)
    (hom : TraceCorQHom source target) :
    TraceCorQHom.smul
      leftCoefficient
      (TraceCorQHom.smul rightCoefficient hom) =
      TraceCorQHom.smul
        (leftCoefficient * rightCoefficient)
        hom :=
  TraceCorQHom.eq_of_ambient_eq
    (Eq.trans
      (TraceCorQHom.ambient_smul
        leftCoefficient
        (TraceCorQHom.smul rightCoefficient hom))
      (Eq.trans
        (congrArg
          (TraceCorQQuotient.smul leftCoefficient)
          (TraceCorQHom.ambient_smul rightCoefficient hom))
        (Eq.trans
          (TraceCorQQuotient.smul_smul
            leftCoefficient
            rightCoefficient
            (TraceCorQHom.ambient hom))
          (Eq.symm
            (TraceCorQHom.ambient_smul
              (leftCoefficient * rightCoefficient)
              hom)))))

/-- Scalar multiplication commutes with typed hom negation. -/
theorem TraceCorQHom.smul_neg
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (hom : TraceCorQHom source target) :
    TraceCorQHom.smul coefficient (TraceCorQHom.neg hom) =
      TraceCorQHom.neg (TraceCorQHom.smul coefficient hom) :=
  TraceCorQHom.eq_of_ambient_eq
    (Eq.trans
      (TraceCorQHom.ambient_smul
        coefficient
        (TraceCorQHom.neg hom))
      (Eq.trans
        (congrArg
          (TraceCorQQuotient.smul coefficient)
          (TraceCorQHom.ambient_neg hom))
        (Eq.trans
          (TraceCorQQuotient.smul_neg
            coefficient
            (TraceCorQHom.ambient hom))
          (Eq.symm
            (Eq.trans
              (TraceCorQHom.ambient_neg
                (TraceCorQHom.smul coefficient hom))
              (congrArg
                TraceCorQQuotient.neg
                (TraceCorQHom.ambient_smul coefficient hom)))))))

end AnalyticMotives
end LFunctions
end Boundary

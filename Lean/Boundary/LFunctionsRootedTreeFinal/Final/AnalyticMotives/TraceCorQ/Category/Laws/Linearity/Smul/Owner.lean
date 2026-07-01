import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Composition.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Neg.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Smul.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.Laws.Owner

/-!
# Scalar linearity of typed trace-correspondence composition

This file proves that scaling either typed input to composition scales the
composite.  The proofs reflect the ambient quotient scalar-composition laws
back to the fixed-endpoint typed hom quotients.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Scaling the left typed hom scales typed composition. -/
theorem TraceCorQHom.smul_comp
    {source middle target : TraceCorQObject}
    (coefficient : Rat)
    (left : TraceCorQHom source middle)
    (right : TraceCorQHom middle target) :
    TraceCorQHom.comp
      (TraceCorQHom.smul coefficient left)
      right =
      TraceCorQHom.smul
        coefficient
        (TraceCorQHom.comp left right) :=
  TraceCorQHom.eq_of_ambient_eq
    (Eq.trans
      (TraceCorQHom.ambient_comp
        (TraceCorQHom.smul coefficient left)
        right)
      (Eq.trans
        (congrArg
          (fun leftClass =>
            TraceCorQQuotient.comp
              leftClass
              (TraceCorQHom.ambient right))
          (TraceCorQHom.ambient_smul coefficient left))
        (Eq.trans
          (TraceCorQQuotient.smul_comp
            coefficient
            (TraceCorQHom.ambient left)
            (TraceCorQHom.ambient right))
          (Eq.symm
            (Eq.trans
              (TraceCorQHom.ambient_smul
                coefficient
                (TraceCorQHom.comp left right))
              (congrArg
                (TraceCorQQuotient.smul coefficient)
                (TraceCorQHom.ambient_comp left right)))))))

/-- Scaling the right typed hom scales typed composition. -/
theorem TraceCorQHom.comp_smul
    {source middle target : TraceCorQObject}
    (coefficient : Rat)
    (left : TraceCorQHom source middle)
    (right : TraceCorQHom middle target) :
    TraceCorQHom.comp
      left
      (TraceCorQHom.smul coefficient right) =
      TraceCorQHom.smul
        coefficient
        (TraceCorQHom.comp left right) :=
  TraceCorQHom.eq_of_ambient_eq
    (Eq.trans
      (TraceCorQHom.ambient_comp
        left
        (TraceCorQHom.smul coefficient right))
      (Eq.trans
        (congrArg
          (fun rightClass =>
            TraceCorQQuotient.comp
              (TraceCorQHom.ambient left)
              rightClass)
          (TraceCorQHom.ambient_smul coefficient right))
        (Eq.trans
          (TraceCorQQuotient.comp_smul
            coefficient
            (TraceCorQHom.ambient left)
            (TraceCorQHom.ambient right))
          (Eq.symm
            (Eq.trans
              (TraceCorQHom.ambient_smul
                coefficient
                (TraceCorQHom.comp left right))
              (congrArg
                (TraceCorQQuotient.smul coefficient)
                (TraceCorQHom.ambient_comp left right)))))))

/-- Scaling both typed inputs scales typed composition by the product scalar. -/
theorem TraceCorQHom.smul_comp_smul
    {source middle target : TraceCorQObject}
    (leftCoefficient rightCoefficient : Rat)
    (left : TraceCorQHom source middle)
    (right : TraceCorQHom middle target) :
    TraceCorQHom.comp
      (TraceCorQHom.smul leftCoefficient left)
      (TraceCorQHom.smul rightCoefficient right) =
      TraceCorQHom.smul
        (leftCoefficient * rightCoefficient)
        (TraceCorQHom.comp left right) :=
  Eq.trans
    (TraceCorQHom.smul_comp
      leftCoefficient
      left
      (TraceCorQHom.smul rightCoefficient right))
    (Eq.trans
      (congrArg
        (TraceCorQHom.smul leftCoefficient)
        (TraceCorQHom.comp_smul rightCoefficient left right))
      (TraceCorQHom.smul_smul
        leftCoefficient
        rightCoefficient
        (TraceCorQHom.comp left right)))

/-- Negating the left typed hom negates typed composition. -/
theorem TraceCorQHom.neg_comp
    {source middle target : TraceCorQObject}
    (left : TraceCorQHom source middle)
    (right : TraceCorQHom middle target) :
    TraceCorQHom.comp
      (TraceCorQHom.neg left)
      right =
      TraceCorQHom.neg
        (TraceCorQHom.comp left right) :=
  TraceCorQHom.smul_comp (-1) left right

/-- Negating the right typed hom negates typed composition. -/
theorem TraceCorQHom.comp_neg
    {source middle target : TraceCorQObject}
    (left : TraceCorQHom source middle)
    (right : TraceCorQHom middle target) :
    TraceCorQHom.comp
      left
      (TraceCorQHom.neg right) =
      TraceCorQHom.neg
        (TraceCorQHom.comp left right) :=
  TraceCorQHom.comp_smul (-1) left right

/-- Negating both typed inputs leaves typed composition unchanged. -/
theorem TraceCorQHom.neg_comp_neg
    {source middle target : TraceCorQObject}
    (left : TraceCorQHom source middle)
    (right : TraceCorQHom middle target) :
    TraceCorQHom.comp
      (TraceCorQHom.neg left)
      (TraceCorQHom.neg right) =
      TraceCorQHom.comp left right :=
  Eq.trans
    (TraceCorQHom.smul_comp_smul (-1) (-1) left right)
    (Eq.trans
      (congrArg
        (fun coefficient =>
          TraceCorQHom.smul coefficient (TraceCorQHom.comp left right))
        (Eq.trans
          (neg_mul_neg 1 1)
          (one_mul 1)))
      (TraceCorQHom.one_smul (TraceCorQHom.comp left right)))

end AnalyticMotives
end LFunctions
end Boundary

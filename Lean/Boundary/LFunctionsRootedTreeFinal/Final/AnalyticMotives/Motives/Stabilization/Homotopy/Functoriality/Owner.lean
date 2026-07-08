import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Homotopy.Owner

/-!
# Functoriality of the analytic trace homotopy quotient

This file records the identity and composition laws for the quotient functor
from analytic trace cochain complexes to the analytic trace homotopy category.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The homotopy quotient sends identity cochain maps to identity morphisms. -/
theorem TraceAnalyticHomotopyCategory.mapOf_id
    (complex : TraceAnalyticCochainComplex) :
    TraceAnalyticHomotopyCategory.mapOf
      (𝟙 complex : TraceAnalyticCochainComplex.Hom complex complex) =
      𝟙 (TraceAnalyticHomotopyCategory.objectOf complex) :=
  Eq.trans
    (TraceAnalyticHomotopyCategory.mapOf_eq
      (𝟙 complex : TraceAnalyticCochainComplex.Hom complex complex))
    (TraceAnalyticHomotopyCategory.quotientFunctor.map_id complex)

/-- The homotopy quotient sends composite cochain maps to composite morphisms. -/
theorem TraceAnalyticHomotopyCategory.mapOf_comp
    {first second third : TraceAnalyticCochainComplex}
    (left : TraceAnalyticCochainComplex.Hom first second)
    (right : TraceAnalyticCochainComplex.Hom second third) :
    TraceAnalyticHomotopyCategory.mapOf (left ≫ right) =
      TraceAnalyticHomotopyCategory.mapOf left ≫
        TraceAnalyticHomotopyCategory.mapOf right :=
  Eq.trans
    (TraceAnalyticHomotopyCategory.mapOf_eq (left ≫ right))
    (Eq.trans
      (TraceAnalyticHomotopyCategory.quotientFunctor.map_comp left right)
      (congrArg₂
        (fun head tail => head ≫ tail)
        (Eq.symm
          (TraceAnalyticHomotopyCategory.mapOf_eq left))
        (Eq.symm
          (TraceAnalyticHomotopyCategory.mapOf_eq right))))

end AnalyticMotives
end LFunctions
end Boundary

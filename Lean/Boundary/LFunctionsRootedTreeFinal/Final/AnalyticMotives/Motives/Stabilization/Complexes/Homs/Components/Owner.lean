import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Complexes.Homs.Owner

/-!
# Component formulas for analytic trace complex morphisms

This file records how identity and composition of analytic trace cochain maps
act in each integer degree.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The identity analytic trace cochain map has identity trace components. -/
theorem TraceAnalyticCochainComplex.Hom.component_id
    (complex : TraceAnalyticCochainComplex)
    (degree : ℤ) :
    (𝟙 complex : TraceAnalyticCochainComplex.Hom complex complex).component degree =
      𝟙 (complex.objectAt degree) :=
  Eq.trans
    (TraceAnalyticCochainComplex.Hom.component_eq
      (𝟙 complex : TraceAnalyticCochainComplex.Hom complex complex)
      degree)
    (HomologicalComplex.id_f complex degree)

/-- Composition of analytic trace cochain maps is componentwise composition. -/
theorem TraceAnalyticCochainComplex.Hom.component_comp
    {first second third : TraceAnalyticCochainComplex}
    (left : TraceAnalyticCochainComplex.Hom first second)
    (right : TraceAnalyticCochainComplex.Hom second third)
    (degree : ℤ) :
    (left ≫ right).component degree =
      left.component degree ≫ right.component degree :=
  Eq.trans
    (TraceAnalyticCochainComplex.Hom.component_eq
      (left ≫ right)
      degree)
    (Eq.trans
      (HomologicalComplex.comp_f left right degree)
      (congrArg₂
        (fun head tail => head ≫ tail)
        (Eq.symm
          (TraceAnalyticCochainComplex.Hom.component_eq left degree))
        (Eq.symm
          (TraceAnalyticCochainComplex.Hom.component_eq right degree))))

end AnalyticMotives
end LFunctions
end Boundary

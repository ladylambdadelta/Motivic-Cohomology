import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Category.Owner

/-!
# Motive-root compact-geometric category facade

This file exposes compact-generator category and Q-linear trace-hom laws under
the `TraceAnalyticMotive` root facade.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Compact geometric analytic generators carry representable trace presheaves. -/
theorem TraceAnalyticMotive.compactGenerator_presheaf
    (generator : TraceAnalyticGeometricGenerator) :
    generator.presheaf =
      TraceCorQPresheaf.representable generator.traceObject :=
  TraceAnalyticCompactGeometric.generator_presheaf
    generator

/-- Compact-geometric root aggregate: categorical identity is trace identity. -/
theorem TraceAnalyticMotive.compactGenerator_root_category_id_traceHom
    (generator : TraceAnalyticGeometricGenerator) :
    (𝟙 generator : generator ⟶ generator).traceHom =
      𝟙 generator.traceObject :=
  TraceAnalyticMotive.compactGenerator_id_traceHom
    generator

/-- Compact-geometric root aggregate: categorical composition is trace composition. -/
theorem TraceAnalyticMotive.compactGenerator_root_category_comp_traceHom
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    (left ≫ right).traceHom =
      left.traceHom ≫ right.traceHom :=
  TraceAnalyticMotive.compactGenerator_comp_traceHom
    left
    right

/-- Compact-geometric root aggregate: zero morphisms are zero trace homs. -/
theorem TraceAnalyticMotive.compactGenerator_root_category_zero_traceHom
    {source target : TraceAnalyticGeometricGenerator} :
    (0 : source ⟶ target).traceHom =
      (0 : source.traceObject ⟶ target.traceObject) :=
  TraceAnalyticMotive.compactGenerator_category_zero_traceHom

/-- Compact-geometric root aggregate: addition is addition of trace homs. -/
theorem TraceAnalyticMotive.compactGenerator_root_category_add_traceHom
    {source target : TraceAnalyticGeometricGenerator}
    (left right : source ⟶ target) :
    (left + right).traceHom =
      left.traceHom + right.traceHom :=
  TraceAnalyticMotive.compactGenerator_category_add_traceHom
    left
    right

/-- Compact-geometric root aggregate: rational scalar multiplication is inherited from trace homs. -/
theorem TraceAnalyticMotive.compactGenerator_root_category_smul_traceHom
    {source target : TraceAnalyticGeometricGenerator}
    (coefficient : Rat)
    (morphism : source ⟶ target) :
    (coefficient • morphism).traceHom =
      coefficient • morphism.traceHom :=
  TraceAnalyticMotive.compactGenerator_category_smul_traceHom
    coefficient
    morphism

/-- Compact-geometric root aggregate: explicit trace negation is inherited from trace homs. -/
theorem TraceAnalyticMotive.compactGenerator_root_category_traceNeg_traceHom
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    (TraceCorQHom.neg morphism).traceHom =
      TraceCorQHom.neg morphism.traceHom :=
  TraceAnalyticMotive.compactGenerator_traceNeg_traceHom
    morphism

/-- Compact-geometric root aggregate: explicit trace subtraction is inherited from trace homs. -/
theorem TraceAnalyticMotive.compactGenerator_root_category_traceSub_traceHom
    {source target : TraceAnalyticGeometricGenerator}
    (left right : source ⟶ target) :
    (TraceCorQHom.sub left right).traceHom =
      TraceCorQHom.sub left.traceHom right.traceHom :=
  TraceAnalyticMotive.compactGenerator_traceSub_traceHom
    left
    right

/-- Compact-geometric root aggregate: explicit trace subtraction from itself is zero. -/
theorem TraceAnalyticMotive.compactGenerator_root_category_traceSub_self_traceHom
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceCorQHom.sub morphism morphism =
      TraceCorQHom.zero source.traceObject target.traceObject :=
  TraceAnalyticMotive.compactGenerator_traceSub_self_traceHom
    morphism

/-- Compact-geometric root aggregate: explicit trace subtraction detects equality. -/
theorem TraceAnalyticMotive.compactGenerator_root_category_eq_of_traceSub_eq_zero
    {source target : TraceAnalyticGeometricGenerator}
    (left right : source ⟶ target)
    (left_sub_right_eq_zero :
      TraceCorQHom.sub left right =
        TraceCorQHom.zero source.traceObject target.traceObject) :
    left = right :=
  TraceAnalyticMotive.compactGenerator_eq_of_traceSub_eq_zero
    left
    right
    left_sub_right_eq_zero

/-- Compact-geometric root aggregate: scalar multiplication distributes over trace subtraction. -/
theorem TraceAnalyticMotive.compactGenerator_root_category_traceSmul_sub
    {source target : TraceAnalyticGeometricGenerator}
    (coefficient : Rat)
    (left right : source ⟶ target) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.sub left right) =
      TraceCorQHom.sub
        (TraceCorQHom.smul coefficient left)
        (TraceCorQHom.smul coefficient right) :=
  TraceAnalyticMotive.compactGenerator_traceSmul_sub
    coefficient
    left
    right

end AnalyticMotives
end LFunctions
end Boundary

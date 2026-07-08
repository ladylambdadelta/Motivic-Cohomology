import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Category.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Category.Linear.Owner

/-!
# Motive-root compact-generator category wrappers

This file mirrors the concrete category laws for compact geometric analytic
generators under `TraceAnalyticMotive`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root compact-generator category identity is trace identity. -/
theorem TraceAnalyticMotive.compactGenerator_category_id_eq_trace_id
    (generator : TraceAnalyticGeometricGenerator) :
    𝟙 generator =
      𝟙 generator.traceObject :=
  TraceAnalyticGeometricGenerator.category_id_eq_trace_id
    generator

/-- Motive-root compact-generator category composition is trace composition. -/
theorem TraceAnalyticMotive.compactGenerator_category_comp_eq_trace_comp
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    left ≫ right =
      left.traceHom ≫ right.traceHom :=
  TraceAnalyticGeometricGenerator.category_comp_eq_trace_comp
    left
    right

/-- Motive-root trace hom of categorical identity is trace identity. -/
theorem TraceAnalyticMotive.compactGenerator_id_traceHom
    (generator : TraceAnalyticGeometricGenerator) :
    (𝟙 generator : generator ⟶ generator).traceHom =
      𝟙 generator.traceObject :=
  TraceAnalyticGeometricGenerator.id_traceHom
    generator

/-- Motive-root trace hom of categorical composite is trace composite. -/
theorem TraceAnalyticMotive.compactGenerator_comp_traceHom
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    (left ≫ right).traceHom =
      left.traceHom ≫ right.traceHom :=
  TraceAnalyticGeometricGenerator.comp_traceHom
    left
    right

/-- Motive-root representable map of identity is identity. -/
theorem TraceAnalyticMotive.compactGenerator_id_representableMap
    (generator : TraceAnalyticGeometricGenerator) :
    (𝟙 generator : generator ⟶ generator).representableMap =
      𝟙 generator.presheaf :=
  TraceAnalyticGeometricGenerator.id_representableMap
    generator

/-- Motive-root representable maps preserve composition. -/
theorem TraceAnalyticMotive.compactGenerator_comp_representableMap
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    (left ≫ right).representableMap =
      left.representableMap ≫ right.representableMap :=
  TraceAnalyticGeometricGenerator.comp_representableMap
    left
    right

/-- Motive-root category aggregate: zero morphisms are zero trace homs. -/
theorem TraceAnalyticMotive.compactGenerator_category_zero_traceHom
    {source target : TraceAnalyticGeometricGenerator} :
    (0 : source ⟶ target).traceHom =
      (0 : source.traceObject ⟶ target.traceObject) :=
  TraceAnalyticMotive.compactGenerator_zero_traceHom

/-- Motive-root category aggregate: addition is addition of trace homs. -/
theorem TraceAnalyticMotive.compactGenerator_category_add_traceHom
    {source target : TraceAnalyticGeometricGenerator}
    (left right : source ⟶ target) :
    (left + right).traceHom =
      left.traceHom + right.traceHom :=
  TraceAnalyticMotive.compactGenerator_add_traceHom
    left
    right

/-- Motive-root category aggregate: rational scalar multiplication is inherited from trace homs. -/
theorem TraceAnalyticMotive.compactGenerator_category_smul_traceHom
    {source target : TraceAnalyticGeometricGenerator}
    (coefficient : Rat)
    (morphism : source ⟶ target) :
    (coefficient • morphism).traceHom =
      coefficient • morphism.traceHom :=
  TraceAnalyticMotive.compactGenerator_smul_traceHom
    coefficient
    morphism

end AnalyticMotives
end LFunctions
end Boundary

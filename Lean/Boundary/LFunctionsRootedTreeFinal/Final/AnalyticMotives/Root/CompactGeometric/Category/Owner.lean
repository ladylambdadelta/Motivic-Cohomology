import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Category.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Category.Linear.Owner

/-!
# Top-root compact-generator category wrappers

This file mirrors motive-root concrete category laws for compact geometric
analytic generators under `AnalyticMotivesRoot`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root compact-generator category identity is trace identity. -/
theorem AnalyticMotivesRoot.compactGenerator_category_id_eq_trace_id
    (generator : TraceAnalyticGeometricGenerator) :
    𝟙 generator =
      𝟙 generator.traceObject :=
  TraceAnalyticMotive.compactGenerator_category_id_eq_trace_id
    generator

/-- Top-root compact-generator category composition is trace composition. -/
theorem AnalyticMotivesRoot.compactGenerator_category_comp_eq_trace_comp
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    left ≫ right =
      left.traceHom ≫ right.traceHom :=
  TraceAnalyticMotive.compactGenerator_category_comp_eq_trace_comp
    left
    right

/-- Top-root trace hom of categorical identity is trace identity. -/
theorem AnalyticMotivesRoot.compactGenerator_id_traceHom
    (generator : TraceAnalyticGeometricGenerator) :
    (𝟙 generator : generator ⟶ generator).traceHom =
      𝟙 generator.traceObject :=
  TraceAnalyticMotive.compactGenerator_id_traceHom
    generator

/-- Top-root trace hom of categorical composite is trace composite. -/
theorem AnalyticMotivesRoot.compactGenerator_comp_traceHom
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    (left ≫ right).traceHom =
      left.traceHom ≫ right.traceHom :=
  TraceAnalyticMotive.compactGenerator_comp_traceHom
    left
    right

/-- Top-root representable map of identity is identity. -/
theorem AnalyticMotivesRoot.compactGenerator_id_representableMap
    (generator : TraceAnalyticGeometricGenerator) :
    (𝟙 generator : generator ⟶ generator).representableMap =
      𝟙 generator.presheaf :=
  TraceAnalyticMotive.compactGenerator_id_representableMap
    generator

/-- Top-root representable maps preserve composition. -/
theorem AnalyticMotivesRoot.compactGenerator_comp_representableMap
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    (left ≫ right).representableMap =
      left.representableMap ≫ right.representableMap :=
  TraceAnalyticMotive.compactGenerator_comp_representableMap
    left
    right

/-- Top-root category aggregate: zero morphisms are zero trace homs. -/
theorem AnalyticMotivesRoot.compactGenerator_category_zero_traceHom
    {source target : TraceAnalyticGeometricGenerator} :
    (0 : source ⟶ target).traceHom =
      (0 : source.traceObject ⟶ target.traceObject) :=
  TraceAnalyticMotive.compactGenerator_category_zero_traceHom

/-- Top-root category aggregate: addition is addition of trace homs. -/
theorem AnalyticMotivesRoot.compactGenerator_category_add_traceHom
    {source target : TraceAnalyticGeometricGenerator}
    (left right : source ⟶ target) :
    (left + right).traceHom =
      left.traceHom + right.traceHom :=
  TraceAnalyticMotive.compactGenerator_category_add_traceHom
    left
    right

/-- Top-root category aggregate: rational scalar multiplication is inherited from trace homs. -/
theorem AnalyticMotivesRoot.compactGenerator_category_smul_traceHom
    {source target : TraceAnalyticGeometricGenerator}
    (coefficient : Rat)
    (morphism : source ⟶ target) :
    (coefficient • morphism).traceHom =
      coefficient • morphism.traceHom :=
  TraceAnalyticMotive.compactGenerator_category_smul_traceHom
    coefficient
    morphism

end AnalyticMotives
end LFunctions
end Boundary

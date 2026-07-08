import Mathlib.CategoryTheory.Category.Basic
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Morphisms.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Associativity.Typed.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Identity.Typed.Owner

/-!
# Category of compact geometric analytic generators

This file packages compact analytic generators and their trace-correspondence
morphisms as a category.  The laws are inherited from the already constructed
`TraceCorQ` category on the underlying certified trace objects.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open scoped CategoryTheory

/-- Compact geometric analytic generators form the trace-correspondence category restricted to
certified generator objects. -/
instance traceAnalyticGeometricGeneratorCategory :
    CategoryTheory.Category TraceAnalyticGeometricGenerator where
  Hom := TraceAnalyticGeometricGenerator.Hom
  id := TraceAnalyticGeometricGenerator.id
  comp := fun left right =>
    TraceAnalyticGeometricGenerator.comp left right
  id_comp := fun hom =>
    TraceCorQHom.left_id hom
  comp_id := fun hom =>
    TraceCorQHom.right_id hom
  assoc := fun left middle right =>
    TraceCorQHom.comp_assoc left middle right

/-- Category identity on a compact generator is the underlying trace identity. -/
theorem TraceAnalyticGeometricGenerator.category_id_eq_trace_id
    (generator : TraceAnalyticGeometricGenerator) :
    𝟙 generator =
      𝟙 generator.traceObject :=
  rfl

/-- Category composition on compact generators is underlying trace composition. -/
theorem TraceAnalyticGeometricGenerator.category_comp_eq_trace_comp
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    left ≫ right =
      left.traceHom ≫ right.traceHom :=
  rfl

/-- The trace hom of a categorical identity is the trace identity. -/
theorem TraceAnalyticGeometricGenerator.id_traceHom
    (generator : TraceAnalyticGeometricGenerator) :
    (𝟙 generator : generator ⟶ generator).traceHom =
      𝟙 generator.traceObject :=
  rfl

/-- The trace hom of a categorical composite is the composite of trace homs. -/
theorem TraceAnalyticGeometricGenerator.comp_traceHom
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    (left ≫ right).traceHom =
      left.traceHom ≫ right.traceHom :=
  rfl

/-- The representable map of an identity compact-generator morphism is identity. -/
theorem TraceAnalyticGeometricGenerator.id_representableMap
    (generator : TraceAnalyticGeometricGenerator) :
    (𝟙 generator : generator ⟶ generator).representableMap =
      𝟙 generator.presheaf :=
  TraceCorQPresheaf.representableMap_id generator.traceObject

/-- Representable maps preserve compact-generator composition. -/
theorem TraceAnalyticGeometricGenerator.comp_representableMap
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    (left ≫ right).representableMap =
      left.representableMap ≫ right.representableMap :=
  TraceCorQPresheaf.representableMap_comp left.traceHom right.traceHom

end AnalyticMotives
end LFunctions
end Boundary

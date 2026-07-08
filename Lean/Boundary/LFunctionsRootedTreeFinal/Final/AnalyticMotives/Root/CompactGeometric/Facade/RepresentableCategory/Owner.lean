import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Category.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Functors.Owner

/-!
# Top-root compact-geometric representable category facade
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic-motives root exposes compact geometric representable presheaves. -/
theorem AnalyticMotivesRoot.compactGenerator_presheaf
    (generator : TraceAnalyticGeometricGenerator) :
    generator.presheaf =
      TraceCorQPresheaf.representable generator.traceObject :=
  TraceAnalyticMotive.compactGenerator_presheaf
    generator

/-- The analytic-motives root exposes compact categorical identities as trace identities. -/
theorem AnalyticMotivesRoot.compactGenerator_root_category_id_traceHom
    (generator : TraceAnalyticGeometricGenerator) :
    (𝟙 generator : generator ⟶ generator).traceHom =
      𝟙 generator.traceObject :=
  TraceAnalyticMotive.compactGenerator_root_category_id_traceHom
    generator

/-- The analytic-motives root exposes compact categorical composition as trace composition. -/
theorem AnalyticMotivesRoot.compactGenerator_root_category_comp_traceHom
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    (left ≫ right).traceHom =
      left.traceHom ≫ right.traceHom :=
  TraceAnalyticMotive.compactGenerator_root_category_comp_traceHom
    left
    right

/-- The analytic-motives root exposes compact zero morphisms as zero trace homs. -/
theorem AnalyticMotivesRoot.compactGenerator_root_category_zero_traceHom
    {source target : TraceAnalyticGeometricGenerator} :
    (0 : source ⟶ target).traceHom =
      (0 : source.traceObject ⟶ target.traceObject) :=
  TraceAnalyticMotive.compactGenerator_root_category_zero_traceHom

/-- The analytic-motives root exposes compact morphism addition as addition of trace homs. -/
theorem AnalyticMotivesRoot.compactGenerator_root_category_add_traceHom
    {source target : TraceAnalyticGeometricGenerator}
    (left right : source ⟶ target) :
    (left + right).traceHom =
      left.traceHom + right.traceHom :=
  TraceAnalyticMotive.compactGenerator_root_category_add_traceHom
    left
    right

/-- The analytic-motives root exposes compact rational scalar multiplication through trace homs. -/
theorem AnalyticMotivesRoot.compactGenerator_root_category_smul_traceHom
    {source target : TraceAnalyticGeometricGenerator}
    (coefficient : Rat)
    (morphism : source ⟶ target) :
    (coefficient • morphism).traceHom =
      coefficient • morphism.traceHom :=
  TraceAnalyticMotive.compactGenerator_root_category_smul_traceHom
    coefficient
    morphism

end AnalyticMotives
end LFunctions
end Boundary

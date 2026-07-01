import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.BulkShadows.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.CompactGeometric.ContourCorQConstruction.Owner

/-!
# Algebraic shadows of constructed generators

This owner extracts algebraic shadow schemes from constructed compact
generators and generated thick closures.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace ConstructedCompactAnalyticGenerator

/-- The algebraic shadow scheme of a constructed compact generator. -/
def algebraicShadow (G : ConstructedCompactAnalyticGenerator) :
    ArithmeticBase :=
  G.source.algebraicShadow

/-- The algebraic shadow of a generator is the base of its source bulk. -/
theorem algebraicShadow_eq_source_base
    (G : ConstructedCompactAnalyticGenerator) :
    G.algebraicShadow = G.source.core.base :=
  rfl

end ConstructedCompactAnalyticGenerator

namespace ConstructedCompactAnalyticThickClosure

/-- The algebraic shadow scheme of one generator in a constructed thick closure. -/
def generatorAlgebraicShadow
    (C : ConstructedCompactAnalyticThickClosure)
    (i : C.GeneratorIndex) :
    ArithmeticBase :=
  (C.generatorAt i).algebraicShadow

/-- The algebraic shadow of a selected generator is its source-bulk base. -/
theorem generatorAlgebraicShadow_eq_source_base
    (C : ConstructedCompactAnalyticThickClosure)
    (i : C.GeneratorIndex) :
    C.generatorAlgebraicShadow i =
      (C.generatorSource i).core.base :=
  rfl

end ConstructedCompactAnalyticThickClosure

namespace ConstructedCompactGeometricAnalyticMotive

/-- The algebraic shadow scheme of one generator in a compact geometric motive. -/
def generatorAlgebraicShadow
    (M : ConstructedCompactGeometricAnalyticMotive)
    (i : M.thickClosure.GeneratorIndex) :
    ArithmeticBase :=
  M.thickClosure.generatorAlgebraicShadow i

/-- The algebraic shadow of a selected compact-geometric generator. -/
theorem generatorAlgebraicShadow_eq_source_base
    (M : ConstructedCompactGeometricAnalyticMotive)
    (i : M.thickClosure.GeneratorIndex) :
    M.generatorAlgebraicShadow i =
      (M.generatorSource i).core.base :=
  rfl

end ConstructedCompactGeometricAnalyticMotive

end AnalyticMotives
end LFunctions
end Boundary

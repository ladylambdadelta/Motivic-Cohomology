import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.GeneratorShadows.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.StableCategory.ContourCorQConstruction.Owner

/-!
# Algebraic shadows of constructed stable packages

This owner exposes the algebraic shadow schemes of the compact generators
inside a constructed stable analytic motive package.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace ConstructedStableAnalyticMotivePackage

/-- The compact-geometric layer of a constructed stable package. -/
def compactGeometricLayer
    (P : ConstructedStableAnalyticMotivePackage) :
    ConstructedCompactGeometricAnalyticMotive :=
  P.compactLayer.compactGeometric

/-- The algebraic shadow scheme of one compact generator in the stable package. -/
def generatorAlgebraicShadow
    (P : ConstructedStableAnalyticMotivePackage)
    (i : P.compactGeometricLayer.thickClosure.GeneratorIndex) :
    ArithmeticBase :=
  P.compactGeometricLayer.generatorAlgebraicShadow i

/-- The source bulk of one compact generator in the stable package. -/
def generatorSource
    (P : ConstructedStableAnalyticMotivePackage)
    (i : P.compactGeometricLayer.thickClosure.GeneratorIndex) :
    ContourAdmissibleBulk :=
  P.compactGeometricLayer.generatorSource i

/-- The generator algebraic shadow is the source bulk's arithmetic base. -/
theorem generatorAlgebraicShadow_eq_source_base
    (P : ConstructedStableAnalyticMotivePackage)
    (i : P.compactGeometricLayer.thickClosure.GeneratorIndex) :
    P.generatorAlgebraicShadow i =
      (P.generatorSource i).core.base :=
  rfl

end ConstructedStableAnalyticMotivePackage

end AnalyticMotives
end LFunctions
end Boundary

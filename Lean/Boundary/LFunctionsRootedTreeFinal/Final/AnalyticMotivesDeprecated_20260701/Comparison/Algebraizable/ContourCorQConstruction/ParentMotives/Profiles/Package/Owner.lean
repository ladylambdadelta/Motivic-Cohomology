import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.ParentMotives.StablePackages.Owner

/-!
# Parent comparison profiles for stable analytic motive packages

This file bundles a constructed stable analytic motive package with the
perfect ground and smooth algebraization data needed for parent-motive
comparison.
-/

universe u

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Comparison profile for one algebraizable stable analytic motive package. -/
structure ConstructedStableAnalyticMotiveParentProfile where
  ground : PerfectAnalyticGround.{u}
  package : ConstructedStableAnalyticMotivePackage
  algebraization :
    ConstructedStableAnalyticMotivePackageAlgebraization ground package

namespace ConstructedStableAnalyticMotiveParentProfile

/-- The constructed analytic package in a parent comparison profile. -/
def analyticPackage
    (P : ConstructedStableAnalyticMotiveParentProfile.{u}) :
    ConstructedStableAnalyticMotivePackage :=
  P.package

/-- The perfect analytic ground in a parent comparison profile. -/
def perfectGround
    (P : ConstructedStableAnalyticMotiveParentProfile.{u}) :
    PerfectAnalyticGround.{u} :=
  P.ground

/-- The package algebraization carried by a parent comparison profile. -/
def packageAlgebraization
    (P : ConstructedStableAnalyticMotiveParentProfile.{u}) :
    ConstructedStableAnalyticMotivePackageAlgebraization
      P.perfectGround P.analyticPackage :=
  P.algebraization

/-- The compact-geometric layer of the analytic package in the profile. -/
def compactGeometricLayer
    (P : ConstructedStableAnalyticMotiveParentProfile.{u}) :
    ConstructedCompactGeometricAnalyticMotive :=
  P.analyticPackage.compactGeometric

/-- The compact generator index type in the profile. -/
abbrev GeneratorIndex
    (P : ConstructedStableAnalyticMotiveParentProfile.{u}) :
    Type :=
  P.compactGeometricLayer.thick.GeneratorIndex

/-- The selected compact generator of the analytic package in the profile. -/
def generatorAt
    (P : ConstructedStableAnalyticMotiveParentProfile.{u})
    (i : P.GeneratorIndex) :
    ConstructedCompactAnalyticGenerator :=
  P.compactGeometricLayer.generatorAt i

/-- The selected algebraization of a compact generator in the profile. -/
def generatorAlgebraizationAt
    (P : ConstructedStableAnalyticMotiveParentProfile.{u})
    (i : P.GeneratorIndex) :
    ConstructedCompactAnalyticGeneratorAlgebraization
      P.perfectGround (P.generatorAt i) :=
  P.packageAlgebraization.at i

end ConstructedStableAnalyticMotiveParentProfile

end AnalyticMotives
end LFunctions
end Boundary

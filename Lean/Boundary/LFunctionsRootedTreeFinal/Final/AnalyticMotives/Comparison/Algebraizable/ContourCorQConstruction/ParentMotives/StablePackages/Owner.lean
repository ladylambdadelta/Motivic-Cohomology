import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.ParentMotives.CompactGeometric.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.StableShadows.Owner

/-!
# Algebraized stable analytic motive packages

This file records the algebraization data needed to compare the compact
generator family inside a constructed stable analytic motive package with the
parent `DMgm(Q)_Q` construction.
-/

universe u

open CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

noncomputable section

/-- Smooth algebraization evidence for the compact-geometric layer of a package. -/
structure ConstructedStableAnalyticMotivePackageAlgebraization
    (G : PerfectAnalyticGround)
    (P : ConstructedStableAnalyticMotivePackage) where
  compactGeometricAlgebraization :
    ConstructedCompactGeometricAnalyticMotiveAlgebraization G P.compactGeometricLayer

namespace ConstructedStableAnalyticMotivePackageAlgebraization

/-- The algebraization of the package's compact-geometric layer. -/
def compactGeometric {G : PerfectAnalyticGround}
    {P : ConstructedStableAnalyticMotivePackage}
    (A : ConstructedStableAnalyticMotivePackageAlgebraization G P) :
    ConstructedCompactGeometricAnalyticMotiveAlgebraization G P.compactGeometricLayer :=
  A.compactGeometricAlgebraization

/-- The algebraization selected for one compact generator in the package. -/
def at {G : PerfectAnalyticGround}
    {P : ConstructedStableAnalyticMotivePackage}
    (A : ConstructedStableAnalyticMotivePackageAlgebraization G P)
    (i : P.compactGeometricLayer.thick.GeneratorIndex) :
    ConstructedCompactAnalyticGeneratorAlgebraization G
      (P.compactGeometricLayer.generatorAt i) :=
  A.compactGeometric.at i

variable {G : PerfectAnalyticGround}
variable (composition : Boundary.CanonicalCompositionData (k := G.carrier))
variable [Abelian (LinearPST (Boundary.canonicalCategory composition))]
variable [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
variable [Abelian (canonicalA1NisLocalization composition)]
variable [HasDerivedCategory (canonicalA1NisLocalization composition)]
variable [(canonicalA1NisLocalizationFunctor composition).Additive]
variable [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
variable [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]

/-- Parent geometric effective image of one compact generator in the package. -/
def parentGeometricEffectiveMotiveAt
    {P : ConstructedStableAnalyticMotivePackage}
    (implementation :
      CanonicalA1NisLocalizationImplementation composition)
    (A : ConstructedStableAnalyticMotivePackageAlgebraization G P)
    (i : P.compactGeometricLayer.thick.GeneratorIndex) :
    canonicalGeometricEffectiveMotives composition implementation :=
  (A.at i).parentGeometricEffectiveMotive composition implementation

/-- Parent stable image of one compact generator in the package. -/
def parentStableMotiveAt
    {P : ConstructedStableAnalyticMotivePackage}
    (A : ConstructedStableAnalyticMotivePackageAlgebraization G P)
    (i : P.compactGeometricLayer.thick.GeneratorIndex) :
    VoevodskyDMgmQ_Q (composition := composition) :=
  (A.at i).parentStableMotive composition

/-- The parent geometric image is the image of the selected package generator. -/
theorem parentGeometricEffectiveMotiveAt_eq_at
    {P : ConstructedStableAnalyticMotivePackage}
    (implementation :
      CanonicalA1NisLocalizationImplementation composition)
    (A : ConstructedStableAnalyticMotivePackageAlgebraization G P)
    (i : P.compactGeometricLayer.thick.GeneratorIndex) :
    A.parentGeometricEffectiveMotiveAt composition implementation i =
      (A.at i).parentGeometricEffectiveMotive composition implementation :=
  rfl

/-- The parent stable image is the image of the selected package generator. -/
theorem parentStableMotiveAt_eq_at
    {P : ConstructedStableAnalyticMotivePackage}
    (A : ConstructedStableAnalyticMotivePackageAlgebraization G P)
    (i : P.compactGeometricLayer.thick.GeneratorIndex) :
    A.parentStableMotiveAt composition i =
      (A.at i).parentStableMotive composition :=
  rfl

end ConstructedStableAnalyticMotivePackageAlgebraization

end

end AnalyticMotives
end LFunctions
end Boundary

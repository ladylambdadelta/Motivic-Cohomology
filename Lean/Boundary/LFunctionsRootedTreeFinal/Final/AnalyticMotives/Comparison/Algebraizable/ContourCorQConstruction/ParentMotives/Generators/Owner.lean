import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.ParentMotives.Geometric.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.ParentMotives.Stable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.GeneratorShadows.Owner

/-!
# Parent motive images of constructed compact generators

This file lifts smooth algebraization from source bulks to constructed compact
analytic generators, then applies the parent effective and stable constructors.
-/

universe u

open CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

noncomputable section

/-- Smooth algebraization evidence for a constructed compact analytic generator. -/
structure ConstructedCompactAnalyticGeneratorAlgebraization
    (G : PerfectAnalyticGround) (K : ConstructedCompactAnalyticGenerator) where
  sourceAlgebraization : SmoothAlgebraization G K.source

namespace ConstructedCompactAnalyticGeneratorAlgebraization

/-- The smooth scheme over the perfect ground attached to the generator source. -/
def scheme {G : PerfectAnalyticGround} {K : ConstructedCompactAnalyticGenerator}
    (A : ConstructedCompactAnalyticGeneratorAlgebraization G K) :
    Geometry.SmSchemeOver G.carrier :=
  A.sourceAlgebraization.scheme

/-- The underlying scheme of the algebraization is the generator shadow. -/
theorem scheme_eq_generator_shadow
    {G : PerfectAnalyticGround} {K : ConstructedCompactAnalyticGenerator}
    (A : ConstructedCompactAnalyticGeneratorAlgebraization G K) :
    A.scheme.scheme = K.algebraicShadow :=
  A.sourceAlgebraization.scheme_eq_shadow

variable {G : PerfectAnalyticGround}
variable (composition : Boundary.CanonicalCompositionData (k := G.carrier))
variable [Abelian (LinearPST (Boundary.canonicalCategory composition))]
variable [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
variable [Abelian (canonicalA1NisLocalization composition)]
variable [HasDerivedCategory (canonicalA1NisLocalization composition)]
variable [(canonicalA1NisLocalizationFunctor composition).Additive]
variable [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
variable [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]

/-- Parent effective motive image of an algebraized constructed generator. -/
def parentEffectiveMotive
    {K : ConstructedCompactAnalyticGenerator}
    (A : ConstructedCompactAnalyticGeneratorAlgebraization G K) :
    canonicalEffectiveMotives composition :=
  A.sourceAlgebraization.parentEffectiveMotive composition

/-- Parent geometric effective motive image of an algebraized constructed generator. -/
def parentGeometricEffectiveMotive
    {K : ConstructedCompactAnalyticGenerator}
    (implementation :
      CanonicalA1NisLocalizationImplementation composition)
    (A : ConstructedCompactAnalyticGeneratorAlgebraization G K) :
    canonicalGeometricEffectiveMotives composition implementation :=
  A.sourceAlgebraization.parentGeometricEffectiveMotive
    composition implementation

/-- Parent stable `DMgm` image of an algebraized constructed generator. -/
def parentStableMotive
    {K : ConstructedCompactAnalyticGenerator}
    (A : ConstructedCompactAnalyticGeneratorAlgebraization G K) :
    VoevodskyDMgmQ_Q (composition := composition) :=
  A.sourceAlgebraization.parentStableMotive composition

/-- The effective image is computed from the generator source algebraization. -/
theorem parentEffectiveMotive_eq_source
    {K : ConstructedCompactAnalyticGenerator}
    (A : ConstructedCompactAnalyticGeneratorAlgebraization G K) :
    A.parentEffectiveMotive composition =
      A.sourceAlgebraization.parentEffectiveMotive composition :=
  rfl

/-- The geometric effective image is computed from the source algebraization. -/
theorem parentGeometricEffectiveMotive_eq_source
    {K : ConstructedCompactAnalyticGenerator}
    (implementation :
      CanonicalA1NisLocalizationImplementation composition)
    (A : ConstructedCompactAnalyticGeneratorAlgebraization G K) :
    A.parentGeometricEffectiveMotive composition implementation =
      A.sourceAlgebraization.parentGeometricEffectiveMotive
        composition implementation :=
  rfl

/-- The stable image is computed from the generator source algebraization. -/
theorem parentStableMotive_eq_source
    {K : ConstructedCompactAnalyticGenerator}
    (A : ConstructedCompactAnalyticGeneratorAlgebraization G K) :
    A.parentStableMotive composition =
      A.sourceAlgebraization.parentStableMotive composition :=
  rfl

end ConstructedCompactAnalyticGeneratorAlgebraization

end

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.ParentMotives.Profiles.Package.Owner

/-!
# Indexed parent images in a stable package comparison profile

This file exposes the parent effective, geometric effective, and stable images
of each compact generator selected by a parent comparison profile.
-/

universe u

open CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

noncomputable section

namespace ConstructedStableAnalyticMotiveParentProfile

variable (P : ConstructedStableAnalyticMotiveParentProfile.{u})
variable (composition :
  Boundary.CanonicalCompositionData (k := P.perfectGround.carrier))
variable [Abelian (LinearPST (Boundary.canonicalCategory composition))]
variable [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
variable [Abelian (canonicalA1NisLocalization composition)]
variable [HasDerivedCategory (canonicalA1NisLocalization composition)]
variable [(canonicalA1NisLocalizationFunctor composition).Additive]
variable [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
variable [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]

/-- Parent effective motive image of one compact generator in the profile. -/
def parentEffectiveMotiveAt
    (i : P.GeneratorIndex) :
    canonicalEffectiveMotives composition :=
  (P.generatorAlgebraizationAt i).parentEffectiveMotive composition

/-- Parent geometric effective motive image of one compact generator in the profile. -/
def parentGeometricEffectiveMotiveAt
    (implementation :
      CanonicalA1NisLocalizationImplementation composition)
    (i : P.GeneratorIndex) :
    canonicalGeometricEffectiveMotives composition implementation :=
  (P.generatorAlgebraizationAt i).parentGeometricEffectiveMotive
    composition implementation

/-- Parent stable motive image of one compact generator in the profile. -/
def parentStableMotiveAt
    (i : P.GeneratorIndex) :
    VoevodskyDMgmQ_Q (composition := composition) :=
  (P.generatorAlgebraizationAt i).parentStableMotive composition

/-- The effective image is computed from the selected generator algebraization. -/
theorem parentEffectiveMotiveAt_eq_generator
    (i : P.GeneratorIndex) :
    P.parentEffectiveMotiveAt composition i =
      (P.generatorAlgebraizationAt i).parentEffectiveMotive composition :=
  rfl

/-- The geometric image is computed from the selected generator algebraization. -/
theorem parentGeometricEffectiveMotiveAt_eq_generator
    (implementation :
      CanonicalA1NisLocalizationImplementation composition)
    (i : P.GeneratorIndex) :
    P.parentGeometricEffectiveMotiveAt composition implementation i =
      (P.generatorAlgebraizationAt i).parentGeometricEffectiveMotive
        composition implementation :=
  rfl

/-- The stable image is computed from the selected generator algebraization. -/
theorem parentStableMotiveAt_eq_generator
    (i : P.GeneratorIndex) :
    P.parentStableMotiveAt composition i =
      (P.generatorAlgebraizationAt i).parentStableMotive composition :=
  rfl

end ConstructedStableAnalyticMotiveParentProfile

end

end AnalyticMotives
end LFunctions
end Boundary

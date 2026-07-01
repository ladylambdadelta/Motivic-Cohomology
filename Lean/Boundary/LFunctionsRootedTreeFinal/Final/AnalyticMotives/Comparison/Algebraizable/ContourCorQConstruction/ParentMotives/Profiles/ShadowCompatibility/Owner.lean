import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.ParentMotives.Profiles.IndexedImages.Owner

/-!
# Shadow compatibility for parent comparison profiles

This file records that the smooth schemes used for parent motive images are
the algebraic shadows already carried by the analytic compact generators.
-/

universe u

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace ConstructedStableAnalyticMotiveParentProfile

/-- The source bulk of one compact generator in a parent comparison profile. -/
def generatorSource
    (P : ConstructedStableAnalyticMotiveParentProfile.{u})
    (i : P.GeneratorIndex) :
    ContourAdmissibleBulk :=
  (P.generatorAt i).source

/-- The algebraic shadow of one compact generator in a parent comparison profile. -/
def generatorAlgebraicShadow
    (P : ConstructedStableAnalyticMotiveParentProfile.{u})
    (i : P.GeneratorIndex) :
    ArithmeticBase :=
  (P.generatorAt i).algebraicShadow

/-- The smooth scheme selected by the generator algebraization. -/
def generatorSmoothSchemeAt
    (P : ConstructedStableAnalyticMotiveParentProfile.{u})
    (i : P.GeneratorIndex) :
    Geometry.SmSchemeOver P.perfectGround.carrier :=
  (P.generatorAlgebraizationAt i).scheme

/-- The selected smooth scheme realizes the generator's analytic algebraic shadow. -/
theorem generatorSmoothSchemeAt_eq_shadow
    (P : ConstructedStableAnalyticMotiveParentProfile.{u})
    (i : P.GeneratorIndex) :
    (P.generatorSmoothSchemeAt i).scheme = P.generatorAlgebraicShadow i :=
  (P.generatorAlgebraizationAt i).scheme_eq_generator_shadow

/-- The profile generator shadow is the source bulk's arithmetic base. -/
theorem generatorAlgebraicShadow_eq_source_base
    (P : ConstructedStableAnalyticMotiveParentProfile.{u})
    (i : P.GeneratorIndex) :
    P.generatorAlgebraicShadow i = (P.generatorSource i).core.base :=
  rfl

/-- The selected smooth scheme realizes the source bulk's arithmetic base. -/
theorem generatorSmoothSchemeAt_eq_source_base
    (P : ConstructedStableAnalyticMotiveParentProfile.{u})
    (i : P.GeneratorIndex) :
    (P.generatorSmoothSchemeAt i).scheme = (P.generatorSource i).core.base :=
  P.generatorSmoothSchemeAt_eq_shadow i

end ConstructedStableAnalyticMotiveParentProfile

end AnalyticMotives
end LFunctions
end Boundary

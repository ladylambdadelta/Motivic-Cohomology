import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.ParentMotives.IdempotentCompletions.Owner

/-!
# Algebraized compact-geometric analytic motives

This file packages smooth algebraization evidence for the thick and idempotent
generator families carried by a constructed compact-geometric analytic motive.
-/

universe u

open CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

noncomputable section

/-- Smooth algebraization evidence for a constructed compact-geometric motive. -/
structure ConstructedCompactGeometricAnalyticMotiveAlgebraization
    (G : PerfectAnalyticGround)
    (M : ConstructedCompactGeometricAnalyticMotive) where
  thickAlgebraization :
    ConstructedCompactAnalyticThickClosureAlgebraization G M.thick
  idempotentAlgebraization :
    ConstructedCompactAnalyticIdempotentCompletionAlgebraization G M.idempotent

namespace ConstructedCompactGeometricAnalyticMotiveAlgebraization

/-- The algebraization of the thick generator family. -/
def thick {G : PerfectAnalyticGround}
    {M : ConstructedCompactGeometricAnalyticMotive}
    (A : ConstructedCompactGeometricAnalyticMotiveAlgebraization G M) :
    ConstructedCompactAnalyticThickClosureAlgebraization G M.thick :=
  A.thickAlgebraization

/-- The algebraization of the idempotent-completion generator family. -/
def idempotent {G : PerfectAnalyticGround}
    {M : ConstructedCompactGeometricAnalyticMotive}
    (A : ConstructedCompactGeometricAnalyticMotiveAlgebraization G M) :
    ConstructedCompactAnalyticIdempotentCompletionAlgebraization G M.idempotent :=
  A.idempotentAlgebraization

/-- The algebraization selected for one compact-geometric generator. -/
def at {G : PerfectAnalyticGround}
    {M : ConstructedCompactGeometricAnalyticMotive}
    (A : ConstructedCompactGeometricAnalyticMotiveAlgebraization G M)
    (i : M.thick.GeneratorIndex) :
    ConstructedCompactAnalyticGeneratorAlgebraization G (M.generatorAt i) :=
  A.thick.at i

variable {G : PerfectAnalyticGround}
variable (composition : Boundary.CanonicalCompositionData (k := G.carrier))
variable [Abelian (LinearPST (Boundary.canonicalCategory composition))]
variable [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
variable [Abelian (canonicalA1NisLocalization composition)]
variable [HasDerivedCategory (canonicalA1NisLocalization composition)]
variable [(canonicalA1NisLocalizationFunctor composition).Additive]
variable [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
variable [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]

/-- Parent geometric effective image of one compact-geometric generator. -/
def parentGeometricEffectiveMotiveAt
    {M : ConstructedCompactGeometricAnalyticMotive}
    (implementation :
      CanonicalA1NisLocalizationImplementation composition)
    (A : ConstructedCompactGeometricAnalyticMotiveAlgebraization G M)
    (i : M.thick.GeneratorIndex) :
    canonicalGeometricEffectiveMotives composition implementation :=
  (A.at i).parentGeometricEffectiveMotive composition implementation

/-- Parent stable image of one compact-geometric generator. -/
def parentStableMotiveAt
    {M : ConstructedCompactGeometricAnalyticMotive}
    (A : ConstructedCompactGeometricAnalyticMotiveAlgebraization G M)
    (i : M.thick.GeneratorIndex) :
    VoevodskyDMgmQ_Q (composition := composition) :=
  (A.at i).parentStableMotive composition

/-- The parent geometric image is the image of the selected generator algebraization. -/
theorem parentGeometricEffectiveMotiveAt_eq_at
    {M : ConstructedCompactGeometricAnalyticMotive}
    (implementation :
      CanonicalA1NisLocalizationImplementation composition)
    (A : ConstructedCompactGeometricAnalyticMotiveAlgebraization G M)
    (i : M.thick.GeneratorIndex) :
    A.parentGeometricEffectiveMotiveAt composition implementation i =
      (A.at i).parentGeometricEffectiveMotive composition implementation :=
  rfl

/-- The parent stable image is the image of the selected generator algebraization. -/
theorem parentStableMotiveAt_eq_at
    {M : ConstructedCompactGeometricAnalyticMotive}
    (A : ConstructedCompactGeometricAnalyticMotiveAlgebraization G M)
    (i : M.thick.GeneratorIndex) :
    A.parentStableMotiveAt composition i =
      (A.at i).parentStableMotive composition :=
  rfl

end ConstructedCompactGeometricAnalyticMotiveAlgebraization

end

end AnalyticMotives
end LFunctions
end Boundary

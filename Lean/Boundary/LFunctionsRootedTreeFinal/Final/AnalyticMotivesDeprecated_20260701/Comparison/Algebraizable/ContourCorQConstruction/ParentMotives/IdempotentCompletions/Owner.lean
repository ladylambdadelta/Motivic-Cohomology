import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.ParentMotives.GeneratorFamilies.Owner

/-!
# Algebraized idempotent-completion generator families

This file records the smooth algebraization data carried by the generator
family underlying a constructed idempotent-completion object.
-/

universe u

open CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

noncomputable section

/-- Smooth algebraization evidence for the generators of an idempotent completion. -/
structure ConstructedCompactAnalyticIdempotentCompletionAlgebraization
    (G : PerfectAnalyticGround)
    (E : ConstructedCompactAnalyticIdempotentCompletion) where
  thickAlgebraization :
    ConstructedCompactAnalyticThickClosureAlgebraization G E.thickClosure

namespace ConstructedCompactAnalyticIdempotentCompletionAlgebraization

/-- The algebraization of the underlying thick closure. -/
def thick {G : PerfectAnalyticGround}
    {E : ConstructedCompactAnalyticIdempotentCompletion}
    (A : ConstructedCompactAnalyticIdempotentCompletionAlgebraization G E) :
    ConstructedCompactAnalyticThickClosureAlgebraization G E.thickClosure :=
  A.thickAlgebraization

/-- The algebraization selected for one generator of the idempotent completion. -/
def at {G : PerfectAnalyticGround}
    {E : ConstructedCompactAnalyticIdempotentCompletion}
    (A : ConstructedCompactAnalyticIdempotentCompletionAlgebraization G E)
    (i : E.thickClosure.GeneratorIndex) :
    ConstructedCompactAnalyticGeneratorAlgebraization G (E.generatorAt i) :=
  A.thick.at i

/-- The selected smooth scheme for one generator of the idempotent completion. -/
def schemeAt {G : PerfectAnalyticGround}
    {E : ConstructedCompactAnalyticIdempotentCompletion}
    (A : ConstructedCompactAnalyticIdempotentCompletionAlgebraization G E)
    (i : E.thickClosure.GeneratorIndex) :
    Geometry.SmSchemeOver G.carrier :=
  (A.at i).scheme

variable {G : PerfectAnalyticGround}
variable (composition : Boundary.CanonicalCompositionData (k := G.carrier))
variable [Abelian (LinearPST (Boundary.canonicalCategory composition))]
variable [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
variable [Abelian (canonicalA1NisLocalization composition)]
variable [HasDerivedCategory (canonicalA1NisLocalization composition)]
variable [(canonicalA1NisLocalizationFunctor composition).Additive]
variable [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
variable [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]

/-- Parent effective motive image of one selected idempotent-completion generator. -/
def parentEffectiveMotiveAt
    {E : ConstructedCompactAnalyticIdempotentCompletion}
    (A : ConstructedCompactAnalyticIdempotentCompletionAlgebraization G E)
    (i : E.thickClosure.GeneratorIndex) :
    canonicalEffectiveMotives composition :=
  (A.at i).parentEffectiveMotive composition

/-- Parent stable motive image of one selected idempotent-completion generator. -/
def parentStableMotiveAt
    {E : ConstructedCompactAnalyticIdempotentCompletion}
    (A : ConstructedCompactAnalyticIdempotentCompletionAlgebraization G E)
    (i : E.thickClosure.GeneratorIndex) :
    VoevodskyDMgmQ_Q (composition := composition) :=
  (A.at i).parentStableMotive composition

/-- The parent effective image is the image of the selected generator algebraization. -/
theorem parentEffectiveMotiveAt_eq_at
    {E : ConstructedCompactAnalyticIdempotentCompletion}
    (A : ConstructedCompactAnalyticIdempotentCompletionAlgebraization G E)
    (i : E.thickClosure.GeneratorIndex) :
    A.parentEffectiveMotiveAt composition i =
      (A.at i).parentEffectiveMotive composition :=
  rfl

/-- The parent stable image is the image of the selected generator algebraization. -/
theorem parentStableMotiveAt_eq_at
    {E : ConstructedCompactAnalyticIdempotentCompletion}
    (A : ConstructedCompactAnalyticIdempotentCompletionAlgebraization G E)
    (i : E.thickClosure.GeneratorIndex) :
    A.parentStableMotiveAt composition i =
      (A.at i).parentStableMotive composition :=
  rfl

end ConstructedCompactAnalyticIdempotentCompletionAlgebraization

end

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.ParentMotives.Generators.Owner

/-!
# Parent motive images of constructed generator families

This file records smooth algebraization evidence for every compact generator
in a constructed finite thick-closure family.
-/

universe u

open CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

noncomputable section

/-- Smooth algebraization evidence for each generator in a constructed thick closure. -/
structure ConstructedCompactAnalyticThickClosureAlgebraization
    (G : PerfectAnalyticGround) (C : ConstructedCompactAnalyticThickClosure) where
  generatorAlgebraization :
    (i : C.GeneratorIndex) →
      ConstructedCompactAnalyticGeneratorAlgebraization G (C.generatorAt i)

namespace ConstructedCompactAnalyticThickClosureAlgebraization

/-- The algebraization selected for one generator in the finite family. -/
def at {G : PerfectAnalyticGround} {C : ConstructedCompactAnalyticThickClosure}
    (A : ConstructedCompactAnalyticThickClosureAlgebraization G C)
    (i : C.GeneratorIndex) :
    ConstructedCompactAnalyticGeneratorAlgebraization G (C.generatorAt i) :=
  A.generatorAlgebraization i

/-- The smooth scheme attached to one selected generator. -/
def schemeAt {G : PerfectAnalyticGround} {C : ConstructedCompactAnalyticThickClosure}
    (A : ConstructedCompactAnalyticThickClosureAlgebraization G C)
    (i : C.GeneratorIndex) :
    Geometry.SmSchemeOver G.carrier :=
  (A.at i).scheme

/-- The selected scheme realizes the selected generator shadow. -/
theorem schemeAt_eq_generator_shadow
    {G : PerfectAnalyticGround} {C : ConstructedCompactAnalyticThickClosure}
    (A : ConstructedCompactAnalyticThickClosureAlgebraization G C)
    (i : C.GeneratorIndex) :
    (A.schemeAt i).scheme = C.generatorAlgebraicShadow i :=
  (A.at i).scheme_eq_generator_shadow

variable {G : PerfectAnalyticGround}
variable (composition : Boundary.CanonicalCompositionData (k := G.carrier))
variable [Abelian (LinearPST (Boundary.canonicalCategory composition))]
variable [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
variable [Abelian (canonicalA1NisLocalization composition)]
variable [HasDerivedCategory (canonicalA1NisLocalization composition)]
variable [(canonicalA1NisLocalizationFunctor composition).Additive]
variable [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
variable [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]

/-- Parent effective motive image of one selected generator in the family. -/
def parentEffectiveMotiveAt
    {C : ConstructedCompactAnalyticThickClosure}
    (A : ConstructedCompactAnalyticThickClosureAlgebraization G C)
    (i : C.GeneratorIndex) :
    canonicalEffectiveMotives composition :=
  (A.at i).parentEffectiveMotive composition

/-- Parent geometric effective motive image of one selected generator. -/
def parentGeometricEffectiveMotiveAt
    {C : ConstructedCompactAnalyticThickClosure}
    (implementation :
      CanonicalA1NisLocalizationImplementation composition)
    (A : ConstructedCompactAnalyticThickClosureAlgebraization G C)
    (i : C.GeneratorIndex) :
    canonicalGeometricEffectiveMotives composition implementation :=
  (A.at i).parentGeometricEffectiveMotive composition implementation

/-- Parent stable motive image of one selected generator in the family. -/
def parentStableMotiveAt
    {C : ConstructedCompactAnalyticThickClosure}
    (A : ConstructedCompactAnalyticThickClosureAlgebraization G C)
    (i : C.GeneratorIndex) :
    VoevodskyDMgmQ_Q (composition := composition) :=
  (A.at i).parentStableMotive composition

/-- The parent effective image at an index is the image of the selected algebraization. -/
theorem parentEffectiveMotiveAt_eq_at
    {C : ConstructedCompactAnalyticThickClosure}
    (A : ConstructedCompactAnalyticThickClosureAlgebraization G C)
    (i : C.GeneratorIndex) :
    A.parentEffectiveMotiveAt composition i =
      (A.at i).parentEffectiveMotive composition :=
  rfl

/-- The parent geometric image at an index is the image of the selected algebraization. -/
theorem parentGeometricEffectiveMotiveAt_eq_at
    {C : ConstructedCompactAnalyticThickClosure}
    (implementation :
      CanonicalA1NisLocalizationImplementation composition)
    (A : ConstructedCompactAnalyticThickClosureAlgebraization G C)
    (i : C.GeneratorIndex) :
    A.parentGeometricEffectiveMotiveAt composition implementation i =
      (A.at i).parentGeometricEffectiveMotive composition implementation :=
  rfl

/-- The parent stable image at an index is the image of the selected algebraization. -/
theorem parentStableMotiveAt_eq_at
    {C : ConstructedCompactAnalyticThickClosure}
    (A : ConstructedCompactAnalyticThickClosureAlgebraization G C)
    (i : C.GeneratorIndex) :
    A.parentStableMotiveAt composition i =
      (A.at i).parentStableMotive composition :=
  rfl

end ConstructedCompactAnalyticThickClosureAlgebraization

end

end AnalyticMotives
end LFunctions
end Boundary

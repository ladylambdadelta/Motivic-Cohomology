import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Descent.Owner

/-!
# Projection formulas for Boundary DMgm descent

This file records the object and morphism projection formulas for a
null-inverting additive-homotopy functor after it descends to the stable
analytic comparison source with values in the concrete Boundary DMgm target.
-/

universe u

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

variable {k : Type u} [Field k] [PerfectField k]

variable (composition : Boundary.CanonicalCompositionData (k := k))
variable [FiniteCorrespondence.CanonicalExternalProductFamily (k := k)]
variable [Abelian (LinearPST (Boundary.canonicalCategory composition))]
variable [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
variable [Abelian (canonicalA1NisLocalization composition)]
variable [HasDerivedCategory (canonicalA1NisLocalization composition)]
variable [(canonicalA1NisLocalizationFunctor composition).Additive]
variable [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
variable [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]

/-- The descended Boundary-DMgm comparison functor sends a quotient-represented
stable analytic object to an object isomorphic to the original functor value. -/
def TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (object : TraceAnalyticAdditiveHomotopyCategory) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
      (composition := composition)
      functor
      inverts).obj
        (TraceAnalyticStableHomotopyComparisonSource.objectOf object) ≅
      functor.obj object :=
  (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorFac
    (composition := composition)
    functor
    inverts).app object

/-- The Boundary-DMgm object projection is the component of the factorization
isomorphism. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso_eq
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (object : TraceAnalyticAdditiveHomotopyCategory) :
    TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition)
        functor
        inverts
        object =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorFac
        (composition := composition)
        functor
        inverts).app object :=
  rfl

/-- The descended Boundary-DMgm comparison functor's morphism action on
represented quotient morphisms is compatible with the original functor through
the factorization isomorphism. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_mapOf_naturality
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    {source targetObject : TraceAnalyticAdditiveHomotopyCategory}
    (hom : source ⟶ targetObject) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
      (composition := composition)
      functor
      inverts).map
        (TraceAnalyticStableHomotopyComparisonSource.mapOf hom) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition)
        functor
        inverts
        targetObject).hom =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition)
        functor
        inverts
        source).hom ≫
        functor.map hom :=
  (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorFac
    (composition := composition)
    functor
    inverts).hom.naturality hom

end AnalyticMotives
end LFunctions
end Boundary

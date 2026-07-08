import Mathlib.CategoryTheory.Localization.Predicate
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.Owner

/-!
# Cochain representatives of derived analytic motives

Every object of the derived analytic motive category is represented, up to
isomorphism, by an analytic abelian-envelope cochain complex before
quasi-isomorphism localization.  This file exposes Mathlib's localization
preimage construction under analytic names.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

attribute [local instance]
  TraceAnalyticDerivedMotiveCategory.hasDerivedCategory

/-- The derived localization functor is a localization at quasi-isomorphisms of
analytic abelian-envelope cochain complexes. -/
instance TraceAnalyticDerivedMotiveCategory.localizationFunctor_isLocalization :
    TraceAnalyticDerivedMotiveCategory.localizationFunctor.IsLocalization
      (HomologicalComplex.quasiIso
        TraceAnalyticAdditiveAbelianEnvelope
        (ComplexShape.up ℤ)) :=
  inferInstance

/-- A concrete analytic abelian-envelope cochain-complex representative of a
derived analytic motive. -/
def TraceAnalyticDerivedMotiveCategory.cochainPreimage
    (object : TraceAnalyticDerivedMotiveCategory) :
    TraceAnalyticAbelianCochainComplex :=
  TraceAnalyticDerivedMotiveCategory.localizationFunctor.objPreimage object

/-- The derived image of the concrete cochain preimage is isomorphic to the
original derived analytic motive. -/
def TraceAnalyticDerivedMotiveCategory.objectOfCochainPreimageIso
    (object : TraceAnalyticDerivedMotiveCategory) :
    TraceAnalyticDerivedMotiveCategory.objectOf
        (TraceAnalyticDerivedMotiveCategory.cochainPreimage object) ≅
      object :=
  TraceAnalyticDerivedMotiveCategory.localizationFunctor.objObjPreimageIso
    object

/-- The cochain preimage is Mathlib's essentially-surjective preimage for the
derived localization functor. -/
theorem TraceAnalyticDerivedMotiveCategory.cochainPreimage_eq
    (object : TraceAnalyticDerivedMotiveCategory) :
    TraceAnalyticDerivedMotiveCategory.cochainPreimage object =
      TraceAnalyticDerivedMotiveCategory.localizationFunctor.objPreimage
        object :=
  rfl

/-- The cochain-preimage comparison is Mathlib's essentially-surjective object
isomorphism for the derived localization functor. -/
theorem TraceAnalyticDerivedMotiveCategory.objectOfCochainPreimageIso_eq
    (object : TraceAnalyticDerivedMotiveCategory) :
    TraceAnalyticDerivedMotiveCategory.objectOfCochainPreimageIso object =
      TraceAnalyticDerivedMotiveCategory
        .localizationFunctor.objObjPreimageIso object :=
  rfl

/-- Every derived analytic motive belongs to the iso-closure of derived images
of analytic abelian-envelope cochain complexes. -/
theorem TraceAnalyticDerivedMotiveCategory.mem_isoClosure_objectOf_cochain
    (object : TraceAnalyticDerivedMotiveCategory) :
    CategoryTheory.isoClosure
        (fun candidate : TraceAnalyticDerivedMotiveCategory =>
          ∃ preimage : TraceAnalyticAbelianCochainComplex,
            candidate =
              TraceAnalyticDerivedMotiveCategory.objectOf preimage)
        object :=
  Exists.intro
    (TraceAnalyticDerivedMotiveCategory.objectOf
      (TraceAnalyticDerivedMotiveCategory.cochainPreimage object))
    (Exists.intro
      (Exists.intro
        (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
        rfl)
      (Nonempty.intro
        (TraceAnalyticDerivedMotiveCategory.objectOfCochainPreimageIso
          object)))

end AnalyticMotives
end LFunctions
end Boundary

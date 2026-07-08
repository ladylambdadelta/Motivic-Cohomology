import Mathlib.Algebra.Homology.Localization
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.Owner

/-!
# Cochain representatives of additive analytic homotopy objects

The homotopy quotient from additive analytic cochain complexes to the additive
analytic homotopy category is a localization at homotopy equivalences.  This
file exposes the resulting essentially-surjective preimage construction under
analytic names.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- A concrete additive cochain-complex representative of an additive homotopy
object. -/
def TraceAnalyticAdditiveHomotopyCategory.cochainPreimage
    (object : TraceAnalyticAdditiveHomotopyCategory) :
    TraceAnalyticAdditiveCochainComplex :=
  TraceAnalyticAdditiveHomotopyCategory.quotientFunctor.objPreimage object

/-- The homotopy image of the concrete cochain preimage is isomorphic to the
original additive homotopy object. -/
def TraceAnalyticAdditiveHomotopyCategory.objectOfCochainPreimageIso
    (object : TraceAnalyticAdditiveHomotopyCategory) :
    TraceAnalyticAdditiveHomotopyCategory.objectOf
        (TraceAnalyticAdditiveHomotopyCategory.cochainPreimage object) ≅
      object :=
  TraceAnalyticAdditiveHomotopyCategory.quotientFunctor.objObjPreimageIso
    object

/-- The concrete cochain preimage is Mathlib's essentially-surjective preimage
for the homotopy quotient functor. -/
theorem TraceAnalyticAdditiveHomotopyCategory.cochainPreimage_eq
    (object : TraceAnalyticAdditiveHomotopyCategory) :
    TraceAnalyticAdditiveHomotopyCategory.cochainPreimage object =
      TraceAnalyticAdditiveHomotopyCategory.quotientFunctor.objPreimage
        object :=
  rfl

/-- The cochain-preimage comparison is Mathlib's essentially-surjective object
isomorphism for the homotopy quotient functor. -/
theorem TraceAnalyticAdditiveHomotopyCategory.objectOfCochainPreimageIso_eq
    (object : TraceAnalyticAdditiveHomotopyCategory) :
    TraceAnalyticAdditiveHomotopyCategory.objectOfCochainPreimageIso object =
      TraceAnalyticAdditiveHomotopyCategory
        .quotientFunctor.objObjPreimageIso object :=
  rfl

/-- Every additive homotopy object belongs to the iso-closure of homotopy
images of concrete additive cochain complexes. -/
theorem TraceAnalyticAdditiveHomotopyCategory.mem_isoClosure_objectOf_cochain
    (object : TraceAnalyticAdditiveHomotopyCategory) :
    CategoryTheory.isoClosure
        (fun candidate : TraceAnalyticAdditiveHomotopyCategory =>
          ∃ preimage : TraceAnalyticAdditiveCochainComplex,
            candidate =
              TraceAnalyticAdditiveHomotopyCategory.objectOf preimage)
        object :=
  Exists.intro
    (TraceAnalyticAdditiveHomotopyCategory.objectOf
      (TraceAnalyticAdditiveHomotopyCategory.cochainPreimage object))
    (Exists.intro
      (Exists.intro
        (TraceAnalyticAdditiveHomotopyCategory.cochainPreimage object)
        rfl)
      (Nonempty.intro
        (TraceAnalyticAdditiveHomotopyCategory
          .objectOfCochainPreimageIso object)))

end AnalyticMotives
end LFunctions
end Boundary

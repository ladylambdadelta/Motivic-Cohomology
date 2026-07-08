import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Owner

/-!
# Comparison-source additive representatives

Every object of the stable analytic comparison source is represented, up to
isomorphism, by an additive analytic homotopy object before Verdier
localization.  This file exposes Mathlib's localization preimage construction
under analytic comparison-source names.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- An additive homotopy representative of a comparison-source object. -/
def TraceAnalyticDMgmComparisonSource.additivePreimage
    (object : TraceAnalyticDMgmComparisonSource) :
    TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticDMgmComparisonSource.quotientFunctor.objPreimage object

/-- The quotient of the additive preimage is isomorphic to the original
comparison-source object. -/
def TraceAnalyticDMgmComparisonSource.objectOfAdditivePreimageIso
    (object : TraceAnalyticDMgmComparisonSource) :
    TraceAnalyticDMgmComparisonSource.objectOf
        (TraceAnalyticDMgmComparisonSource.additivePreimage object) ≅
      object :=
  TraceAnalyticDMgmComparisonSource.quotientFunctor.objObjPreimageIso object

/-- The additive preimage is Mathlib's essentially-surjective preimage for the
comparison-source quotient functor. -/
theorem TraceAnalyticDMgmComparisonSource.additivePreimage_eq
    (object : TraceAnalyticDMgmComparisonSource) :
    TraceAnalyticDMgmComparisonSource.additivePreimage object =
      TraceAnalyticDMgmComparisonSource.quotientFunctor.objPreimage object :=
  rfl

/-- The preimage isomorphism is Mathlib's essentially-surjective object
isomorphism for the comparison-source quotient functor. -/
theorem TraceAnalyticDMgmComparisonSource.objectOfAdditivePreimageIso_eq
    (object : TraceAnalyticDMgmComparisonSource) :
    TraceAnalyticDMgmComparisonSource.objectOfAdditivePreimageIso object =
      TraceAnalyticDMgmComparisonSource.quotientFunctor.objObjPreimageIso
        object :=
  rfl

/-- Every comparison-source object lies in the iso-closure of the quotient
images of additive homotopy objects. -/
theorem TraceAnalyticDMgmComparisonSource.mem_isoClosure_objectOf_additive
    (object : TraceAnalyticDMgmComparisonSource) :
    CategoryTheory.isoClosure
        (fun candidate : TraceAnalyticDMgmComparisonSource =>
          ∃ preimage : TraceAnalyticAdditiveHomotopyCategory,
            candidate =
              TraceAnalyticDMgmComparisonSource.objectOf preimage)
        object :=
  Exists.intro
    (TraceAnalyticDMgmComparisonSource.objectOf
      (TraceAnalyticDMgmComparisonSource.additivePreimage object))
    (Exists.intro
      (Exists.intro
        (TraceAnalyticDMgmComparisonSource.additivePreimage object)
        rfl)
      (Nonempty.intro
        (TraceAnalyticDMgmComparisonSource.objectOfAdditivePreimageIso
          object)))

end AnalyticMotives
end LFunctions
end Boundary

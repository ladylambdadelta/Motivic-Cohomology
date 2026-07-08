import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Preimage.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.Preimage.Owner

/-!
# Cochain representatives of stable analytic comparison-source objects

This file composes the stable Verdier preimage with the concrete cochain
preimage for the additive homotopy quotient.  The result is an actual additive
analytic cochain complex representing any stable analytic comparison-source
object, up to the canonical quotient isomorphism.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource

/-- A concrete additive analytic cochain complex representing a stable
comparison-source object. -/
def cochainPreimage
    (object : TraceAnalyticDMgmComparisonSource) :
    TraceAnalyticAdditiveCochainComplex :=
  TraceAnalyticAdditiveHomotopyCategory.cochainPreimage
    (TraceAnalyticDMgmComparisonSource.additivePreimage object)

/-- The additive homotopy object represented by the cochain preimage of a
stable comparison-source object. -/
def cochainPreimageHomotopyObject
    (object : TraceAnalyticDMgmComparisonSource) :
    TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticAdditiveHomotopyCategory.objectOf
    (TraceAnalyticDMgmComparisonSource.cochainPreimage object)

/-- The cochain-preimage homotopy object is isomorphic to the stable additive
preimage. -/
def cochainPreimageHomotopyIso
    (object : TraceAnalyticDMgmComparisonSource) :
    TraceAnalyticDMgmComparisonSource.cochainPreimageHomotopyObject object ≅
      TraceAnalyticDMgmComparisonSource.additivePreimage object :=
  TraceAnalyticAdditiveHomotopyCategory.objectOfCochainPreimageIso
    (TraceAnalyticDMgmComparisonSource.additivePreimage object)

/-- The stable image of the cochain preimage is isomorphic to the original
stable comparison-source object. -/
def objectOfCochainPreimageIso
    (object : TraceAnalyticDMgmComparisonSource) :
    TraceAnalyticDMgmComparisonSource.objectOf
        (TraceAnalyticDMgmComparisonSource.cochainPreimageHomotopyObject
          object) ≅
      object :=
  TraceAnalyticDMgmComparisonSource.quotientFunctor.mapIso
      (TraceAnalyticDMgmComparisonSource.cochainPreimageHomotopyIso object) ≪≫
    TraceAnalyticDMgmComparisonSource.objectOfAdditivePreimageIso object

/-- The stable cochain preimage is the homotopy cochain preimage of the stable
additive preimage. -/
theorem cochainPreimage_eq
    (object : TraceAnalyticDMgmComparisonSource) :
    TraceAnalyticDMgmComparisonSource.cochainPreimage object =
      TraceAnalyticAdditiveHomotopyCategory.cochainPreimage
        (TraceAnalyticDMgmComparisonSource.additivePreimage object) :=
  rfl

/-- The cochain-preimage homotopy object is the homotopy image of the concrete
cochain preimage. -/
theorem cochainPreimageHomotopyObject_eq
    (object : TraceAnalyticDMgmComparisonSource) :
    TraceAnalyticDMgmComparisonSource.cochainPreimageHomotopyObject object =
      TraceAnalyticAdditiveHomotopyCategory.objectOf
        (TraceAnalyticDMgmComparisonSource.cochainPreimage object) :=
  rfl

/-- The stable cochain-preimage isomorphism is the stable image of the homotopy
preimage isomorphism followed by the stable additive-preimage isomorphism. -/
theorem objectOfCochainPreimageIso_eq
    (object : TraceAnalyticDMgmComparisonSource) :
    TraceAnalyticDMgmComparisonSource.objectOfCochainPreimageIso object =
      TraceAnalyticDMgmComparisonSource.quotientFunctor.mapIso
          (TraceAnalyticDMgmComparisonSource
            .cochainPreimageHomotopyIso object) ≪≫
        TraceAnalyticDMgmComparisonSource.objectOfAdditivePreimageIso
          object :=
  rfl

end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary

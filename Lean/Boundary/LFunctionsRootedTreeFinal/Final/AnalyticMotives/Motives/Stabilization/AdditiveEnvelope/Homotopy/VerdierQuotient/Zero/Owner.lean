import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.VerdierQuotient.Preadditive.Owner

/-!
# Zero object of the analytic Verdier quotient

The analytic Verdier quotient has a zero object because the quotient functor is
additive and the additive homotopy category has a zero object.  This file names
that construction at the stable-motive owner level so later stable-infinity
packages do not fill the pointed field by anonymous instance search.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The stable analytic motive category has the zero object transported by the
additive Verdier quotient functor. -/
def TraceAnalyticStableMotiveCategory.zeroObjectStructure :
    HasZeroObject TraceAnalyticStableMotiveCategory :=
  letI quotientAdditive :
      TraceAnalyticStableMotiveCategory.quotientFunctor.Additive :=
    TraceAnalyticStableMotiveCategory.quotientFunctorAdditive
  TraceAnalyticStableMotiveCategory.quotientFunctor.hasZeroObject_of_additive

end AnalyticMotives
end LFunctions
end Boundary

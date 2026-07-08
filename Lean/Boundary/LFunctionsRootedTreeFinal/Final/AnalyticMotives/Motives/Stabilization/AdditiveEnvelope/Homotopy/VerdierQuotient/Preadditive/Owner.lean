import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.VerdierQuotient.Owner

/-!
# Preadditivity of the analytic Verdier quotient

Mathlib's calculus-of-fractions localization carries the preadditive structure
from the source category to the Verdier quotient, and makes the quotient
functor additive.  This file exposes those inherited structures at the
analytic-stable-motive owner level.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The stable analytic motive category is preadditive. -/
def TraceAnalyticStableMotiveCategory.preadditiveStructure :
    Preadditive TraceAnalyticStableMotiveCategory :=
  Localization.preadditive
    TraceAnalyticStableMotiveCategory.quotientFunctor
    TraceAnalyticStableNullSubcategory.invertedMorphisms

/-- The Verdier quotient functor is additive. -/
def TraceAnalyticStableMotiveCategory.quotientFunctorAdditive :
    TraceAnalyticStableMotiveCategory.quotientFunctor.Additive :=
  Localization.functor_additive
    TraceAnalyticStableMotiveCategory.quotientFunctor
    TraceAnalyticStableNullSubcategory.invertedMorphisms

end AnalyticMotives
end LFunctions
end Boundary

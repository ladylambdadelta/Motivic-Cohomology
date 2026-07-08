import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.Additive
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.YonedaComplex.Owner

/-!
# Additivity of the analytic Yoneda cochain functor

This file supplies the local analytic version of the additivity of the
Q-linear Yoneda embedding and its prolongation to cochain complexes.  The proof
is the concrete right-composition calculation on analytic trace morphisms:
postcomposition by a sum is the sum of the two postcompositions.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The analytic Q-linear Yoneda embedding is additive. -/
def TraceAnalyticAdditiveAbelianEnvelope.yonedaAdditive :
    TraceAnalyticAdditiveAbelianEnvelope.yoneda.Additive :=
  { map_add := fun {source target} {left right} =>
      NatTrans.ext
        (funext fun probe =>
          LinearMap.ext fun hom =>
            Preadditive.comp_add _ _ _ hom left right) }

/-- The degreewise analytic Yoneda functor on cochain complexes is additive. -/
def TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplexFunctorAdditive :
    TraceAnalyticAdditiveAbelianEnvelope
      .yonedaCochainComplexFunctor.Additive :=
  letI : TraceAnalyticAdditiveAbelianEnvelope.yoneda.Additive :=
    TraceAnalyticAdditiveAbelianEnvelope.yonedaAdditive
  Functor.map_homogical_complex_additive
    TraceAnalyticAdditiveAbelianEnvelope.yoneda
    (ComplexShape.up ℤ)

end AnalyticMotives
end LFunctions
end Boundary

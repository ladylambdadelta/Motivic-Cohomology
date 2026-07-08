import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.Owner

/-!
# Homology of derived analytic motives

This file exposes the concrete homology functors on the derived analytic
motive category and relates homology vanishing of a represented object to
`ExactAt` for the underlying analytic abelian-envelope cochain complex.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDerivedMotiveCategory

attribute [local instance]
  TraceAnalyticDerivedMotiveCategory.hasDerivedCategory

/-- The degree-`degree` homology functor on derived analytic motives. -/
def homologyFunctor
    (degree : ℤ) :
    TraceAnalyticDerivedMotiveCategory ⥤
      TraceAnalyticAdditiveAbelianEnvelope :=
  DerivedCategory.homologyFunctor
    TraceAnalyticAdditiveAbelianEnvelope
    degree

/-- Derived analytic homology is induced from cochain-complex homology through
the localization functor. -/
def homologyFunctorFactors
    (degree : ℤ) :
    TraceAnalyticDerivedMotiveCategory.localizationFunctor ⋙
        TraceAnalyticDerivedMotiveCategory.homologyFunctor degree ≅
      HomologicalComplex.homologyFunctor
        TraceAnalyticAdditiveAbelianEnvelope
        (ComplexShape.up ℤ)
        degree :=
  DerivedCategory.homologyFunctorFactors
    TraceAnalyticAdditiveAbelianEnvelope
    degree

/-- The homology functor wrapper is Mathlib's derived homology functor. -/
theorem homologyFunctor_eq
    (degree : ℤ) :
    TraceAnalyticDerivedMotiveCategory.homologyFunctor degree =
      DerivedCategory.homologyFunctor
        TraceAnalyticAdditiveAbelianEnvelope
        degree :=
  rfl

/-- The factorization wrapper is Mathlib's factorization of derived homology
through cochain-complex homology. -/
theorem homologyFunctorFactors_eq
    (degree : ℤ) :
    TraceAnalyticDerivedMotiveCategory.homologyFunctorFactors degree =
      DerivedCategory.homologyFunctorFactors
        TraceAnalyticAdditiveAbelianEnvelope
        degree :=
  rfl

/-- For a represented analytic abelian-envelope cochain complex, vanishing of
derived homology in one degree is equivalent to exactness of the underlying
cochain complex at that degree. -/
theorem homologyFunctor_objectOf_isZero_iff_exactAt
    (complex : TraceAnalyticAbelianCochainComplex)
    (degree : ℤ) :
    IsZero
        ((TraceAnalyticDerivedMotiveCategory.homologyFunctor degree).obj
          (TraceAnalyticDerivedMotiveCategory.objectOf complex)) ↔
      complex.ExactAt degree :=
  Iff.trans
    ((TraceAnalyticDerivedMotiveCategory.homologyFunctorFactors degree).app
        complex).isZero_iff
    (Iff.symm
      (_root_.HomologicalComplex.exactAt_iff_isZero_homology
        (K := complex)
        (i := degree)))

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary

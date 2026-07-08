import Mathlib.Algebra.Homology.Additive
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.YonedaComplex.Owner

/-!
# Isomorphism reflection for represented analytic cochain complexes

The degreewise Yoneda functor from concrete additive analytic cochain complexes
to abelian-envelope cochain complexes reflects isomorphisms.  This is the
cochain-level reflection bridge needed before abelian-envelope exactness can be
used to prove concrete cone-comparison isomorphisms.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticAdditiveAbelianEnvelope

/-- The degreewise analytic Yoneda functor on cochain complexes reflects
isomorphisms. -/
def yonedaCochainComplexReflectsIsomorphisms :
    TraceAnalyticAdditiveAbelianEnvelope
      .yonedaCochainComplexFunctor.ReflectsIsomorphisms :=
  inferInstance

/-- If a concrete analytic cochain map becomes an isomorphism after degreewise
Yoneda embedding, then it was already an isomorphism. -/
theorem isIso_of_yonedaCochainMap_isIso
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    [IsIso
      (TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainMap hom)] :
    IsIso hom :=
  letI :
      TraceAnalyticAdditiveAbelianEnvelope
        .yonedaCochainComplexFunctor.ReflectsIsomorphisms :=
    TraceAnalyticAdditiveAbelianEnvelope
      .yonedaCochainComplexReflectsIsomorphisms
  isIso_of_reflects_iso
    hom
    TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplexFunctor

/-- Isomorphism of a concrete analytic cochain map is equivalent to isomorphism
after degreewise Yoneda embedding. -/
theorem yonedaCochainMap_isIso_iff
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target) :
    IsIso
        (TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainMap hom) ↔
      IsIso hom :=
  letI :
      TraceAnalyticAdditiveAbelianEnvelope
        .yonedaCochainComplexFunctor.ReflectsIsomorphisms :=
    TraceAnalyticAdditiveAbelianEnvelope
      .yonedaCochainComplexReflectsIsomorphisms
  isIso_iff_of_reflects_iso
    hom
    TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplexFunctor

end TraceAnalyticAdditiveAbelianEnvelope

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.YonedaComplex.Owner

/-!
# Homology of represented analytic cochain complexes

The concrete additive analytic category is not abelian.  Its degreewise
Yoneda image lands in the abelian-envelope complex category, where homology is
available from the pointwise abelian structure.  This file records that
homology input at the true abelian-envelope owner level.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticAdditiveAbelianEnvelope

/-- The represented abelian-envelope cochain complex attached to a concrete
analytic additive cochain complex has homology in every degree. -/
theorem yonedaCochainComplex_hasHomology
    (complex : TraceAnalyticAdditiveCochainComplex)
    (degree : ℤ) :
    (TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex
      complex).HasHomology degree :=
  CategoryWithHomology.hasHomology
    ((TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex
      complex).sc degree)

/-- The represented abelian-envelope cochain complex attached to a concrete
analytic additive cochain complex has all homology objects. -/
theorem yonedaCochainComplex_hasHomology_all
    (complex : TraceAnalyticAdditiveCochainComplex) :
    ∀ degree : ℤ,
      (TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex
        complex).HasHomology degree :=
  fun degree =>
    TraceAnalyticAdditiveAbelianEnvelope
      .yonedaCochainComplex_hasHomology complex degree

end TraceAnalyticAdditiveAbelianEnvelope

end AnalyticMotives
end LFunctions
end Boundary

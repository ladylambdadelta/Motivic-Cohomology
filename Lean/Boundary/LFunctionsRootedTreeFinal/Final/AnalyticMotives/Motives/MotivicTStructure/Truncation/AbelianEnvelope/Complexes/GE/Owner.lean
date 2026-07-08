import Mathlib.Algebra.Homology.Embedding.TruncGE
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.Complexes.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Map.Owner

/-!
# Abelian-envelope analytic `GE` truncations

This file repeats the upper-tail truncation construction in the abelian
envelope of analytic additive complexes.  Unlike the concrete additive
category, this target category has homology in every short complex, so this is
the owner level for the homological truncation calculus.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- The abelian-envelope upper-tail truncation functor at cut `cut`. -/
def abelianEnvelopeTruncGEFunctor
    (cut : ℤ) :
    TraceAnalyticAbelianCochainComplex ⥤
      TraceAnalyticAbelianCochainComplex :=
  (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).truncGEFunctor
    TraceAnalyticAdditiveAbelianEnvelope

/-- The abelian-envelope upper-tail truncation of an analytic complex. -/
def abelianEnvelopeTruncGE
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    TraceAnalyticAbelianCochainComplex :=
  (TraceAnalyticMotivicTStructure.abelianEnvelopeTruncGEFunctor cut).obj
    complex

/-- The map induced on abelian-envelope upper-tail truncations. -/
def abelianEnvelopeTruncGEMap
    (cut : ℤ)
    {source target : TraceAnalyticAbelianCochainComplex}
    (hom : source ⟶ target) :
    TraceAnalyticMotivicTStructure.abelianEnvelopeTruncGE cut source ⟶
      TraceAnalyticMotivicTStructure.abelianEnvelopeTruncGE cut target :=
  (TraceAnalyticMotivicTStructure.abelianEnvelopeTruncGEFunctor cut).map hom

/-- The abelian-envelope upper truncation functor is Mathlib's `truncGEFunctor`
for the upper-tail integer embedding. -/
theorem abelianEnvelopeTruncGEFunctor_eq
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.abelianEnvelopeTruncGEFunctor cut =
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).truncGEFunctor
        TraceAnalyticAdditiveAbelianEnvelope :=
  rfl

/-- The object part of abelian-envelope upper truncation is the object part of
the abelian-envelope truncation functor. -/
theorem abelianEnvelopeTruncGE_eq_functor_obj
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    TraceAnalyticMotivicTStructure.abelianEnvelopeTruncGE cut complex =
      (TraceAnalyticMotivicTStructure.abelianEnvelopeTruncGEFunctor cut).obj
        complex :=
  rfl

/-- The map part of abelian-envelope upper truncation is the map part of the
abelian-envelope truncation functor. -/
theorem abelianEnvelopeTruncGEMap_eq_functor_map
    (cut : ℤ)
    {source target : TraceAnalyticAbelianCochainComplex}
    (hom : source ⟶ target) :
    TraceAnalyticMotivicTStructure.abelianEnvelopeTruncGEMap cut hom =
      (TraceAnalyticMotivicTStructure.abelianEnvelopeTruncGEFunctor cut).map
        hom :=
  rfl

/-- Every abelian-envelope analytic cochain complex has homology in every
degree. -/
theorem abelianEnvelopeCochainComplex_hasHomology
    (complex : TraceAnalyticAbelianCochainComplex)
    (degree : ℤ) :
    complex.HasHomology degree :=
  CategoryWithHomology.hasHomology (complex.sc degree)

/-- Every abelian-envelope analytic cochain complex has all homology objects. -/
theorem abelianEnvelopeCochainComplex_hasHomology_all
    (complex : TraceAnalyticAbelianCochainComplex) :
    ∀ degree : ℤ, complex.HasHomology degree :=
  fun degree =>
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainComplex_hasHomology complex degree

/-- The abelian-envelope upper truncation projection
`K ⟶ truncGE(cut,K)`. -/
def abelianEnvelopeTruncGEProjectionMap
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    complex ⟶
      TraceAnalyticMotivicTStructure.abelianEnvelopeTruncGE cut complex :=
  letI : ∀ degree : ℤ, complex.HasHomology degree :=
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainComplex_hasHomology_all complex
  TraceAnalyticMotivicTStructure.truncGEProjectionMap
    (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
    complex

/-- The abelian-envelope upper projection is the generic upper projection for
the integer upper-tail embedding. -/
theorem abelianEnvelopeTruncGEProjectionMap_eq
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    TraceAnalyticMotivicTStructure
        .abelianEnvelopeTruncGEProjectionMap cut complex =
      TraceAnalyticMotivicTStructure.truncGEProjectionMap
        (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
        complex :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

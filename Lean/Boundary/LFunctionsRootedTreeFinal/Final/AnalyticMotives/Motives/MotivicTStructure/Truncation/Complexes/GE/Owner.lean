import Mathlib.Algebra.Homology.Embedding.TruncGE
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Complexes.Owner

/-!
# Concrete analytic `GE` truncations of additive complexes

This file exposes Mathlib's canonical homological-complex truncation along the
integer embedding `ComplexShape.embeddingUpIntGE` under analytic-motive names.
These are concrete additive-complex truncations, before passage to the
homotopy category and before Verdier localization.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The integer upper-tail embedding used for the analytic `GE` truncation at
cut `cut`.  It embeds the natural-number shaped upper tail by `n ↦ cut + n`. -/
def TraceAnalyticMotivicTStructure.truncGEEmbedding
    (cut : ℤ) :
    ComplexShape.Embedding (ComplexShape.up ℕ) (ComplexShape.up ℤ) :=
  ComplexShape.embeddingUpIntGE cut

/-- The concrete additive-complex `GE` truncation functor at cut `cut`.

The source and target are both integer cochain complexes; Mathlib constructs
the truncation by first restricting to the upper tail and then extending back
by zero/opcycles at the boundary. -/
def TraceAnalyticMotivicTStructure.additiveTruncGEFunctor
    (cut : ℤ) :
    TraceAnalyticAdditiveCochainComplex ⥤
      TraceAnalyticAdditiveCochainComplex :=
  (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).truncGEFunctor
    TraceAnalyticAdditiveCategoryObject

/-- The concrete additive-complex `GE` truncation of one analytic complex. -/
def TraceAnalyticMotivicTStructure.additiveTruncGE
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex) :
    TraceAnalyticAdditiveCochainComplex :=
  (TraceAnalyticMotivicTStructure.additiveTruncGEFunctor cut).obj complex

/-- The concrete additive-complex `GE` truncation of a chain map. -/
def TraceAnalyticMotivicTStructure.additiveTruncGEMap
    (cut : ℤ)
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target) :
    TraceAnalyticMotivicTStructure.additiveTruncGE cut source ⟶
      TraceAnalyticMotivicTStructure.additiveTruncGE cut target :=
  (TraceAnalyticMotivicTStructure.additiveTruncGEFunctor cut).map hom

/-- The analytic `GE` truncation functor is Mathlib's `truncGEFunctor` for the
upper-tail integer embedding. -/
theorem TraceAnalyticMotivicTStructure.additiveTruncGEFunctor_eq
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.additiveTruncGEFunctor cut =
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).truncGEFunctor
        TraceAnalyticAdditiveCategoryObject :=
  rfl

/-- The object part of analytic `GE` truncation is the object part of the
analytic truncation functor. -/
theorem TraceAnalyticMotivicTStructure.additiveTruncGE_eq_functor_obj
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex) :
    TraceAnalyticMotivicTStructure.additiveTruncGE cut complex =
      (TraceAnalyticMotivicTStructure.additiveTruncGEFunctor cut).obj
        complex :=
  rfl

/-- The map part of analytic `GE` truncation is the map part of the analytic
truncation functor. -/
theorem TraceAnalyticMotivicTStructure.additiveTruncGEMap_eq_functor_map
    (cut : ℤ)
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target) :
    TraceAnalyticMotivicTStructure.additiveTruncGEMap cut hom =
      (TraceAnalyticMotivicTStructure.additiveTruncGEFunctor cut).map hom :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

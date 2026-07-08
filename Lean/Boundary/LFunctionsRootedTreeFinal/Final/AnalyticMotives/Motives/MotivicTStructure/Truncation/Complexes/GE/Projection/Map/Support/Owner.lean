import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Map.Owner

/-!
# Support of the full upper truncation projection map

This file upgrades the degreewise support statement for the projection
component to the actual chain map constructed by `Embedding.liftExtend`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
variable {ι ι' : Type*} {shape : ComplexShape ι} {ambientShape : ComplexShape ι'}

/-- If the retraction of an embedding is `none` at a degree, then there is no
tail index mapping to that degree. -/
theorem embedding_no_tail_of_r_eq_none
    (embedding : ComplexShape.Embedding shape ambientShape)
    (degree : ι')
    (hnone : embedding.r degree = none) :
    ¬ ∃ tail, embedding.f tail = degree :=
  fun witness =>
    let hsome :
        embedding.r degree = some witness.choose :=
      ComplexShape.Embedding.r_eq_some
        embedding
        witness.choose_spec
    Option.noConfusion
      (Eq.trans hnone.symm hsome)

/-- The full upper truncation projection map has zero component outside the
embedded upper tail. -/
theorem truncGEProjectionMap_f_of_r_eq_none
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (degree : ι')
    (hnone : embedding.r degree = none) :
    (TraceAnalyticMotivicTStructure.truncGEProjectionMap
        embedding
        complex).f degree =
      0 :=
  dif_neg
    (TraceAnalyticMotivicTStructure.embedding_no_tail_of_r_eq_none
      embedding
      degree
      hnone)

/-- Analytic integer specialization: the upper projection map has zero
component on any degree outside the upper-tail embedding. -/
theorem additiveTruncGEProjectionMap_f_of_r_eq_none
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (degree : ℤ)
    (hnone :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).r degree =
        none) :
    (TraceAnalyticMotivicTStructure.additiveTruncGEProjectionMap
        cut
        complex).f degree =
      0 :=
  TraceAnalyticMotivicTStructure.truncGEProjectionMap_f_of_r_eq_none
    (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
    complex
    degree
    hnone

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

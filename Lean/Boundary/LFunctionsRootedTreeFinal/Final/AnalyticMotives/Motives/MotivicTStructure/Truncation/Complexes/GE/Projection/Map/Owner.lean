import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Core.Lift.Owner

/-!
# Upper truncation projection map

This file constructs the full chain map `K ⟶ K.truncGE e` by extending the
restricted-core projection along Mathlib's `Embedding.liftExtend`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
variable {ι ι' : Type*} {shape : ComplexShape ι} {ambientShape : ComplexShape ι'}

/-- The full upper truncation projection chain map
`K ⟶ K.truncGE e`. -/
def truncGEProjectionMap
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree] :
    complex ⟶ complex.truncGE embedding :=
  embedding.liftExtend
    (truncGEProjectionCoreMap embedding complex)
    (truncGEProjectionCoreMap_hasLift embedding complex)

/-- Formula for a full upper projection component at a degree in the embedded
tail, expressed through Mathlib's `liftExtend` formula. -/
theorem truncGEProjectionMap_f_of_tail
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (tail : ι)
    (degree : ι')
    (hdegree : embedding.f tail = degree) :
    (truncGEProjectionMap embedding complex).f degree =
      (_root_.HomologicalComplex.restrictionXIso
          complex
          embedding
          hdegree).inv ≫
        (truncGEProjectionCoreMap embedding complex).f tail ≫
        (_root_.HomologicalComplex.extendXIso
          (complex.truncGE' embedding)
          embedding
          hdegree).inv :=
  embedding.liftExtend_f
    (truncGEProjectionCoreMap embedding complex)
    (truncGEProjectionCoreMap_hasLift embedding complex)
    hdegree

/-- Analytic integer specialization of the full upper truncation projection
chain map. -/
def additiveTruncGEProjectionMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    complex ⟶ TraceAnalyticMotivicTStructure.additiveTruncGE cut complex :=
  TraceAnalyticMotivicTStructure.truncGEProjectionMap
    (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
    complex

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

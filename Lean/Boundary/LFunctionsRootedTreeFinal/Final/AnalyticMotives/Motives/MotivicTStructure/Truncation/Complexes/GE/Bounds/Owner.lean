import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Objects.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Weights.Source.Bounds.Owner

/-!
# Bounded upper analytic truncations

This file proves that the concrete upper truncation of a bounded analytic
complex is again represented by a bounded analytic complex.  The bound is
allowed to increase by the single boundary opcycles object introduced by
Mathlib's canonical truncation.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- The uniform weight bound for the upper truncation of a bounded complex. -/
def additiveTruncGEBound
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    Nat :=
  Nat.max
    bound
    ((complex.complex.opcycles cut).weightLevel)

/-- The original bound maps into the upper-truncation bound. -/
theorem additiveTruncGEBound_original_le
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    bound ≤
      TraceAnalyticMotivicTStructure.additiveTruncGEBound cut complex :=
  Nat.le_max_left
    bound
    ((complex.complex.opcycles cut).weightLevel)

/-- The boundary opcycles weight maps into the upper-truncation bound. -/
theorem additiveTruncGEBound_boundary_le
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (complex.complex.opcycles cut).weightLevel ≤
      TraceAnalyticMotivicTStructure.additiveTruncGEBound cut complex :=
  Nat.le_max_right
    bound
    ((complex.complex.opcycles cut).weightLevel)

/-- At a boundary tail degree, the upper truncation degree weight is bounded
by the enlarged upper-truncation bound. -/
theorem additiveTruncGE_degreeWeight_le_of_boundary
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree]
    (degree : ℤ)
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).r degree =
        some tail)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail) :
    (TraceAnalyticMotivicTStructure.additiveTruncGE
        cut
        complex.complex).degreeWeight degree ≤
      TraceAnalyticMotivicTStructure.additiveTruncGEBound cut complex :=
  let object_eq :
      (TraceAnalyticMotivicTStructure.additiveTruncGE
          cut
          complex.complex).objectAt degree =
        complex.complex.opcycles degree :=
    TraceAnalyticMotivicTStructure.additiveTruncGE_X_of_boundary
      cut
      complex.complex
      degree
      tail
      htail
      hboundary
  let degree_eq_cut :
      degree = cut :=
    TraceAnalyticMotivicTStructure.truncGEEmbedding_boundary_degree_eq
      cut
      degree
      tail
      htail
      hboundary
  Eq.subst
    (motive := fun weight =>
      weight ≤
        TraceAnalyticMotivicTStructure.additiveTruncGEBound cut complex)
    (Eq.trans
      (TraceAnalyticAdditiveCochainComplex.degreeWeight_eq
        (TraceAnalyticMotivicTStructure.additiveTruncGE
          cut
          complex.complex)
        degree)
      (Eq.trans
        (congrArg TraceAnalyticAdditiveObject.weightLevel object_eq)
        (congrArg
          (fun boundaryDegree =>
            (complex.complex.opcycles boundaryDegree).weightLevel)
          degree_eq_cut)))
    (TraceAnalyticMotivicTStructure.additiveTruncGEBound_boundary_le
      cut
      complex)

/-- On a nonboundary upper-tail degree, the upper truncation degree weight is
bounded by the original bound and hence by the enlarged bound. -/
theorem additiveTruncGE_degreeWeight_le_of_not_boundary
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree]
    (degree : ℤ)
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).r degree =
        some tail)
    (hboundary :
      ¬ (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail) :
    (TraceAnalyticMotivicTStructure.additiveTruncGE
        cut
        complex.complex).degreeWeight degree ≤
      TraceAnalyticMotivicTStructure.additiveTruncGEBound cut complex :=
  let object_eq :
      (TraceAnalyticMotivicTStructure.additiveTruncGE
          cut
          complex.complex).objectAt degree =
        complex.complex.objectAt degree :=
    TraceAnalyticMotivicTStructure.additiveTruncGE_X_of_not_boundary
      cut
      complex.complex
      degree
      tail
      htail
      hboundary
  let original_le :
      complex.complex.degreeWeight degree ≤
        TraceAnalyticMotivicTStructure.additiveTruncGEBound cut complex :=
    Nat.le_trans
      (complex.degreeWeight_le degree)
      (TraceAnalyticMotivicTStructure.additiveTruncGEBound_original_le
        cut
        complex)
  Eq.subst
    (motive := fun weight =>
      weight ≤
        TraceAnalyticMotivicTStructure.additiveTruncGEBound cut complex)
    (Eq.trans
      (TraceAnalyticAdditiveCochainComplex.degreeWeight_eq
        (TraceAnalyticMotivicTStructure.additiveTruncGE
          cut
          complex.complex)
        degree)
      (Eq.trans
        (congrArg TraceAnalyticAdditiveObject.weightLevel object_eq)
        (Eq.symm
          (TraceAnalyticAdditiveCochainComplex.degreeWeight_eq
            complex.complex
            degree))))
    original_le

/-- Outside the upper tail, the upper truncation degree weight is zero and
hence bounded by the enlarged upper-truncation bound. -/
theorem additiveTruncGE_degreeWeight_le_of_r_eq_none
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree]
    (degree : ℤ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).r degree =
        none) :
    (TraceAnalyticMotivicTStructure.additiveTruncGE
        cut
        complex.complex).degreeWeight degree ≤
      TraceAnalyticMotivicTStructure.additiveTruncGEBound cut complex :=
  let object_eq :
      (TraceAnalyticMotivicTStructure.additiveTruncGE
          cut
          complex.complex).objectAt degree =
        TraceAnalyticAdditiveObject.zero :=
    TraceAnalyticMotivicTStructure.additiveTruncGE_X_of_r_eq_none
      cut
      complex.complex
      degree
      htail
  Eq.subst
    (motive := fun weight =>
      weight ≤
        TraceAnalyticMotivicTStructure.additiveTruncGEBound cut complex)
    (Eq.trans
      (TraceAnalyticAdditiveCochainComplex.degreeWeight_eq
        (TraceAnalyticMotivicTStructure.additiveTruncGE
          cut
          complex.complex)
        degree)
      (Eq.trans
        (congrArg TraceAnalyticAdditiveObject.weightLevel object_eq)
        TraceAnalyticAdditiveObject.weightLevel_zero))
    (Nat.zero_le
      (TraceAnalyticMotivicTStructure.additiveTruncGEBound cut complex))

/-- Every degree of the upper truncation of a bounded complex is bounded by
the enlarged upper-truncation bound. -/
theorem additiveTruncGE_degreeWeight_le
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree]
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.additiveTruncGE
        cut
        complex.complex).degreeWeight degree ≤
      TraceAnalyticMotivicTStructure.additiveTruncGEBound cut complex :=
  match htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).r degree with
  | none =>
      TraceAnalyticMotivicTStructure
        .additiveTruncGE_degreeWeight_le_of_r_eq_none
          cut
          complex
          degree
          htail
  | some tail =>
      if hboundary :
          (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
            tail then
        TraceAnalyticMotivicTStructure
          .additiveTruncGE_degreeWeight_le_of_boundary
            cut
            complex
            degree
            tail
            htail
            hboundary
      else
        TraceAnalyticMotivicTStructure
          .additiveTruncGE_degreeWeight_le_of_not_boundary
            cut
            complex
            degree
            tail
            htail
            hboundary

/-- The upper analytic truncation of a bounded comparison-source complex is
again a bounded comparison-source complex, with the explicit enlarged bound
above. -/
def sourceAdditiveTruncGEWeightBoundedBy
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree] :
    TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
      (TraceAnalyticMotivicTStructure.additiveTruncGEBound cut complex) :=
  ⟨
    TraceAnalyticMotivicTStructure.additiveTruncGE cut complex.complex,
    TraceAnalyticMotivicTStructure.additiveTruncGE_degreeWeight_le
      cut
      complex
  ⟩

/-- The bounded upper-truncation representative has the concrete upper
truncation as its underlying complex. -/
theorem sourceAdditiveTruncGEWeightBoundedBy_complex
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.sourceAdditiveTruncGEWeightBoundedBy
        cut
        complex).complex =
      TraceAnalyticMotivicTStructure.additiveTruncGE cut complex.complex :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

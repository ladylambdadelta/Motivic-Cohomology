import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.LE.Objects.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Weights.Source.Bounds.Owner

/-!
# Bounded lower analytic truncations

This file proves that the concrete lower truncation of a bounded analytic
complex is again represented by a bounded analytic complex.  The bound is
allowed to increase by the actual boundary degree object introduced by the
dual truncation construction.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- The uniform weight bound for the lower truncation of a bounded complex. -/
def additiveTruncLEBound
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    Nat :=
  Nat.max
    bound
    ((TraceAnalyticMotivicTStructure.additiveTruncLE
      cut
      complex.complex).degreeWeight cut)

/-- The original bound maps into the lower-truncation bound. -/
theorem additiveTruncLEBound_original_le
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    bound ≤
      TraceAnalyticMotivicTStructure.additiveTruncLEBound cut complex :=
  Nat.le_max_left
    bound
    ((TraceAnalyticMotivicTStructure.additiveTruncLE
      cut
      complex.complex).degreeWeight cut)

/-- The boundary degree weight maps into the lower-truncation bound. -/
theorem additiveTruncLEBound_boundary_le
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.additiveTruncLE
      cut
      complex.complex).degreeWeight cut ≤
      TraceAnalyticMotivicTStructure.additiveTruncLEBound cut complex :=
  Nat.le_max_right
    bound
    ((TraceAnalyticMotivicTStructure.additiveTruncLE
      cut
      complex.complex).degreeWeight cut)

/-- At a boundary tail degree, the lower truncation degree weight is bounded
by the enlarged lower-truncation bound. -/
theorem additiveTruncLE_degreeWeight_le_of_boundary
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree]
    (degree : ℤ)
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).r degree =
        some tail)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op.BoundaryGE
        tail) :
    (TraceAnalyticMotivicTStructure.additiveTruncLE
        cut
        complex.complex).degreeWeight degree ≤
      TraceAnalyticMotivicTStructure.additiveTruncLEBound cut complex :=
  let degree_eq_cut :
      degree = cut :=
    TraceAnalyticMotivicTStructure.truncLEEmbedding_boundary_degree_eq
      cut
      degree
      tail
      htail
      hboundary
  Eq.subst
    (motive := fun boundaryDegree =>
      (TraceAnalyticMotivicTStructure.additiveTruncLE
          cut
          complex.complex).degreeWeight boundaryDegree ≤
        TraceAnalyticMotivicTStructure.additiveTruncLEBound cut complex)
    (Eq.symm degree_eq_cut)
    (TraceAnalyticMotivicTStructure.additiveTruncLEBound_boundary_le
      cut
      complex)

/-- On a nonboundary lower-tail degree, the lower truncation degree weight is
bounded by the original bound and hence by the enlarged bound. -/
theorem additiveTruncLE_degreeWeight_le_of_not_boundary
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree]
    (degree : ℤ)
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).r degree =
        some tail)
    (hboundary :
      ¬ (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op.BoundaryGE
        tail) :
    (TraceAnalyticMotivicTStructure.additiveTruncLE
        cut
        complex.complex).degreeWeight degree ≤
      TraceAnalyticMotivicTStructure.additiveTruncLEBound cut complex :=
  let object_eq :
      (TraceAnalyticMotivicTStructure.additiveTruncLE
          cut
          complex.complex).objectAt degree =
        complex.complex.objectAt degree :=
    TraceAnalyticMotivicTStructure.additiveTruncLE_X_of_not_boundary
      cut
      complex.complex
      degree
      tail
      htail
      hboundary
  let original_le :
      complex.complex.degreeWeight degree ≤
        TraceAnalyticMotivicTStructure.additiveTruncLEBound cut complex :=
    Nat.le_trans
      (complex.degreeWeight_le degree)
      (TraceAnalyticMotivicTStructure.additiveTruncLEBound_original_le
        cut
        complex)
  Eq.subst
    (motive := fun weight =>
      weight ≤
        TraceAnalyticMotivicTStructure.additiveTruncLEBound cut complex)
    (Eq.trans
      (TraceAnalyticAdditiveCochainComplex.degreeWeight_eq
        (TraceAnalyticMotivicTStructure.additiveTruncLE
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

/-- Outside the lower tail, the lower truncation degree weight is zero and
hence bounded by the enlarged lower-truncation bound. -/
theorem additiveTruncLE_degreeWeight_le_of_r_eq_none
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree]
    (degree : ℤ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).r degree =
        none) :
    (TraceAnalyticMotivicTStructure.additiveTruncLE
        cut
        complex.complex).degreeWeight degree ≤
      TraceAnalyticMotivicTStructure.additiveTruncLEBound cut complex :=
  let object_eq :
      (TraceAnalyticMotivicTStructure.additiveTruncLE
          cut
          complex.complex).objectAt degree =
        TraceAnalyticAdditiveObject.zero :=
    TraceAnalyticMotivicTStructure.additiveTruncLE_X_of_r_eq_none
      cut
      complex.complex
      degree
      htail
  Eq.subst
    (motive := fun weight =>
      weight ≤
        TraceAnalyticMotivicTStructure.additiveTruncLEBound cut complex)
    (Eq.trans
      (TraceAnalyticAdditiveCochainComplex.degreeWeight_eq
        (TraceAnalyticMotivicTStructure.additiveTruncLE
          cut
          complex.complex)
        degree)
      (Eq.trans
        (congrArg TraceAnalyticAdditiveObject.weightLevel object_eq)
        TraceAnalyticAdditiveObject.weightLevel_zero))
    (Nat.zero_le
      (TraceAnalyticMotivicTStructure.additiveTruncLEBound cut complex))

/-- Every degree of the lower truncation of a bounded complex is bounded by
the enlarged lower-truncation bound. -/
theorem additiveTruncLE_degreeWeight_le
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree]
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.additiveTruncLE
        cut
        complex.complex).degreeWeight degree ≤
      TraceAnalyticMotivicTStructure.additiveTruncLEBound cut complex :=
  match htail :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).r degree with
  | none =>
      TraceAnalyticMotivicTStructure
        .additiveTruncLE_degreeWeight_le_of_r_eq_none
          cut
          complex
          degree
          htail
  | some tail =>
      if hboundary :
          (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op.BoundaryGE
            tail then
        TraceAnalyticMotivicTStructure
          .additiveTruncLE_degreeWeight_le_of_boundary
            cut
            complex
            degree
            tail
            htail
            hboundary
      else
        TraceAnalyticMotivicTStructure
          .additiveTruncLE_degreeWeight_le_of_not_boundary
            cut
            complex
            degree
            tail
            htail
            hboundary

/-- The lower analytic truncation of a bounded comparison-source complex is
again a bounded comparison-source complex, with the explicit enlarged bound
above. -/
def sourceAdditiveTruncLEWeightBoundedBy
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree] :
    TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
      (TraceAnalyticMotivicTStructure.additiveTruncLEBound cut complex) :=
  ⟨
    TraceAnalyticMotivicTStructure.additiveTruncLE cut complex.complex,
    TraceAnalyticMotivicTStructure.additiveTruncLE_degreeWeight_le
      cut
      complex
  ⟩

/-- The bounded lower-truncation representative has the concrete lower
truncation as its underlying complex. -/
theorem sourceAdditiveTruncLEWeightBoundedBy_complex
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.sourceAdditiveTruncLEWeightBoundedBy
        cut
        complex).complex =
      TraceAnalyticMotivicTStructure.additiveTruncLE cut complex.complex :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

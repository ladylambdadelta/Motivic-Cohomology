import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Weights.Source.Owner

/-!
# Source complex weights for analytic comparison

This file exposes the concrete degreewise weight profile of additive analytic
complexes and maps under comparison-source names.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Comparison-facing degree weight of an additive analytic complex. -/
def TraceAnalyticMotiveComparison.sourceComplexDegreeWeight
    (complex : TraceAnalyticAdditiveCochainComplex)
    (degree : ℤ) :
    Nat :=
  complex.degreeWeight degree

/-- Comparison-facing complex degree weight is the existing analytic degree
weight. -/
theorem TraceAnalyticMotiveComparison.sourceComplexDegreeWeight_eq_degreeWeight
    (complex : TraceAnalyticAdditiveCochainComplex)
    (degree : ℤ) :
    TraceAnalyticMotiveComparison.sourceComplexDegreeWeight complex degree =
      complex.degreeWeight degree :=
  rfl

/-- Comparison-facing complex degree weight is the weight of the object in that
degree. -/
theorem TraceAnalyticMotiveComparison.sourceComplexDegreeWeight_eq_objectAt
    (complex : TraceAnalyticAdditiveCochainComplex)
    (degree : ℤ) :
    TraceAnalyticMotiveComparison.sourceComplexDegreeWeight complex degree =
      TraceAnalyticMotiveComparison.sourceAdditiveObjectWeight
        (complex.objectAt degree) :=
  TraceAnalyticAdditiveCochainComplex.degreeWeight_eq complex degree

/-- Comparison-facing source weight of a differential. -/
def TraceAnalyticMotiveComparison.sourceDifferentialSourceWeight
    (complex : TraceAnalyticAdditiveCochainComplex)
    (sourceDegree targetDegree : ℤ) :
    Nat :=
  complex.differentialSourceWeight sourceDegree targetDegree

/-- Differential source weight is the comparison-source degree weight of the
source degree. -/
theorem TraceAnalyticMotiveComparison.sourceDifferentialSourceWeight_eq
    (complex : TraceAnalyticAdditiveCochainComplex)
    (sourceDegree targetDegree : ℤ) :
    TraceAnalyticMotiveComparison.sourceDifferentialSourceWeight
        complex
        sourceDegree
        targetDegree =
      TraceAnalyticMotiveComparison.sourceComplexDegreeWeight
        complex
        sourceDegree :=
  TraceAnalyticAdditiveCochainComplex.differentialSourceWeight_eq
    complex
    sourceDegree
    targetDegree

/-- Comparison-facing target weight of a differential. -/
def TraceAnalyticMotiveComparison.sourceDifferentialTargetWeight
    (complex : TraceAnalyticAdditiveCochainComplex)
    (sourceDegree targetDegree : ℤ) :
    Nat :=
  complex.differentialTargetWeight sourceDegree targetDegree

/-- Differential target weight is the comparison-source degree weight of the
target degree. -/
theorem TraceAnalyticMotiveComparison.sourceDifferentialTargetWeight_eq
    (complex : TraceAnalyticAdditiveCochainComplex)
    (sourceDegree targetDegree : ℤ) :
    TraceAnalyticMotiveComparison.sourceDifferentialTargetWeight
        complex
        sourceDegree
        targetDegree =
      TraceAnalyticMotiveComparison.sourceComplexDegreeWeight
        complex
        targetDegree :=
  TraceAnalyticAdditiveCochainComplex.differentialTargetWeight_eq
    complex
    sourceDegree
    targetDegree

/-- Comparison-facing source degree weight of an additive analytic chain map. -/
def TraceAnalyticMotiveComparison.sourceMapSourceDegreeWeight
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    (degree : ℤ) :
    Nat :=
  hom.sourceDegreeWeight degree

/-- Chain-map source degree weight is the comparison-source weight of the source
complex in that degree. -/
theorem TraceAnalyticMotiveComparison.sourceMapSourceDegreeWeight_eq
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    (degree : ℤ) :
    TraceAnalyticMotiveComparison.sourceMapSourceDegreeWeight hom degree =
      TraceAnalyticMotiveComparison.sourceComplexDegreeWeight source degree :=
  TraceAnalyticAdditiveCochainComplex.Hom.sourceDegreeWeight_eq
    hom
    degree

/-- Comparison-facing target degree weight of an additive analytic chain map. -/
def TraceAnalyticMotiveComparison.sourceMapTargetDegreeWeight
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    (degree : ℤ) :
    Nat :=
  hom.targetDegreeWeight degree

/-- Chain-map target degree weight is the comparison-source weight of the target
complex in that degree. -/
theorem TraceAnalyticMotiveComparison.sourceMapTargetDegreeWeight_eq
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    (degree : ℤ) :
    TraceAnalyticMotiveComparison.sourceMapTargetDegreeWeight hom degree =
      TraceAnalyticMotiveComparison.sourceComplexDegreeWeight target degree :=
  TraceAnalyticAdditiveCochainComplex.Hom.targetDegreeWeight_eq
    hom
    degree

end AnalyticMotives
end LFunctions
end Boundary

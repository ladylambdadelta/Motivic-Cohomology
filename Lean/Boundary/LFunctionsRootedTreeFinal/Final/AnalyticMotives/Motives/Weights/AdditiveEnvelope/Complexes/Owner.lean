import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Complexes.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Objects.Owner

/-!
# Weight levels of additive analytic complexes

An additive analytic complex has a concrete weight level in each cohomological
degree, computed from the finite trace-family object in that degree.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The weight level of an additive analytic complex in one degree. -/
def TraceAnalyticAdditiveCochainComplex.degreeWeight
    (complex : TraceAnalyticAdditiveCochainComplex)
    (degree : ℤ) :
    Nat :=
  (complex.objectAt degree).weightLevel

/-- Degree weight is the weight level of the object in that degree. -/
theorem TraceAnalyticAdditiveCochainComplex.degreeWeight_eq
    (complex : TraceAnalyticAdditiveCochainComplex)
    (degree : ℤ) :
    complex.degreeWeight degree =
      (complex.objectAt degree).weightLevel :=
  rfl

/-- The source weight level of a differential. -/
def TraceAnalyticAdditiveCochainComplex.differentialSourceWeight
    (complex : TraceAnalyticAdditiveCochainComplex)
    (sourceDegree targetDegree : ℤ) :
    Nat :=
  complex.degreeWeight sourceDegree

/-- The target weight level of a differential. -/
def TraceAnalyticAdditiveCochainComplex.differentialTargetWeight
    (complex : TraceAnalyticAdditiveCochainComplex)
    (sourceDegree targetDegree : ℤ) :
    Nat :=
  complex.degreeWeight targetDegree

/-- Differential source weight is the source degree weight. -/
theorem TraceAnalyticAdditiveCochainComplex.differentialSourceWeight_eq
    (complex : TraceAnalyticAdditiveCochainComplex)
    (sourceDegree targetDegree : ℤ) :
    complex.differentialSourceWeight sourceDegree targetDegree =
      complex.degreeWeight sourceDegree :=
  rfl

/-- Differential target weight is the target degree weight. -/
theorem TraceAnalyticAdditiveCochainComplex.differentialTargetWeight_eq
    (complex : TraceAnalyticAdditiveCochainComplex)
    (sourceDegree targetDegree : ℤ) :
    complex.differentialTargetWeight sourceDegree targetDegree =
      complex.degreeWeight targetDegree :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

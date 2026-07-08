import Mathlib.Algebra.Homology.HomologicalComplex
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Owner

/-!
# Analytic trace complexes

The first stable envelope of the concrete analytic trace-correspondence
category is the category of integer cochain complexes in `TraceCorQObject`.
The differentials are honest trace correspondences, so the stable layer remains
analytic rather than being replaced by a separate syntactic category.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The concrete category of integer cochain complexes in analytic trace correspondences. -/
abbrev TraceAnalyticCochainComplex :=
  CochainComplex TraceCorQObject ℤ

/-- A trace analytic cochain complex has trace-correspondence objects in each degree. -/
def TraceAnalyticCochainComplex.objectAt
    (complex : TraceAnalyticCochainComplex)
    (degree : ℤ) :
    TraceCorQObject :=
  complex.X degree

/-- A trace analytic cochain complex has trace-correspondence differentials. -/
def TraceAnalyticCochainComplex.differential
    (complex : TraceAnalyticCochainComplex)
    (sourceDegree targetDegree : ℤ) :
    complex.objectAt sourceDegree ⟶ complex.objectAt targetDegree :=
  complex.d sourceDegree targetDegree

/-- The object projection is the underlying homological-complex object field. -/
theorem TraceAnalyticCochainComplex.objectAt_eq
    (complex : TraceAnalyticCochainComplex)
    (degree : ℤ) :
    complex.objectAt degree =
      complex.X degree :=
  rfl

/-- The differential projection is the underlying homological-complex differential. -/
theorem TraceAnalyticCochainComplex.differential_eq
    (complex : TraceAnalyticCochainComplex)
    (sourceDegree targetDegree : ℤ) :
    complex.differential sourceDegree targetDegree =
      complex.d sourceDegree targetDegree :=
  rfl

/-- Analytic trace differentials square to zero. -/
theorem TraceAnalyticCochainComplex.differential_comp_differential
    (complex : TraceAnalyticCochainComplex)
    (first second third : ℤ) :
    complex.differential first second ≫
        complex.differential second third =
      0 :=
  HomologicalComplex.d_comp_d complex first second third

/-- The analytic trace cochain-complex category is the standard homological-complex category. -/
def TraceAnalyticCochainComplex.categoryStructure :
    CategoryTheory.Category TraceAnalyticCochainComplex :=
  inferInstance

end AnalyticMotives
end LFunctions
end Boundary

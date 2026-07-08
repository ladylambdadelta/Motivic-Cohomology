import Mathlib.Algebra.Homology.Embedding.IsSupported
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.Bounds.Owner

/-!
# Support criteria for derived analytic homological bounds

This file turns Mathlib support of cochain complexes along an embedding into
membership in the concrete homological bound predicates on derived analytic
motives.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- If a represented analytic abelian-envelope complex is supported on an
embedding, and every degree above the cut lies outside that embedding, then
its derived object is homologically `≤ cut`. -/
theorem homologicalLE_objectOf_of_isSupported
    {ι : Type*}
    {shape : ComplexShape ι}
    (embedding : shape.Embedding (ComplexShape.up ℤ))
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    [complex.IsSupported embedding]
    (houtside :
      ∀ degree : ℤ,
        cut < degree →
          ∀ index : ι,
            embedding.f index ≠ degree) :
    TraceAnalyticDerivedMotiveCategory.HomologicalLE
      cut
      (TraceAnalyticDerivedMotiveCategory.objectOf complex) :=
  TraceAnalyticDerivedMotiveCategory.homologicalLE_objectOf_of_exactAt
    cut
    complex
    (fun degree hcut =>
      complex.exactAt_of_isSupported
        embedding
        degree
        (houtside degree hcut))

/-- If a represented analytic abelian-envelope complex is supported on an
embedding, and every degree below the cut lies outside that embedding, then
its derived object is homologically `≥ cut`. -/
theorem homologicalGE_objectOf_of_isSupported
    {ι : Type*}
    {shape : ComplexShape ι}
    (embedding : shape.Embedding (ComplexShape.up ℤ))
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    [complex.IsSupported embedding]
    (houtside :
      ∀ degree : ℤ,
        degree < cut →
          ∀ index : ι,
            embedding.f index ≠ degree) :
    TraceAnalyticDerivedMotiveCategory.HomologicalGE
      cut
      (TraceAnalyticDerivedMotiveCategory.objectOf complex) :=
  TraceAnalyticDerivedMotiveCategory.homologicalGE_objectOf_of_exactAt
    cut
    complex
    (fun degree hcut =>
      complex.exactAt_of_isSupported
        embedding
        degree
        (houtside degree hcut))

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary

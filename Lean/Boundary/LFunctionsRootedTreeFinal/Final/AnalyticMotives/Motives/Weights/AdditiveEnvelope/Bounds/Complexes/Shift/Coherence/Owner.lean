import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Complexes.Shift.Maps.Owner

/-!
# Coherence isomorphisms for shifted bounded complexes

The concrete shifted bounded representatives inherit the zero-shift and
additive-shift comparison isomorphisms from Mathlib's cochain-complex shifts.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The zero shift of a bounded complex is isomorphic to the original complex. -/
def TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.shiftZeroIso
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound) :
    (complex.shift (0 : ℤ)).complex ≅ complex.complex :=
  (CochainComplex.shiftFunctorZero'
    TraceAnalyticAdditiveCategoryObject
    (0 : ℤ)
    rfl).app complex.complex

/-- The zero-shift comparison is Mathlib's cochain-complex zero-shift isomorphism. -/
theorem TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.shiftZeroIso_eq
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound) :
    complex.shiftZeroIso =
      (CochainComplex.shiftFunctorZero'
        TraceAnalyticAdditiveCategoryObject
        (0 : ℤ)
        rfl).app complex.complex :=
  rfl

/-- The zero-shift comparison is natural for bounded chain maps. -/
theorem TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom.shiftZeroIso_naturality
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    hom.shift (0 : ℤ) ≫ target.shiftZeroIso.hom =
      source.shiftZeroIso.hom ≫ hom :=
  (CochainComplex.shiftFunctorZero'
    TraceAnalyticAdditiveCategoryObject
    (0 : ℤ)
    rfl).hom.naturality hom

/-- Shifting by a sum is isomorphic to shifting successively. -/
def TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.shiftAddIso
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound)
    (first second : ℤ) :
    (complex.shift (first + second)).complex ≅
      ((complex.shift first).shift second).complex :=
  (CochainComplex.shiftFunctorAdd'
    TraceAnalyticAdditiveCategoryObject
    first
    second
    (first + second)
    rfl).app complex.complex

/-- The additive-shift comparison is Mathlib's cochain-complex shift-add isomorphism. -/
theorem TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.shiftAddIso_eq
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound)
    (first second : ℤ) :
    complex.shiftAddIso first second =
      (CochainComplex.shiftFunctorAdd'
        TraceAnalyticAdditiveCategoryObject
        first
        second
        (first + second)
        rfl).app complex.complex :=
  rfl

/-- The additive-shift comparison is natural for bounded chain maps. -/
theorem TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom.shiftAddIso_naturality
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (first second : ℤ) :
    hom.shift (first + second) ≫ target.shiftAddIso first second.hom =
      source.shiftAddIso first second.hom ≫ (hom.shift first).shift second :=
  (CochainComplex.shiftFunctorAdd'
    TraceAnalyticAdditiveCategoryObject
    first
    second
    (first + second)
    rfl).hom.naturality hom

end AnalyticMotives
end LFunctions
end Boundary

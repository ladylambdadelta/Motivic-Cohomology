import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.NullSubcategory.Owner

/-!
# Contractible additive analytic complexes

This file connects Mathlib's homotopy-category contractibility criterion to
the analytic stable null subcategory.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Limits

/-- A contracting homotopy of the identity makes the homotopy image of an
additive analytic cochain complex a zero object. -/
theorem TraceAnalyticAdditiveHomotopyCategory.isZero_objectOf_of_contractible
    (complex : TraceAnalyticAdditiveCochainComplex)
    (contractible : Nonempty (Homotopy (𝟙 complex) 0)) :
    IsZero (TraceAnalyticAdditiveHomotopyCategory.objectOf complex) :=
  (HomotopyCategory.isZero_quotient_obj_iff complex).2 contractible

/-- A contractible additive analytic cochain complex represents an object of
the stable null subcategory. -/
theorem TraceAnalyticStableNullSubcategory.objectOf_mem_of_contractible
    (complex : TraceAnalyticAdditiveCochainComplex)
    (contractible : Nonempty (Homotopy (𝟙 complex) 0)) :
    TraceAnalyticStableNullSubcategory.P
      (TraceAnalyticAdditiveHomotopyCategory.objectOf complex) :=
  CategoryTheory.mem_of_iso
    (P := TraceAnalyticStableNullSubcategory.P)
    ((TraceAnalyticAdditiveHomotopyCategory
      .isZero_objectOf_of_contractible complex contractible).isoZero.symm)
    TraceAnalyticStableNullObject.zero_mem

/-- A complex homotopy equivalent to a contractible complex represents an
object of the stable null subcategory. -/
theorem TraceAnalyticStableNullSubcategory.objectOf_mem_of_homotopyEquiv_contractible
    (source target : TraceAnalyticAdditiveCochainComplex)
    (equiv : HomotopyEquiv source target)
    (contractible : Nonempty (Homotopy (𝟙 target) 0)) :
    TraceAnalyticStableNullSubcategory.P
      (TraceAnalyticAdditiveHomotopyCategory.objectOf source) :=
  CategoryTheory.mem_of_iso
    (P := TraceAnalyticStableNullSubcategory.P)
    ((HomotopyCategory.isoOfHomotopyEquiv equiv).symm)
    (TraceAnalyticStableNullSubcategory.objectOf_mem_of_contractible
      target
      contractible)

/-- The mapping cone of the identity map is contractible. -/
theorem TraceAnalyticAdditiveHomotopyCategory.identityMappingCone_contractible
    (complex : TraceAnalyticAdditiveCochainComplex) :
    Nonempty
      (Homotopy
        (𝟙 (CochainComplex.mappingCone (𝟙 complex)))
        0) :=
  ⟨CochainComplex.mappingCone.homotopyToZeroOfId complex⟩

/-- A complex homotopy equivalent to the mapping cone of an identity map
represents an object of the stable null subcategory. -/
theorem TraceAnalyticStableNullSubcategory.objectOf_mem_of_homotopyEquiv_identityCone
    (source target : TraceAnalyticAdditiveCochainComplex)
    (equiv :
      HomotopyEquiv
        source
        (CochainComplex.mappingCone (𝟙 target))) :
    TraceAnalyticStableNullSubcategory.P
      (TraceAnalyticAdditiveHomotopyCategory.objectOf source) :=
  TraceAnalyticStableNullSubcategory.objectOf_mem_of_homotopyEquiv_contractible
    source
    (CochainComplex.mappingCone (𝟙 target))
    equiv
    (TraceAnalyticAdditiveHomotopyCategory.identityMappingCone_contractible
      target)

/-- A complex isomorphic to the mapping cone of an identity map represents an
object of the stable null subcategory. -/
theorem TraceAnalyticStableNullSubcategory.objectOf_mem_of_iso_identityCone
    (source target : TraceAnalyticAdditiveCochainComplex)
    (iso :
      source ≅ CochainComplex.mappingCone (𝟙 target)) :
    TraceAnalyticStableNullSubcategory.P
      (TraceAnalyticAdditiveHomotopyCategory.objectOf source) :=
  TraceAnalyticStableNullSubcategory.objectOf_mem_of_homotopyEquiv_identityCone
    source
    target
    (HomotopyEquiv.ofIso iso)

end AnalyticMotives
end LFunctions
end Boundary

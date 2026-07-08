import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Shift.ShortComplex.Comparison.Components.Identities.Owner

/-!
# Vertex isomorphisms of the shifted short-complex comparison

The named forward and inverse component maps assemble into isomorphisms on the
three vertices of the shifted short-complex comparison.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The left vertex isomorphism of the shifted short-complex comparison. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₁
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplex
      hom
      shift).X₁ ≅
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedMapShortComplexTransported
        hom
        shift).X₁ where
  hom :=
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_hom₁
      hom
      shift
  inv :=
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_inv₁
      hom
      shift
  hom_inv_id :=
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_hom₁_comp_inv₁
      hom
      shift
  inv_hom_id :=
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_inv₁_comp_hom₁
      hom
      shift

/-- The middle vertex isomorphism of the shifted short-complex comparison. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₂
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplex
      hom
      shift).X₂ ≅
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedMapShortComplexTransported
        hom
        shift).X₂ where
  hom :=
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_hom₂
      hom
      shift
  inv :=
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_inv₂
      hom
      shift
  hom_inv_id :=
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_hom₂_comp_inv₂
      hom
      shift
  inv_hom_id :=
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_inv₂_comp_hom₂
      hom
      shift

/-- The right vertex isomorphism of the shifted short-complex comparison. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₃
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplex
      hom
      shift).X₃ ≅
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedMapShortComplexTransported
        hom
        shift).X₃ where
  hom :=
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_hom₃
      hom
      shift
  inv :=
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_inv₃
      hom
      shift
  hom_inv_id :=
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_hom₃_comp_inv₃
      hom
      shift
  inv_hom_id :=
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_inv₃_comp_hom₃
      hom
      shift

/-- The left vertex isomorphism has the named left component as its forward map. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₁_hom
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₁
      hom
      shift).hom =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_hom₁
        hom
        shift :=
  rfl

/-- The middle vertex isomorphism has the named middle component as its forward map. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₂_hom
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₂
      hom
      shift).hom =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_hom₂
        hom
        shift :=
  rfl

/-- The right vertex isomorphism has the named right component as its forward map. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₃_hom
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₃
      hom
      shift).hom =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_hom₃
        hom
        shift :=
  rfl

/-- The left vertex isomorphism has the named left inverse component as its inverse map. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₁_inv
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₁
      hom
      shift).inv =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_inv₁
        hom
        shift :=
  rfl

/-- The middle vertex isomorphism has the named middle inverse component as its inverse map. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₂_inv
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₂
      hom
      shift).inv =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_inv₂
        hom
        shift :=
  rfl

/-- The right vertex isomorphism has the named right inverse component as its inverse map. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₃_inv
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₃
      hom
      shift).inv =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_inv₃
        hom
        shift :=
  rfl

/-- The left vertex isomorphism is the first projection of the short-complex isomorphism. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₁_eq_π₁
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₁
        hom
        shift =
      ShortComplex.π₁.mapIso
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap
          hom
          shift) :=
  rfl

/-- The middle vertex isomorphism is the second projection of the short-complex isomorphism. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₂_eq_π₂
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₂
        hom
        shift =
      ShortComplex.π₂.mapIso
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap
          hom
          shift) :=
  rfl

/-- The right vertex isomorphism is the third projection of the short-complex isomorphism. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₃_eq_π₃
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₃
        hom
        shift =
      ShortComplex.π₃.mapIso
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap
          hom
          shift) :=
  rfl

/-- The left vertex isomorphism is the first triangle-vertex projection of the
shifted mapping-cone triangle isomorphism. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₁_eq_triangleπ₁
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₁
        hom
        shift =
      Triangle.π₁.mapIso
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedTriangleIsoShiftedMap
          hom
          shift) :=
  Eq.trans
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₁_eq_π₁
      hom
      shift)
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_π₁
      hom
      shift)

/-- The middle vertex isomorphism is the second triangle-vertex projection of the
shifted mapping-cone triangle isomorphism. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₂_eq_triangleπ₂
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₂
        hom
        shift =
      Triangle.π₂.mapIso
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedTriangleIsoShiftedMap
          hom
          shift) :=
  Eq.trans
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₂_eq_π₂
      hom
      shift)
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_π₂
      hom
      shift)

/-- The right vertex isomorphism is the third triangle-vertex projection of the
shifted mapping-cone triangle isomorphism. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₃_eq_triangleπ₃
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₃
        hom
        shift =
      Triangle.π₃.mapIso
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedTriangleIsoShiftedMap
          hom
          shift) :=
  Eq.trans
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₃_eq_π₃
      hom
      shift)
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_π₃
      hom
      shift)

/-- The left vertex forward map is the forward map of the first triangle projection. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₁_hom_eq_triangleπ₁_hom
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₁
      hom
      shift).hom =
      (Triangle.π₁.mapIso
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedTriangleIsoShiftedMap
          hom
          shift)).hom :=
  congrArg
    (fun iso => iso.hom)
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₁_eq_triangleπ₁
      hom
      shift)

/-- The middle vertex forward map is the forward map of the second triangle projection. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₂_hom_eq_triangleπ₂_hom
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₂
      hom
      shift).hom =
      (Triangle.π₂.mapIso
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedTriangleIsoShiftedMap
          hom
          shift)).hom :=
  congrArg
    (fun iso => iso.hom)
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₂_eq_triangleπ₂
      hom
      shift)

/-- The right vertex forward map is the forward map of the third triangle projection. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₃_hom_eq_triangleπ₃_hom
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₃
      hom
      shift).hom =
      (Triangle.π₃.mapIso
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedTriangleIsoShiftedMap
          hom
          shift)).hom :=
  congrArg
    (fun iso => iso.hom)
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₃_eq_triangleπ₃
      hom
      shift)

/-- The left vertex inverse map is the inverse map of the first triangle projection. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₁_inv_eq_triangleπ₁_inv
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₁
      hom
      shift).inv =
      (Triangle.π₁.mapIso
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedTriangleIsoShiftedMap
          hom
          shift)).inv :=
  congrArg
    (fun iso => iso.inv)
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₁_eq_triangleπ₁
      hom
      shift)

/-- The middle vertex inverse map is the inverse map of the second triangle projection. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₂_inv_eq_triangleπ₂_inv
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₂
      hom
      shift).inv =
      (Triangle.π₂.mapIso
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedTriangleIsoShiftedMap
          hom
          shift)).inv :=
  congrArg
    (fun iso => iso.inv)
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₂_eq_triangleπ₂
      hom
      shift)

/-- The right vertex inverse map is the inverse map of the third triangle projection. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₃_inv_eq_triangleπ₃_inv
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₃
      hom
      shift).inv =
      (Triangle.π₃.mapIso
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedTriangleIsoShiftedMap
          hom
          shift)).inv :=
  congrArg
    (fun iso => iso.inv)
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_iso₃_eq_triangleπ₃
      hom
      shift)

end AnalyticMotives
end LFunctions
end Boundary

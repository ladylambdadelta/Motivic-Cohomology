import Boundary.ComponentGeometry
import Boundary.Localization

/-!
# A1 Homotopy Targets For Presheaves With Transfers

This file records typed representable `A1`-homotopy data together with the
chosen transfer maps whose projection maps are used as localization generators.
-/

universe u

variable {k : Type u} [Field k] [PerfectField k]

open AlgebraicGeometry CategoryTheory

namespace Boundary

noncomputable section

/-- Typed representable `A1`-homotopy data consisting of a base object, a
chosen cylinder, and the transfer data needed to express the interval
projection on representables. -/
structure A1RepresentableHomotopyDataQ (category : SmCorQ (k := k)) where
  base : Geometry.SmSchemeOver k
  cylinder : Geometry.SmSchemeOver k
  projection : cylinder ⟶ base
  zeroSection : base ⟶ cylinder
  oneSection : base ⟶ cylinder
  projectionTransfer : SmCorQ.Hom category cylinder base
  zeroSectionTransfer : SmCorQ.Hom category base cylinder
  oneSectionTransfer : SmCorQ.Hom category base cylinder
  zeroSectionRetractionTarget :
    category.comp zeroSectionTransfer projectionTransfer = category.id base
  oneSectionRetractionTarget :
    category.comp oneSectionTransfer projectionTransfer = category.id base

namespace A1RepresentableHomotopyDataQ

def sourcePresheaf {category : SmCorQ (k := k)}
    (witness : A1RepresentableHomotopyDataQ category) :
    PST category :=
  Qtr (category := category) witness.cylinder

def targetPresheaf {category : SmCorQ (k := k)}
    (witness : A1RepresentableHomotopyDataQ category) :
    PST category :=
  Qtr (category := category) witness.base

/-- The `A1` localization map attached to a witness: the projection from the
chosen cylinder to the base. -/
def homotopyMap {category : SmCorQ (k := k)}
    (witness : A1RepresentableHomotopyDataQ category) :
    witness.sourcePresheaf ⟶ witness.targetPresheaf :=
  QtrMap (category := category) witness.projectionTransfer

def zeroSectionMap {category : SmCorQ (k := k)}
    (witness : A1RepresentableHomotopyDataQ category) :
    witness.targetPresheaf ⟶ witness.sourcePresheaf :=
  QtrMap (category := category) witness.zeroSectionTransfer

def oneSectionMap {category : SmCorQ (k := k)}
    (witness : A1RepresentableHomotopyDataQ category) :
    witness.targetPresheaf ⟶ witness.sourcePresheaf :=
  QtrMap (category := category) witness.oneSectionTransfer

@[simp] theorem zeroSection_retraction
    {category : SmCorQ (k := k)}
  (witness : A1RepresentableHomotopyDataQ category) :
    witness.zeroSectionMap ≫ witness.homotopyMap = 𝟙 witness.targetPresheaf := by
  refine CategoryTheory.NatTrans.ext (funext fun Z => ?_)
  apply LinearMap.ext
  intro g
  change category.comp (category.comp g witness.zeroSectionTransfer)
      witness.projectionTransfer = g
  rw [category.assoc, witness.zeroSectionRetractionTarget, category.comp_id]

@[simp] theorem oneSection_retraction
    {category : SmCorQ (k := k)}
  (witness : A1RepresentableHomotopyDataQ category) :
    witness.oneSectionMap ≫ witness.homotopyMap = 𝟙 witness.targetPresheaf := by
  refine CategoryTheory.NatTrans.ext (funext fun Z => ?_)
  apply LinearMap.ext
  intro g
  change category.comp (category.comp g witness.oneSectionTransfer)
      witness.projectionTransfer = g
  rw [category.assoc, witness.oneSectionRetractionTarget, category.comp_id]

end A1RepresentableHomotopyDataQ

/-- Honest locality predicate relative to chosen representable `A1`-homotopy
data: a presheaf sends the selected projection map to an isomorphism. -/
def IsA1LocalAtRepresentableDataQ {category : SmCorQ (k := k)}
  (F : PST category) (data : A1RepresentableHomotopyDataQ category) := by
  letI := SmCorQCat category
  exact CategoryTheory.IsIso (F.map (Quiver.Hom.op data.projectionTransfer))

/-- Exact geometric data for the affine-line product and projection. -/
structure A1GeometryDataQ where
  affineLine : Geometry.SmSchemeOver k
  productObj : Geometry.SmSchemeOver k → Geometry.SmSchemeOver k
  productIsoToOverBaseProduct :
    ∀ X : Geometry.SmSchemeOver k,
      (productObj X).scheme ≅ overBaseProduct X affineLine
  projection :
    (X : Geometry.SmSchemeOver k) → productObj X ⟶ X
  projection_hom_eq_fst :
    ∀ X : Geometry.SmSchemeOver k,
      (projection X).hom =
        (productIsoToOverBaseProduct X).hom ≫ overBaseProduct.fst X affineLine

namespace A1GeometryDataQ

def productProjection {geometry : A1GeometryDataQ (k := k)}
    (X : Geometry.SmSchemeOver k) : geometry.productObj X ⟶ X :=
  geometry.projection X

end A1GeometryDataQ

/-- A chosen affine-line geometry package together with transfer morphisms used
as the projection maps `X × A1 → X` for all smooth `X`. -/
structure A1ProjectionTransferFamilyQ (category : SmCorQ (k := k)) where
  geometry : A1GeometryDataQ (k := k)
  projectionTransfer :
    (X : Geometry.SmSchemeOver k) → SmCorQ.Hom category (geometry.productObj X) X

namespace A1ProjectionTransferFamilyQ

def inducedMap {category : SmCorQ (k := k)}
    (family : A1ProjectionTransferFamilyQ category)
  (F : PST category) (X : Geometry.SmSchemeOver k) := by
  letI := SmCorQCat category
  exact F.map (Quiver.Hom.op (family.projectionTransfer X))

end A1ProjectionTransferFamilyQ

/-- Family of representable `A1` generators feeding the transfer-presheaf
localization construction. -/
structure A1LocalizationTargetQ (category : SmCorQ (k := k)) where
  Witness : Type (u + 1)
  witness : Witness → A1RepresentableHomotopyDataQ category

namespace A1LocalizationTargetQ

def toLocalizingMorphisms {category : SmCorQ (k := k)}
    (presentation : A1LocalizationTargetQ category) :
    LocalizingMorphismPresentationQ category where
  Generator := presentation.Witness
  data := fun index =>
    ⟨(presentation.witness index).sourcePresheaf,
      (presentation.witness index).targetPresheaf,
      (presentation.witness index).homotopyMap⟩

end A1LocalizationTargetQ

end

end Boundary

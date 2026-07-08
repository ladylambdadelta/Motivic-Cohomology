import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.Contractible.IdentityCone.IsIso.Maps.Owner

/-!
# Composites of the identity-cone comparison maps

This file names the two composites of the mapping-cone maps associated to an
isomorphism and records the commutative-square data for their single-map
normal forms.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticAdditiveHomotopyCategory

/-- The composite from the cone of an isomorphism to itself through the
identity cone. -/
def mappingConeIsoIdentityConeForwardBackwardComposite
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    [IsIso hom] :
    CochainComplex.mappingCone hom ⟶ CochainComplex.mappingCone hom :=
  TraceAnalyticAdditiveHomotopyCategory.mappingConeIsoToIdentityConeMap hom ≫
    TraceAnalyticAdditiveHomotopyCategory.identityConeToMappingConeIsoMap hom

/-- The composite from the identity cone to itself through the cone of an
isomorphism. -/
def mappingConeIsoIdentityConeBackwardForwardComposite
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    [IsIso hom] :
    CochainComplex.mappingCone (𝟙 target) ⟶
      CochainComplex.mappingCone (𝟙 target) :=
  TraceAnalyticAdditiveHomotopyCategory.identityConeToMappingConeIsoMap hom ≫
    TraceAnalyticAdditiveHomotopyCategory.mappingConeIsoToIdentityConeMap hom

/-- The commutative square for the single-map normal form of the forward-then-
backward composite. -/
theorem mappingConeIsoForwardBackwardSingleMap_comm
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    [IsIso hom] :
    hom ≫ (𝟙 target ≫ 𝟙 target) =
      (hom ≫ inv hom) ≫ hom :=
  Eq.trans
    (congrArg (fun right => hom ≫ right) (Category.id_comp (𝟙 target)))
    (Eq.trans
      (Category.comp_id hom)
      (Eq.trans
        (Eq.symm (Category.id_comp hom))
        (congrArg
          (fun left => left ≫ hom)
          (Eq.symm (IsIso.hom_inv_id hom)))))

/-- The commutative square for the single-map normal form of the backward-then-
forward composite. -/
theorem mappingConeIsoBackwardForwardSingleMap_comm
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    [IsIso hom] :
    𝟙 target ≫ (𝟙 target ≫ 𝟙 target) =
      (inv hom ≫ hom) ≫ 𝟙 target :=
  Eq.trans
    (congrArg (fun right => 𝟙 target ≫ right) (Category.id_comp (𝟙 target)))
    (Eq.trans
      (Category.id_comp (𝟙 target))
      (Eq.trans
        (Eq.symm (Category.comp_id (𝟙 target)))
        (congrArg
          (fun left => left ≫ 𝟙 target)
          (Eq.symm (IsIso.inv_hom_id hom)))))

/-- The single `mappingCone.map` expression associated to the forward-then-
backward composite. -/
def mappingConeIsoForwardBackwardSingleMap
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    [IsIso hom] :
    CochainComplex.mappingCone hom ⟶ CochainComplex.mappingCone hom :=
  CochainComplex.mappingCone.map
    hom
    hom
    (hom ≫ inv hom)
    (𝟙 target ≫ 𝟙 target)
    (TraceAnalyticAdditiveHomotopyCategory
      .mappingConeIsoForwardBackwardSingleMap_comm hom)

/-- The single `mappingCone.map` expression associated to the backward-then-
forward composite. -/
def mappingConeIsoBackwardForwardSingleMap
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    [IsIso hom] :
    CochainComplex.mappingCone (𝟙 target) ⟶
      CochainComplex.mappingCone (𝟙 target) :=
  CochainComplex.mappingCone.map
    (𝟙 target)
    (𝟙 target)
    (inv hom ≫ hom)
    (𝟙 target ≫ 𝟙 target)
    (TraceAnalyticAdditiveHomotopyCategory
      .mappingConeIsoBackwardForwardSingleMap_comm hom)

/-- The forward-then-backward composite is its single-map normal form. -/
theorem mappingConeIsoForwardBackwardComposite_eq_singleMap
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    [IsIso hom] :
    TraceAnalyticAdditiveHomotopyCategory
        .mappingConeIsoIdentityConeForwardBackwardComposite hom =
      TraceAnalyticAdditiveHomotopyCategory
        .mappingConeIsoForwardBackwardSingleMap hom :=
  Eq.symm
    (CochainComplex.mappingCone.map_comp
      (φ₁ := hom)
      (φ₂ := 𝟙 target)
      (φ₃ := hom)
      (a := hom)
      (b := 𝟙 target)
      (comm :=
        TraceAnalyticAdditiveHomotopyCategory
          .mappingConeIsoToIdentityCone_comm hom)
      (a' := inv hom)
      (b' := 𝟙 target)
      (TraceAnalyticAdditiveHomotopyCategory
        .identityConeToMappingConeIso_comm hom))

/-- The backward-then-forward composite is its single-map normal form. -/
theorem mappingConeIsoBackwardForwardComposite_eq_singleMap
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    [IsIso hom] :
    TraceAnalyticAdditiveHomotopyCategory
        .mappingConeIsoIdentityConeBackwardForwardComposite hom =
      TraceAnalyticAdditiveHomotopyCategory
        .mappingConeIsoBackwardForwardSingleMap hom :=
  Eq.symm
    (CochainComplex.mappingCone.map_comp
      (φ₁ := 𝟙 target)
      (φ₂ := hom)
      (φ₃ := 𝟙 target)
      (a := inv hom)
      (b := 𝟙 target)
      (comm :=
        TraceAnalyticAdditiveHomotopyCategory
          .identityConeToMappingConeIso_comm hom)
      (a' := hom)
      (b' := 𝟙 target)
      (TraceAnalyticAdditiveHomotopyCategory
        .mappingConeIsoToIdentityCone_comm hom))

/-- The commutative square for the identity single-map normal form on the cone
of an isomorphism. -/
theorem mappingConeIsoForwardBackwardIdentitySingleMap_comm
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    [IsIso hom] :
    hom ≫ 𝟙 target = 𝟙 source ≫ hom :=
  Eq.trans
    (Category.comp_id hom)
    (Eq.symm (Category.id_comp hom))

/-- The commutative square for the identity single-map normal form on the
identity cone. -/
theorem mappingConeIsoBackwardForwardIdentitySingleMap_comm
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    [IsIso hom] :
    𝟙 target ≫ 𝟙 target = 𝟙 target ≫ 𝟙 target :=
  rfl

/-- The identity single-map normal form on the cone of an isomorphism. -/
def mappingConeIsoForwardBackwardIdentitySingleMap
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    [IsIso hom] :
    CochainComplex.mappingCone hom ⟶ CochainComplex.mappingCone hom :=
  CochainComplex.mappingCone.map
    hom
    hom
    (𝟙 source)
    (𝟙 target)
    (TraceAnalyticAdditiveHomotopyCategory
      .mappingConeIsoForwardBackwardIdentitySingleMap_comm hom)

/-- The identity single-map normal form on the identity cone. -/
def mappingConeIsoBackwardForwardIdentitySingleMap
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    [IsIso hom] :
    CochainComplex.mappingCone (𝟙 target) ⟶
      CochainComplex.mappingCone (𝟙 target) :=
  CochainComplex.mappingCone.map
    (𝟙 target)
    (𝟙 target)
    (𝟙 target)
    (𝟙 target)
    (TraceAnalyticAdditiveHomotopyCategory
      .mappingConeIsoBackwardForwardIdentitySingleMap_comm hom)

/-- The commutative square after replacing only the source component in the
forward-then-backward single-map normal form by an identity. -/
theorem mappingConeIsoForwardBackwardSourceIdentitySingleMap_comm
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    [IsIso hom] :
    hom ≫ (𝟙 target ≫ 𝟙 target) =
      𝟙 source ≫ hom :=
  Eq.trans
    (congrArg (fun right => hom ≫ right) (Category.id_comp (𝟙 target)))
    (Eq.trans
      (Category.comp_id hom)
      (Eq.symm (Category.id_comp hom)))

/-- The commutative square after replacing only the source component in the
backward-then-forward single-map normal form by an identity. -/
theorem mappingConeIsoBackwardForwardSourceIdentitySingleMap_comm
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    [IsIso hom] :
    𝟙 target ≫ (𝟙 target ≫ 𝟙 target) =
      𝟙 target ≫ 𝟙 target :=
  congrArg
    (fun right => 𝟙 target ≫ right)
    (Category.id_comp (𝟙 target))

/-- The forward-then-backward single-map normal form after replacing the source
component by an identity but before replacing the target component. -/
def mappingConeIsoForwardBackwardSourceIdentitySingleMap
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    [IsIso hom] :
    CochainComplex.mappingCone hom ⟶ CochainComplex.mappingCone hom :=
  CochainComplex.mappingCone.map
    hom
    hom
    (𝟙 source)
    (𝟙 target ≫ 𝟙 target)
    (TraceAnalyticAdditiveHomotopyCategory
      .mappingConeIsoForwardBackwardSourceIdentitySingleMap_comm hom)

/-- The backward-then-forward single-map normal form after replacing the source
component by an identity but before replacing the target component. -/
def mappingConeIsoBackwardForwardSourceIdentitySingleMap
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    [IsIso hom] :
    CochainComplex.mappingCone (𝟙 target) ⟶
      CochainComplex.mappingCone (𝟙 target) :=
  CochainComplex.mappingCone.map
    (𝟙 target)
    (𝟙 target)
    (𝟙 target)
    (𝟙 target ≫ 𝟙 target)
    (TraceAnalyticAdditiveHomotopyCategory
      .mappingConeIsoBackwardForwardSourceIdentitySingleMap_comm hom)

/-- The actual identity morphism on the cone of an isomorphism. -/
def mappingConeIsoForwardBackwardIdentityMorphism
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    [IsIso hom] :
    CochainComplex.mappingCone hom ⟶ CochainComplex.mappingCone hom :=
  𝟙 (CochainComplex.mappingCone hom)

/-- The actual identity morphism on the identity cone of the target. -/
def mappingConeIsoBackwardForwardIdentityMorphism
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    [IsIso hom] :
    CochainComplex.mappingCone (𝟙 target) ⟶
      CochainComplex.mappingCone (𝟙 target) :=
  𝟙 (CochainComplex.mappingCone (𝟙 target))

/-- Projection formula for the actual identity morphism on the cone of an
isomorphism. -/
theorem mappingConeIsoForwardBackwardIdentityMorphism_eq
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    [IsIso hom] :
    TraceAnalyticAdditiveHomotopyCategory
        .mappingConeIsoForwardBackwardIdentityMorphism hom =
      𝟙 (CochainComplex.mappingCone hom) :=
  rfl

/-- Projection formula for the actual identity morphism on the identity cone of
the target. -/
theorem mappingConeIsoBackwardForwardIdentityMorphism_eq
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    [IsIso hom] :
    TraceAnalyticAdditiveHomotopyCategory
        .mappingConeIsoBackwardForwardIdentityMorphism hom =
      𝟙 (CochainComplex.mappingCone (𝟙 target)) :=
  rfl

/-- Source-component equality for the forward-then-backward single-map normal
form. -/
theorem mappingConeIsoForwardBackwardSingleMap_sourceComponent_eq_identity
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    [IsIso hom] :
    hom ≫ inv hom = 𝟙 source :=
  IsIso.hom_inv_id hom

/-- Target-component equality for the forward-then-backward single-map normal
form. -/
theorem mappingConeIsoForwardBackwardSingleMap_targetComponent_eq_identity
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    [IsIso hom] :
    𝟙 target ≫ 𝟙 target = 𝟙 target :=
  Category.id_comp (𝟙 target)

/-- Source-component equality for the backward-then-forward single-map normal
form. -/
theorem mappingConeIsoBackwardForwardSingleMap_sourceComponent_eq_identity
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    [IsIso hom] :
    inv hom ≫ hom = 𝟙 target :=
  IsIso.inv_hom_id hom

/-- Target-component equality for the backward-then-forward single-map normal
form. -/
theorem mappingConeIsoBackwardForwardSingleMap_targetComponent_eq_identity
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    [IsIso hom] :
    𝟙 target ≫ 𝟙 target = 𝟙 target :=
  Category.id_comp (𝟙 target)

/-- Replacing the source component in the forward-then-backward single-map
normal form gives the source-identity intermediate map. -/
theorem mappingConeIsoForwardBackwardSingleMap_eq_sourceIdentitySingleMap
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    [IsIso hom] :
    TraceAnalyticAdditiveHomotopyCategory
        .mappingConeIsoForwardBackwardSingleMap hom =
      TraceAnalyticAdditiveHomotopyCategory
        .mappingConeIsoForwardBackwardSourceIdentitySingleMap hom :=
  match
    TraceAnalyticAdditiveHomotopyCategory
      .mappingConeIsoForwardBackwardSingleMap_sourceComponent_eq_identity hom
  with
  | rfl => rfl

/-- Replacing the target component in the forward-then-backward source-identity
intermediate map gives the identity single-map normal form. -/
theorem mappingConeIsoForwardBackwardSourceIdentitySingleMap_eq_identitySingleMap
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    [IsIso hom] :
    TraceAnalyticAdditiveHomotopyCategory
        .mappingConeIsoForwardBackwardSourceIdentitySingleMap hom =
      TraceAnalyticAdditiveHomotopyCategory
        .mappingConeIsoForwardBackwardIdentitySingleMap hom :=
  match
    TraceAnalyticAdditiveHomotopyCategory
      .mappingConeIsoForwardBackwardSingleMap_targetComponent_eq_identity hom
  with
  | rfl => rfl

/-- Replacing the source component in the backward-then-forward single-map
normal form gives the source-identity intermediate map. -/
theorem mappingConeIsoBackwardForwardSingleMap_eq_sourceIdentitySingleMap
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    [IsIso hom] :
    TraceAnalyticAdditiveHomotopyCategory
        .mappingConeIsoBackwardForwardSingleMap hom =
      TraceAnalyticAdditiveHomotopyCategory
        .mappingConeIsoBackwardForwardSourceIdentitySingleMap hom :=
  match
    TraceAnalyticAdditiveHomotopyCategory
      .mappingConeIsoBackwardForwardSingleMap_sourceComponent_eq_identity hom
  with
  | rfl => rfl

/-- Replacing the target component in the backward-then-forward source-identity
intermediate map gives the identity single-map normal form. -/
theorem mappingConeIsoBackwardForwardSourceIdentitySingleMap_eq_identitySingleMap
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    [IsIso hom] :
    TraceAnalyticAdditiveHomotopyCategory
        .mappingConeIsoBackwardForwardSourceIdentitySingleMap hom =
      TraceAnalyticAdditiveHomotopyCategory
        .mappingConeIsoBackwardForwardIdentitySingleMap hom :=
  match
    TraceAnalyticAdditiveHomotopyCategory
      .mappingConeIsoBackwardForwardSingleMap_targetComponent_eq_identity hom
  with
  | rfl => rfl

/-- The identity single-map normal form on the cone of an isomorphism is the
actual identity morphism. -/
theorem mappingConeIsoForwardBackwardIdentitySingleMap_eq_identityMorphism
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    [IsIso hom] :
    TraceAnalyticAdditiveHomotopyCategory
        .mappingConeIsoForwardBackwardIdentitySingleMap hom =
      TraceAnalyticAdditiveHomotopyCategory
        .mappingConeIsoForwardBackwardIdentityMorphism hom :=
  CochainComplex.mappingCone.map_id

/-- The identity single-map normal form on the identity cone is the actual
identity morphism. -/
theorem mappingConeIsoBackwardForwardIdentitySingleMap_eq_identityMorphism
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    [IsIso hom] :
    TraceAnalyticAdditiveHomotopyCategory
        .mappingConeIsoBackwardForwardIdentitySingleMap hom =
      TraceAnalyticAdditiveHomotopyCategory
        .mappingConeIsoBackwardForwardIdentityMorphism hom :=
  CochainComplex.mappingCone.map_id

/-- The forward-then-backward composite of the identity-cone comparison maps is
the identity. -/
theorem mappingConeIsoForwardBackwardComposite_eq_identityMorphism
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    [IsIso hom] :
    TraceAnalyticAdditiveHomotopyCategory
        .mappingConeIsoIdentityConeForwardBackwardComposite hom =
      TraceAnalyticAdditiveHomotopyCategory
        .mappingConeIsoForwardBackwardIdentityMorphism hom :=
  Eq.trans
    (TraceAnalyticAdditiveHomotopyCategory
      .mappingConeIsoForwardBackwardComposite_eq_singleMap hom)
    (Eq.trans
      (TraceAnalyticAdditiveHomotopyCategory
        .mappingConeIsoForwardBackwardSingleMap_eq_sourceIdentitySingleMap hom)
      (Eq.trans
        (TraceAnalyticAdditiveHomotopyCategory
          .mappingConeIsoForwardBackwardSourceIdentitySingleMap_eq_identitySingleMap
            hom)
        (TraceAnalyticAdditiveHomotopyCategory
          .mappingConeIsoForwardBackwardIdentitySingleMap_eq_identityMorphism
            hom)))

/-- The backward-then-forward composite of the identity-cone comparison maps is
the identity. -/
theorem mappingConeIsoBackwardForwardComposite_eq_identityMorphism
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    [IsIso hom] :
    TraceAnalyticAdditiveHomotopyCategory
        .mappingConeIsoIdentityConeBackwardForwardComposite hom =
      TraceAnalyticAdditiveHomotopyCategory
        .mappingConeIsoBackwardForwardIdentityMorphism hom :=
  Eq.trans
    (TraceAnalyticAdditiveHomotopyCategory
      .mappingConeIsoBackwardForwardComposite_eq_singleMap hom)
    (Eq.trans
      (TraceAnalyticAdditiveHomotopyCategory
        .mappingConeIsoBackwardForwardSingleMap_eq_sourceIdentitySingleMap hom)
      (Eq.trans
        (TraceAnalyticAdditiveHomotopyCategory
          .mappingConeIsoBackwardForwardSourceIdentitySingleMap_eq_identitySingleMap
            hom)
        (TraceAnalyticAdditiveHomotopyCategory
          .mappingConeIsoBackwardForwardIdentitySingleMap_eq_identityMorphism
            hom)))

/-- The mapping cone of an isomorphism is isomorphic to the identity cone of
its target. -/
def mappingConeIsoIdentityConeIso
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    [IsIso hom] :
    CochainComplex.mappingCone hom ≅
      CochainComplex.mappingCone (𝟙 target) where
  hom :=
    TraceAnalyticAdditiveHomotopyCategory
      .mappingConeIsoToIdentityConeMap hom
  inv :=
    TraceAnalyticAdditiveHomotopyCategory
      .identityConeToMappingConeIsoMap hom
  hom_inv_id :=
    Eq.trans
      (TraceAnalyticAdditiveHomotopyCategory
        .mappingConeIsoForwardBackwardComposite_eq_identityMorphism hom)
      (TraceAnalyticAdditiveHomotopyCategory
        .mappingConeIsoForwardBackwardIdentityMorphism_eq hom)
  inv_hom_id :=
    Eq.trans
      (TraceAnalyticAdditiveHomotopyCategory
        .mappingConeIsoBackwardForwardComposite_eq_identityMorphism hom)
      (TraceAnalyticAdditiveHomotopyCategory
        .mappingConeIsoBackwardForwardIdentityMorphism_eq hom)

end TraceAnalyticAdditiveHomotopyCategory

end AnalyticMotives
end LFunctions
end Boundary

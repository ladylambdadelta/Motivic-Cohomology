import Boundary.Basic
import Boundary.PolynomialSmoothness
import Boundary.SmOver
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Irreducible
import Geometry.Topology.IrreducibleComponents

universe u

variable {k : Type u} [Field k] [PerfectField k]

open AlgebraicGeometry CategoryTheory Limits

namespace Boundary

noncomputable section

namespace LocalIrreducibleProduct

open Set TopologicalSpace

theorem isIrreducible_prod
    {α β : Type u} [TopologicalSpace α] [TopologicalSpace β]
    {s : Set α} {t : Set β}
    (hs : IsIrreducible s) (ht : IsIrreducible t) :
    IsIrreducible (s ×ˢ t) := by
  refine ⟨hs.1.prod ht.1, ?_⟩
  intro U V hU hV hU' hV'
  rcases hU' with ⟨⟨x1, y1⟩, ⟨hxy1st, hxy1U⟩⟩
  rcases hV' with ⟨⟨x2, y2⟩, ⟨hxy2st, hxy2V⟩⟩
  rcases hxy1st with ⟨hx1, hy1⟩
  rcases hxy2st with ⟨hx2, hy2⟩
  rcases isOpen_prod_iff.mp hU x1 y1 hxy1U with
    ⟨U1, V1, hU1Open, hV1Open, hU1x, hV1y, hProd1⟩
  rcases isOpen_prod_iff.mp hV x2 y2 hxy2V with
    ⟨U2, V2, hU2Open, hV2Open, hU2x, hV2y, hProd2⟩
  have hxs : (s ∩ U1).Nonempty := ⟨x1, hx1, hU1x⟩
  have hxt : (t ∩ V1).Nonempty := ⟨y1, hy1, hV1y⟩
  have hys : (s ∩ U2).Nonempty := ⟨x2, hx2, hU2x⟩
  have hyt : (t ∩ V2).Nonempty := ⟨y2, hy2, hV2y⟩
  rcases hs.2 U1 U2 hU1Open hU2Open hxs hys with ⟨x, hxs', hxU1, hxU2⟩
  rcases ht.2 V1 V2 hV1Open hV2Open hxt hyt with ⟨y, hyt', hyV1, hyV2⟩
  refine ⟨(x, y), ⟨hxs', hyt'⟩, ?_⟩
  exact ⟨hProd1 ⟨hxU1, hyV1⟩, hProd2 ⟨hxU2, hyV2⟩⟩

theorem locallyIrreducible_prod
    {α β : Type u} [TopologicalSpace α] [TopologicalSpace β]
    (hα : Geometry.Topology.LocallyIrreducibleSpace α)
    (hβ : Geometry.Topology.LocallyIrreducibleSpace β) :
    Geometry.Topology.LocallyIrreducibleSpace (α × β) := by
  intro xy
  rcases hα xy.1 with ⟨U, hUOpen, hxU, hUIrr⟩
  rcases hβ xy.2 with ⟨V, hVOpen, hyV, hVIrr⟩
  refine ⟨U ×ˢ V, hUOpen.prod hVOpen, ⟨hxU, hyV⟩, ?_⟩
  exact isIrreducible_prod hUIrr hVIrr

theorem locallyIrreducible_of_isLocalHomeomorph
    {α β : Type u} [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β}
    (hf : IsLocalHomeomorph f)
    (hβ : Geometry.Topology.LocallyIrreducibleSpace β) :
    Geometry.Topology.LocallyIrreducibleSpace α := by
  intro x
  rcases (isLocalHomeomorph_iff_isOpenEmbedding_restrict.mp hf) x with ⟨U, hUx, hEmb⟩
  have hxU : x ∈ U := mem_of_mem_nhds hUx
  rcases hβ (f x) with ⟨V, hVOpen, hfxV, hVIrr⟩
  let Wsub : Set U := (U.restrict f) ⁻¹' V
  have hWsubOpen : IsOpen Wsub := hEmb.continuous.isOpen_preimage _ hVOpen
  have hWsubNonempty : Wsub.Nonempty := by
    refine ⟨⟨x, hxU⟩, ?_⟩
    exact hfxV
  have hWsubPreirr : IsPreirreducible Wsub := hVIrr.2.preimage hEmb
  have hWsubIrr : IsIrreducible Wsub := ⟨hWsubNonempty, hWsubPreirr⟩
  have hImageIrr : IsIrreducible (Subtype.val '' Wsub) :=
    hWsubIrr.image Subtype.val continuous_subtype_val.continuousOn
    have hImageEq : Subtype.val '' Wsub = U ∩ f ⁻¹' V := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z.2, hz⟩
      · rintro ⟨hyU, hyV⟩
        exact ⟨⟨y, hyU⟩, hyV, rfl⟩
    refine ⟨U ∩ f ⁻¹' V, hEmb.isOpenMap _ hWsubOpen, ⟨hxU, hfxV⟩, ?_⟩
    rw [← hImageEq]
    exact hImageIrr

theorem locallyIrreducible_of_irreducibleSpace
    {α : Type u} [TopologicalSpace α] [IrreducibleSpace α] :
    Geometry.Topology.LocallyIrreducibleSpace α := by
  intro x
  refine ⟨Set.univ, isOpen_univ, trivial, ?_⟩
  exact IrreducibleSpace.isIrreducible_univ α

theorem locallyIrreducible_of_openCover
    {α : Type u} [TopologicalSpace α]
    {ι : Type u}
    (U : ι → Set α)
    (hUOpen : ∀ i, IsOpen (U i))
    (hCover : ∀ x : α, ∃ i, x ∈ U i)
    (hLoc : ∀ i, Geometry.Topology.LocallyIrreducibleSpace (U i)) :
    Geometry.Topology.LocallyIrreducibleSpace α := by
  intro x
  rcases hCover x with ⟨i, hxU⟩
  rcases hLoc i ⟨x, hxU⟩ with ⟨V, hVOpen, hxV, hVIrr⟩
  refine ⟨Subtype.val '' V, ?_, ?_, ?_⟩
  · exact (hUOpen i).isOpenEmbedding_subtypeVal.isOpenMap _ hVOpen
  · exact ⟨⟨x, hxU⟩, hxV, rfl⟩
  · exact hVIrr.image Subtype.val continuous_subtype_val.continuousOn

theorem isLocalHomeomorph_of_openCover
    {α β ι : Type u} [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β}
    (U : ι → Set α)
    (hUOpen : ∀ i, IsOpen (U i))
    (hCover : ∀ x : α, ∃ i, x ∈ U i)
    (hf : ∀ i, IsLocalHomeomorph (U i).restrict f) :
    IsLocalHomeomorph f := by
  apply IsLocalHomeomorph.mk
  intro x
  rcases hCover x with ⟨i, hxU⟩
  let s : Opens α := ⟨U i, hUOpen i⟩
  have hsNonempty : Nonempty s := ⟨⟨x, hxU⟩⟩
  obtain ⟨e, hxe, he⟩ := hf i ⟨x, hxU⟩
  refine
    ⟨(s.partialHomeomorphSubtypeCoe hsNonempty).symm.trans e, ?_, ?_⟩
  · change x ∈ ((s.partialHomeomorphSubtypeCoe hsNonempty).symm.trans e).source
    rw [PartialHomeomorph.trans_source]
      change x ∈ (s.partialHomeomorphSubtypeCoe hsNonempty).symm.source ∧
          (s.partialHomeomorphSubtypeCoe hsNonempty).symm x ∈ e.source
      constructor
      · exact hxU
      · exact hxe
    · intro y hy
      rw [PartialHomeomorph.trans_source] at hy
      have hyU : y ∈ U i := by
        exact hy.1
      have hySource : ⟨y, hyU⟩ ∈ e.source := by
        exact hy.2
      have hEq := congrFun he ⟨y, hyU⟩
      change f y = e ⟨y, hyU⟩ at hEq
      change f y =
        ((s.partialHomeomorphSubtypeCoe hsNonempty).symm.trans e) y
      rw [PartialHomeomorph.trans_apply]
      exact hEq

theorem isLocalHomeomorph_iff_of_iSup_eq_top
    {α β ι : Type u} [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β}
    (U : ι → Opens β)
    (hU : iSup U = ⊤) :
    IsLocalHomeomorph f ↔ ∀ i, IsLocalHomeomorph ((U i).1.restrictPreimage f) := by
  constructor
  · intro hf i
    apply IsLocalHomeomorph.mk
    intro x
    rcases hf x.1 with ⟨e, hxe, he⟩
    refine ⟨e.restr ((U i : Set β)), ?_, ?_⟩
    · exact ⟨hxe, x.2⟩
    · ext y
      rfl
  · intro hf
    apply isLocalHomeomorph_of_openCover
      (U := fun i => f ⁻¹' (U i : Set β))
      · intro i
        exact (hf i).continuous.isOpen_preimage _ (U i).2
      · intro x
        have htop : f x ∈ (⊤ : Opens β) := trivial
        rw [← hU] at htop
        exact Opens.mem_iSup.mp htop
      · intro i
        exact hf i

end LocalIrreducibleProduct

namespace AlgebraicGeometry.Scheme.Hom

/-- The underlying map of an open immersion of schemes is a local
homeomorphism. This is the precise topological API needed to pull local
irreducibility back along affine `Spec.map` constructions. -/
theorem isLocalHomeomorph_base_of_isOpenImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    IsLocalHomeomorph f.base :=
  f.isOpenEmbedding.isLocalHomeomorph

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry

/-- The morphism property "the underlying map is a local homeomorphism" respects
scheme isomorphisms. -/
theorem topologically_isLocalHomeomorph_respectsIso :
    MorphismProperty.RespectsIso
      (AlgebraicGeometry.topologically (@IsLocalHomeomorph)) :=
  AlgebraicGeometry.topologically_respectsIso
    (@IsLocalHomeomorph)
    (fun e ↦ e.isLocalHomeomorph)
    (fun _ _ hf hg ↦ hg.comp hf)

instance topologically_isLocalHomeomorph_isLocalAtTarget :
    IsLocalAtTarget (AlgebraicGeometry.topologically (@IsLocalHomeomorph)) :=
  AlgebraicGeometry.topologically_isLocalAtTarget'
    (@IsLocalHomeomorph)
    (fun _ _ _ _ f ι U hU ↦
      LocalIrreducibleProduct.isLocalHomeomorph_iff_of_iSup_eq_top (f := f) U hU)

/-- Transport local-homeomorphism of underlying maps across an isomorphism of
arrow objects. -/
theorem scheme_isLocalHomeomorph_iff_of_arrowIso
    {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {g : X' ⟶ Y'}
    (e : Arrow.mk f ≅ Arrow.mk g) :
    IsLocalHomeomorph f.base ↔ IsLocalHomeomorph g.base := by
    let P : MorphismProperty Scheme := AlgebraicGeometry.topologically (@IsLocalHomeomorph)
    have hP : P.RespectsIso := topologically_isLocalHomeomorph_respectsIso
    change P (Arrow.mk f).hom ↔ P (Arrow.mk g).hom
    exact MorphismProperty.arrow_mk_iso_iff P e

/-- The affine `Spec.map` attached to a localization away from one element is a
local homeomorphism on underlying spaces. -/
theorem specMap_isLocalHomeomorph_localizationAway
    {R : Type u} [CommRing R] (r : R) :
    IsLocalHomeomorph
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))).base) := by
  letI :
      IsOpenImmersion
        (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) :=
    inferInstance
  exact Scheme.Hom.isLocalHomeomorph_base_of_isOpenImmersion _

/-- More generally, the affine `Spec.map` attached to any algebra presented as
`R[r⁻¹]` is a local homeomorphism on underlying spaces. -/
theorem specMap_isLocalHomeomorph_of_isLocalization
    {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (r : R) [IsLocalization.Away r S] :
    IsLocalHomeomorph
      (Spec.map (CommRingCat.ofHom (algebraMap R S))).base := by
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
    AlgebraicGeometry.IsOpenImmersion.of_isLocalization (S := S) r
  exact Scheme.Hom.isLocalHomeomorph_base_of_isOpenImmersion _

/-- If an affine `Spec.map` becomes a local homeomorphism after localizing the
target ring on a spanning family, then it is already a local homeomorphism. -/
theorem specMap_isLocalHomeomorph_of_localizationSpanTarget
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S)
    (s : Set S) (hs : Ideal.span s = ⊤)
    (hlocal :
      ∀ r : s,
        IsLocalHomeomorph
          (Spec.map
            (CommRingCat.ofHom
              ((algebraMap S (Localization.Away (r : S))).comp φ))).base) :
    IsLocalHomeomorph (Spec.map (CommRingCat.ofHom φ)).base := by
  classical
  let f := (Spec.map (CommRingCat.ofHom φ)).base
  apply LocalIrreducibleProduct.isLocalHomeomorph_of_openCover
    (U := fun r : s => (PrimeSpectrum.basicOpen (r : S) : Set (PrimeSpectrum S)))
  · intro r
    exact PrimeSpectrum.isOpen_basicOpen
  · intro x
    by_contra hx
    have hsx : s ⊆ x.asIdeal := by
      intro r hr
      exact not_not.mp (fun hmem => hx ⟨r, hr, (PrimeSpectrum.mem_basicOpen _ _).2 hmem⟩)
    have hspan : Ideal.span s ≤ x.asIdeal :=
      Ideal.span_le.mpr hsx
    have : (1 : S) ∈ x.asIdeal := by
      rw [← hs]
      exact hspan (Ideal.mem_top _)
    exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem x.asIdeal this isUnit_one)
  · intro r
    have hiff :=
      scheme_isLocalHomeomorph_iff_of_arrowIso
        (SpecMapRestrictBasicOpenIso (CommRingCat.ofHom φ) (r : S))
    exact hiff.mpr (hlocal r)

end AlgebraicGeometry

/-- The fiber product `X ×_k Y` over the base field. -/
abbrev overBaseProduct (X Y : Geometry.SmSchemeOver k) : Scheme :=
  pullback X.structMap Y.structMap

/-- The projection `X ×_k Y → X`. -/
abbrev overBaseProduct.fst (X Y : Geometry.SmSchemeOver k) :
    overBaseProduct X Y ⟶ X.scheme :=
  pullback.fst X.structMap Y.structMap

/-- The projection `X ×_k Y → Y`. -/
abbrev overBaseProduct.snd (X Y : Geometry.SmSchemeOver k) :
    overBaseProduct X Y ⟶ Y.scheme :=
  pullback.snd X.structMap Y.structMap

/-- The fiber product `X ×_k Y` as an actual object of `Sm/k`. -/
def overBaseProductObject (X Y : Geometry.SmSchemeOver k) : Geometry.SmSchemeOver k where
  scheme := overBaseProduct X Y
  structMap := overBaseProduct.fst X Y ≫ X.structMap
  smooth := by
    letI : MorphismProperty.IsStableUnderBaseChange @IsSmooth :=
      AlgebraicGeometry.isSmooth_isStableUnderBaseChange
    letI : IsSmooth (overBaseProduct.fst X Y) :=
      MorphismProperty.pullback_fst X.structMap Y.structMap Y.smooth
    letI : IsSmooth X.structMap := X.smooth
    infer_instance
  separated := by
    letI : IsSeparated (overBaseProduct.fst X Y) :=
      MorphismProperty.pullback_fst X.structMap Y.structMap Y.separated
    letI : IsSeparated X.structMap := X.separated
    infer_instance
  finiteType := ⟨by
      letI : QuasiCompact (overBaseProduct.fst X Y) :=
        MorphismProperty.pullback_fst X.structMap Y.structMap Y.quasiCompact_structMap
      letI : QuasiCompact X.structMap := X.quasiCompact_structMap
      infer_instance,
    by
      letI : LocallyOfFiniteType (overBaseProduct.fst X Y) :=
        MorphismProperty.pullback_fst X.structMap Y.structMap Y.locallyOfFiniteType_structMap
      letI : LocallyOfFiniteType X.structMap := X.locallyOfFiniteType_structMap
      infer_instance⟩

/-- The unit object for products over `Spec k`. -/
def overBaseUnitObject : Geometry.SmSchemeOver k where
  scheme := Spec (CommRingCat.of k)
  structMap := 𝟙 _
  smooth := by infer_instance
  separated := by infer_instance
  finiteType := by constructor <;> infer_instance

/-- The first projection `X ×_k Y ⟶ X` in `Sm/k`. -/
def overBaseProductFst (X Y : Geometry.SmSchemeOver k) :
    SmOverHom (overBaseProductObject X Y) X where
  hom := overBaseProduct.fst X Y
  over := rfl

/-- The second projection `X ×_k Y ⟶ Y` in `Sm/k`. -/
def overBaseProductSnd (X Y : Geometry.SmSchemeOver k) :
    SmOverHom (overBaseProductObject X Y) Y where
  hom := overBaseProduct.snd X Y
  over := by
    change pullback.snd X.structMap Y.structMap ≫ Y.structMap =
      pullback.fst X.structMap Y.structMap ≫ X.structMap
    exact (pullback.condition (f := X.structMap) (g := Y.structMap)).symm

/-- Functoriality of the base product over `Spec k` on ordinary morphisms. -/
def overBaseProductMap
    {X₁ X₂ Y₁ Y₂ : Geometry.SmSchemeOver k}
    (f : SmOverHom X₁ X₂)
    (g : SmOverHom Y₁ Y₂) :
    SmOverHom (overBaseProductObject X₁ Y₁) (overBaseProductObject X₂ Y₂) where
  hom :=
    pullback.map X₁.structMap Y₁.structMap X₂.structMap Y₂.structMap
      f.hom g.hom (𝟙 _)
      (by
        rw [Category.id_comp]
        exact f.over.symm)
      (by
        rw [Category.id_comp]
        exact g.over.symm)
  over := by
    change
      pullback.map X₁.structMap Y₁.structMap X₂.structMap Y₂.structMap
        f.hom g.hom (𝟙 _) _ _ ≫ X₂.structMap =
      pullback.fst X₁.structMap Y₁.structMap ≫ X₁.structMap
    rw [pullback.map_fst_assoc]
    exact f.over

@[simp] theorem overBaseProductMap_id
    (X Y : Geometry.SmSchemeOver k) :
    overBaseProductMap (𝟙 X) (𝟙 Y) =
        𝟙 (overBaseProductObject X Y) := by
  apply SmOverHom.ext
  apply pullback.hom_ext
  · change
      (overBaseProductMap (𝟙 X) (𝟙 Y)).hom ≫
          pullback.fst X.structMap Y.structMap =
        𝟙 (pullback X.structMap Y.structMap) ≫
          pullback.fst X.structMap Y.structMap
    rw [Category.id_comp]
    exact pullback.map_fst _ _ _ _ _ _ _ _ _
  · change
      (overBaseProductMap (𝟙 X) (𝟙 Y)).hom ≫
          pullback.snd X.structMap Y.structMap =
        𝟙 (pullback X.structMap Y.structMap) ≫
          pullback.snd X.structMap Y.structMap
    rw [Category.id_comp]
    exact pullback.map_snd _ _ _ _ _ _ _ _ _

@[simp] theorem overBaseProductMap_comp
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Geometry.SmSchemeOver k}
    (f₁₂ : SmOverHom X₁ X₂) (f₂₃ : SmOverHom X₂ X₃)
    (g₁₂ : SmOverHom Y₁ Y₂) (g₂₃ : SmOverHom Y₂ Y₃) :
    overBaseProductMap (SmOverHom.comp f₁₂ f₂₃) (SmOverHom.comp g₁₂ g₂₃) =
        SmOverHom.comp (overBaseProductMap f₁₂ g₁₂) (overBaseProductMap f₂₃ g₂₃) := by
  apply SmOverHom.ext
  apply pullback.hom_ext
  · change
      (overBaseProductMap (SmOverHom.comp f₁₂ f₂₃) (SmOverHom.comp g₁₂ g₂₃)).hom ≫
          pullback.fst X₃.structMap Y₃.structMap =
        (overBaseProductMap f₁₂ g₁₂).hom ≫
          (overBaseProductMap f₂₃ g₂₃).hom ≫
            pullback.fst X₃.structMap Y₃.structMap
    rw [pullback.map_fst, Category.assoc, pullback.map_fst]
    rw [pullback.map_fst]
  · change
      (overBaseProductMap (SmOverHom.comp f₁₂ f₂₃) (SmOverHom.comp g₁₂ g₂₃)).hom ≫
          pullback.snd X₃.structMap Y₃.structMap =
        (overBaseProductMap f₁₂ g₁₂).hom ≫
          (overBaseProductMap f₂₃ g₂₃).hom ≫
            pullback.snd X₃.structMap Y₃.structMap
    rw [pullback.map_snd, Category.assoc, pullback.map_snd]
    rw [pullback.map_snd]

/-- Left unitor for the fiber product over `Spec k`. -/
noncomputable def overBaseProductLeftUnitor
    (X : Geometry.SmSchemeOver k) :
    overBaseProductObject (overBaseUnitObject (k := k)) X ≅ X where
  hom := overBaseProductSnd (overBaseUnitObject (k := k)) X
  inv :=
    { hom :=
        pullback.lift X.structMap (𝟙 X.scheme) (by
          rw [Category.id_comp])
      over := by
        change (pullback.lift X.structMap (𝟙 X.scheme) _ ≫
            pullback.fst (𝟙 (Spec (CommRingCat.of k))) X.structMap) ≫
              𝟙 (Spec (CommRingCat.of k)) =
          X.structMap
        rw [pullback.lift_fst, Category.comp_id] }
  hom_inv_id := by
    apply SmOverHom.ext
    change overBaseProduct.snd (overBaseUnitObject (k := k)) X ≫
        pullback.lift X.structMap (𝟙 X.scheme) _ =
      𝟙 (overBaseProductObject (overBaseUnitObject (k := k)) X).scheme
    apply pullback.hom_ext
    · rw [overBaseProductSnd, overBaseProductObject, overBaseUnitObject, Category.assoc]
          using (pullback.condition
            (f := (𝟙 (Spec (CommRingCat.of k))))
            (g := X.structMap)).symm
    · change
        overBaseProduct.snd (overBaseUnitObject (k := k)) X ≫
            pullback.lift X.structMap (𝟙 X.scheme) _ ≫
              pullback.snd (𝟙 (Spec (CommRingCat.of k))) X.structMap =
          𝟙 (pullback (𝟙 (Spec (CommRingCat.of k))) X.structMap) ≫
            pullback.snd (𝟙 (Spec (CommRingCat.of k))) X.structMap
      rw [Category.id_comp, Category.assoc, pullback.lift_snd, Category.comp_id]
  inv_hom_id := by
    apply SmOverHom.ext
    change pullback.lift X.structMap (𝟙 X.scheme) _ ≫
        overBaseProduct.snd (overBaseUnitObject (k := k)) X =
      𝟙 X.scheme
    change pullback.lift X.structMap (𝟙 X.scheme) _ ≫
        pullback.snd (𝟙 (Spec (CommRingCat.of k))) X.structMap =
      𝟙 X.scheme
    rw [pullback.lift_snd]

/-- Right unitor for the fiber product over `Spec k`. -/
noncomputable def overBaseProductRightUnitor
    (X : Geometry.SmSchemeOver k) :
    overBaseProductObject X (overBaseUnitObject (k := k)) ≅ X where
  hom := overBaseProductFst X (overBaseUnitObject (k := k))
  inv :=
    { hom :=
        pullback.lift (𝟙 X.scheme) X.structMap (by
          rw [Category.comp_id])
      over := by
        change (pullback.lift (𝟙 X.scheme) X.structMap _ ≫
            pullback.fst X.structMap (𝟙 (Spec (CommRingCat.of k)))) ≫
              X.structMap =
          X.structMap
        rw [pullback.lift_fst, Category.id_comp] }
  hom_inv_id := by
    apply SmOverHom.ext
    change overBaseProduct.fst X (overBaseUnitObject (k := k)) ≫
        pullback.lift (𝟙 X.scheme) X.structMap _ =
      𝟙 (overBaseProductObject X (overBaseUnitObject (k := k))).scheme
    apply pullback.hom_ext
    · change
        overBaseProduct.fst X (overBaseUnitObject (k := k)) ≫
            pullback.lift (𝟙 X.scheme) X.structMap _ ≫
              pullback.fst X.structMap (𝟙 (Spec (CommRingCat.of k))) =
          𝟙 (pullback X.structMap (𝟙 (Spec (CommRingCat.of k)))) ≫
            pullback.fst X.structMap (𝟙 (Spec (CommRingCat.of k)))
      rw [Category.id_comp, Category.assoc, pullback.lift_fst, Category.comp_id]
    · rw [overBaseProductFst, overBaseProductObject, overBaseUnitObject, Category.assoc]
        using (pullback.condition
          (f := X.structMap)
          (g := (𝟙 (Spec (CommRingCat.of k)))))
  inv_hom_id := by
    apply SmOverHom.ext
    change pullback.lift (𝟙 X.scheme) X.structMap _ ≫
        overBaseProduct.fst X (overBaseUnitObject (k := k)) =
      𝟙 X.scheme
    change pullback.lift (𝟙 X.scheme) X.structMap _ ≫
        pullback.fst X.structMap (𝟙 (Spec (CommRingCat.of k))) =
      𝟙 X.scheme
    rw [pullback.lift_fst]

@[simp, reassoc] theorem overBaseProductLeftUnitor_hom
    (X : Geometry.SmSchemeOver k) :
    (overBaseProductLeftUnitor (k := k) X).hom.hom =
      overBaseProduct.snd (overBaseUnitObject (k := k)) X := by
  rfl

@[simp, reassoc] theorem overBaseProductLeftUnitor_inv_fst
    (X : Geometry.SmSchemeOver k) :
    (overBaseProductLeftUnitor (k := k) X).inv.hom ≫
        overBaseProduct.fst (overBaseUnitObject (k := k)) X =
      X.structMap := by
    change pullback.lift X.structMap (𝟙 X.scheme) _ ≫
        pullback.fst (𝟙 (Spec (CommRingCat.of k))) X.structMap =
      X.structMap
    rw [pullback.lift_fst]

@[simp, reassoc] theorem overBaseProductLeftUnitor_inv_snd
    (X : Geometry.SmSchemeOver k) :
    (overBaseProductLeftUnitor (k := k) X).inv.hom ≫
        overBaseProduct.snd (overBaseUnitObject (k := k)) X =
      𝟙 X.scheme := by
    change pullback.lift X.structMap (𝟙 X.scheme) _ ≫
        pullback.snd (𝟙 (Spec (CommRingCat.of k))) X.structMap =
      𝟙 X.scheme
    rw [pullback.lift_snd]

@[simp, reassoc] theorem overBaseProductRightUnitor_hom
    (X : Geometry.SmSchemeOver k) :
    (overBaseProductRightUnitor (k := k) X).hom.hom =
      overBaseProduct.fst X (overBaseUnitObject (k := k)) := by
  rfl

@[simp, reassoc] theorem overBaseProductRightUnitor_inv_fst
    (X : Geometry.SmSchemeOver k) :
    (overBaseProductRightUnitor (k := k) X).inv.hom ≫
        overBaseProduct.fst X (overBaseUnitObject (k := k)) =
      𝟙 X.scheme := by
    change pullback.lift (𝟙 X.scheme) X.structMap _ ≫
        pullback.fst X.structMap (𝟙 (Spec (CommRingCat.of k))) =
      𝟙 X.scheme
    rw [pullback.lift_fst]

@[simp, reassoc] theorem overBaseProductRightUnitor_inv_snd
    (X : Geometry.SmSchemeOver k) :
    (overBaseProductRightUnitor (k := k) X).inv.hom ≫
        overBaseProduct.snd X (overBaseUnitObject (k := k)) =
      X.structMap := by
    change pullback.lift (𝟙 X.scheme) X.structMap _ ≫
        pullback.snd X.structMap (𝟙 (Spec (CommRingCat.of k))) =
      X.structMap
    rw [pullback.lift_snd]

/-- Associativity isomorphism for iterated fiber products over `Spec k`,
written at the level of `Sm/k` objects. -/
noncomputable def overBaseProductAssoc
    (X Y Z : Geometry.SmSchemeOver k) :
    overBaseProductObject (overBaseProductObject X Y) Z ≅
      overBaseProductObject X (overBaseProductObject Y Z) := by
  refine
    { hom :=
        { hom :=
            pullback.lift
              (overBaseProduct.fst (overBaseProductObject X Y) Z ≫ overBaseProduct.fst X Y)
              (pullback.lift
                (overBaseProduct.fst (overBaseProductObject X Y) Z ≫ overBaseProduct.snd X Y)
                (overBaseProduct.snd (overBaseProductObject X Y) Z)
                (by
                  calc
                    (overBaseProduct.fst (overBaseProductObject X Y) Z ≫
                          overBaseProduct.snd X Y) ≫ Y.structMap =
                        overBaseProduct.fst (overBaseProductObject X Y) Z ≫
                          (overBaseProduct.snd X Y ≫ Y.structMap) := by
                          rw [Category.assoc]
                    _ = overBaseProduct.fst (overBaseProductObject X Y) Z ≫
                          (overBaseProduct.fst X Y ≫ X.structMap) := by
                          rw [(pullback.condition (f := X.structMap) (g := Y.structMap)).symm]
                    _ = overBaseProduct.snd (overBaseProductObject X Y) Z ≫ Z.structMap := by
                          rw [← Category.assoc]
                          exact pullback.condition
                            (f := (overBaseProductObject X Y).structMap)
                            (g := Z.structMap))
              (by
                calc
                  (overBaseProduct.fst (overBaseProductObject X Y) Z ≫
                        overBaseProduct.fst X Y) ≫ X.structMap =
                      overBaseProduct.fst (overBaseProductObject X Y) Z ≫
                        (overBaseProduct.fst X Y ≫ X.structMap) := by
                        rw [Category.assoc]
                  _ = overBaseProduct.fst (overBaseProductObject X Y) Z ≫
                        (overBaseProduct.snd X Y ≫ Y.structMap) := by
                        rw [pullback.condition (f := X.structMap) (g := Y.structMap)]
                  _ =
                      pullback.lift
                        (overBaseProduct.fst (overBaseProductObject X Y) Z ≫
                          overBaseProduct.snd X Y)
                        (overBaseProduct.snd (overBaseProductObject X Y) Z)
                        _ ≫ (overBaseProductObject Y Z).structMap := by
                        change overBaseProduct.fst (overBaseProductObject X Y) Z ≫
                            (overBaseProduct.snd X Y ≫ Y.structMap) =
                          pullback.lift
                              (overBaseProduct.fst (overBaseProductObject X Y) Z ≫
                                overBaseProduct.snd X Y)
                              (overBaseProduct.snd (overBaseProductObject X Y) Z) _ ≫
                            (pullback.fst Y.structMap Z.structMap ≫ Y.structMap)
                        rw [Category.assoc, pullback.lift_fst])
          over := by
            change pullback.lift
                (overBaseProduct.fst (overBaseProductObject X Y) Z ≫
                  overBaseProduct.fst X Y)
                (pullback.lift
                  (overBaseProduct.fst (overBaseProductObject X Y) Z ≫
                    overBaseProduct.snd X Y)
                  (overBaseProduct.snd (overBaseProductObject X Y) Z) _) _ ≫
                X.structMap =
              (pullback.fst (overBaseProductObject X Y).structMap Z.structMap ≫
                  (overBaseProductObject X Y).structMap)
            rw [pullback.lift_fst] }
      inv :=
        { hom :=
            pullback.lift
              (pullback.lift
                (overBaseProduct.fst X (overBaseProductObject Y Z))
                (overBaseProduct.snd X (overBaseProductObject Y Z) ≫ overBaseProduct.fst Y Z)
                (by
                  calc
                    overBaseProduct.fst X (overBaseProductObject Y Z) ≫ X.structMap =
                        overBaseProduct.snd X (overBaseProductObject Y Z) ≫
                          (overBaseProductObject Y Z).structMap := by
                          exact pullback.condition
                    _ = (overBaseProduct.snd X (overBaseProductObject Y Z) ≫
                            overBaseProduct.fst Y Z) ≫ Y.structMap := by
                          rw [Category.assoc])
              (overBaseProduct.snd X (overBaseProductObject Y Z) ≫ overBaseProduct.snd Y Z)
              (by
                calc
                  pullback.lift
                        (overBaseProduct.fst X (overBaseProductObject Y Z))
                        (overBaseProduct.snd X (overBaseProductObject Y Z) ≫
                          overBaseProduct.fst Y Z)
                        _ ≫ (overBaseProductObject X Y).structMap =
                      overBaseProduct.fst X (overBaseProductObject Y Z) ≫ X.structMap := by
                        change pullback.lift
                            (overBaseProduct.fst X (overBaseProductObject Y Z))
                            (overBaseProduct.snd X (overBaseProductObject Y Z) ≫
                              overBaseProduct.fst Y Z) _ ≫
                            (pullback.fst X.structMap Y.structMap ≫ X.structMap) =
                          overBaseProduct.fst X (overBaseProductObject Y Z) ≫ X.structMap
                        rw [Category.assoc, pullback.lift_fst]
                  _ = overBaseProduct.snd X (overBaseProductObject Y Z) ≫
                        (overBaseProductObject Y Z).structMap := by
                        exact pullback.condition
                  _ = overBaseProduct.snd X (overBaseProductObject Y Z) ≫
                        (overBaseProduct.snd Y Z ≫ Z.structMap) := by
                        rw [pullback.condition
                          (f := (overBaseProductObject Y Z).structMap)
                          (g := X.structMap)]
                        change overBaseProduct.snd X (overBaseProductObject Y Z) ≫
                            (pullback.fst Y.structMap Z.structMap ≫ Y.structMap) =
                          overBaseProduct.snd X (overBaseProductObject Y Z) ≫
                            (pullback.snd Y.structMap Z.structMap ≫ Z.structMap)
                        rw [pullback.condition]
                  _ = (overBaseProduct.snd X (overBaseProductObject Y Z) ≫
                        overBaseProduct.snd Y Z) ≫ Z.structMap := by
                        rw [Category.assoc])
          over := by
            change pullback.lift
                (pullback.lift
                  (overBaseProduct.fst X (overBaseProductObject Y Z))
                  (overBaseProduct.snd X (overBaseProductObject Y Z) ≫
                    overBaseProduct.fst Y Z) _)
                (overBaseProduct.snd X (overBaseProductObject Y Z) ≫
                  overBaseProduct.snd Y Z) _ ≫
                (overBaseProductObject X Y).structMap =
              pullback.fst X.structMap (overBaseProductObject Y Z).structMap ≫
                X.structMap
            rw [pullback.lift_fst]
            change pullback.lift
                (overBaseProduct.fst X (overBaseProductObject Y Z))
                (overBaseProduct.snd X (overBaseProductObject Y Z) ≫
                  overBaseProduct.fst Y Z) _ ≫
                (pullback.fst X.structMap Y.structMap ≫ X.structMap) =
              pullback.fst X.structMap (overBaseProductObject Y Z).structMap ≫
                X.structMap
            rw [Category.assoc, pullback.lift_fst] }
      hom_inv_id := by
        apply SmOverHom.ext
        change (pullback.lift
            (overBaseProduct.fst (overBaseProductObject X Y) Z ≫ overBaseProduct.fst X Y)
            (pullback.lift
              (overBaseProduct.fst (overBaseProductObject X Y) Z ≫ overBaseProduct.snd X Y)
              (overBaseProduct.snd (overBaseProductObject X Y) Z) _)
            _ ≫
          pullback.lift
            (pullback.lift
              (overBaseProduct.fst X (overBaseProductObject Y Z))
              (overBaseProduct.snd X (overBaseProductObject Y Z) ≫ overBaseProduct.fst Y Z) _)
            (overBaseProduct.snd X (overBaseProductObject Y Z) ≫ overBaseProduct.snd Y Z) _) =
          𝟙 (overBaseProductObject (overBaseProductObject X Y) Z).scheme
        apply pullback.hom_ext
        · apply pullback.hom_ext
          · rw [Category.assoc, pullback.lift_fst_assoc, pullback.lift_fst,
              pullback.lift_fst, Category.id_comp]
          · rw [Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd,
              pullback.lift_fst_assoc, pullback.lift_snd, Category.id_comp]
        · rw [Category.assoc, pullback.lift_snd_assoc, pullback.lift_snd,
            Category.id_comp]
      inv_hom_id := by
        apply SmOverHom.ext
        change (pullback.lift
            (pullback.lift
              (overBaseProduct.fst X (overBaseProductObject Y Z))
              (overBaseProduct.snd X (overBaseProductObject Y Z) ≫ overBaseProduct.fst Y Z) _)
            (overBaseProduct.snd X (overBaseProductObject Y Z) ≫ overBaseProduct.snd Y Z) _ ≫
          pullback.lift
            (overBaseProduct.fst (overBaseProductObject X Y) Z ≫ overBaseProduct.fst X Y)
            (pullback.lift
              (overBaseProduct.fst (overBaseProductObject X Y) Z ≫ overBaseProduct.snd X Y)
              (overBaseProduct.snd (overBaseProductObject X Y) Z) _)
            _) =
          𝟙 (overBaseProductObject X (overBaseProductObject Y Z)).scheme
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst_assoc, pullback.lift_fst,
            Category.id_comp]
        · apply pullback.hom_ext
          · rw [Category.assoc, pullback.lift_snd_assoc, pullback.lift_fst,
              pullback.lift_snd_assoc, pullback.lift_fst, Category.id_comp]
          · rw [Category.assoc, pullback.lift_snd_assoc, pullback.lift_snd,
              Category.id_comp] }

/-- Symmetry isomorphism for the fiber product over `Spec k`,
written at the level of `Sm/k` objects. -/
noncomputable def overBaseProductSymm
    (X Y : Geometry.SmSchemeOver k) :
    overBaseProductObject X Y ≅ overBaseProductObject Y X := by
  let e := pullbackSymmetry X.structMap Y.structMap
  refine
    { hom :=
        { hom := e.hom
          over := by
            change e.hom ≫
                (pullback.fst Y.structMap X.structMap ≫ Y.structMap) =
              pullback.fst X.structMap Y.structMap ≫ X.structMap
            rw [← Category.assoc, pullbackSymmetry_hom_comp_fst]
            exact (pullback.condition (f := X.structMap) (g := Y.structMap)).symm }
      inv :=
        { hom := e.inv
          over := by
            change e.inv ≫
                (pullback.fst X.structMap Y.structMap ≫ X.structMap) =
              pullback.fst Y.structMap X.structMap ≫ Y.structMap
            rw [← Category.assoc, pullbackSymmetry_inv_comp_fst]
            exact (pullback.condition (f := Y.structMap) (g := X.structMap)).symm }
      hom_inv_id := by
        apply SmOverHom.ext
        exact e.hom_inv_id
      inv_hom_id := by
        apply SmOverHom.ext
        exact e.inv_hom_id }

@[simp, reassoc] theorem overBaseProductAssoc_hom_fst
      (X Y Z : Geometry.SmSchemeOver k) :
      (overBaseProductAssoc X Y Z).hom.hom ≫ overBaseProduct.fst X (overBaseProductObject Y Z) =
        overBaseProduct.fst (overBaseProductObject X Y) Z ≫ overBaseProduct.fst X Y := by
    change
      pullback.lift
          (overBaseProduct.fst (overBaseProductObject X Y) Z ≫ overBaseProduct.fst X Y)
          (pullback.lift
            (overBaseProduct.fst (overBaseProductObject X Y) Z ≫ overBaseProduct.snd X Y)
            (overBaseProduct.snd (overBaseProductObject X Y) Z) _) _ ≫
        pullback.fst X.structMap (overBaseProductObject Y Z).structMap =
      overBaseProduct.fst (overBaseProductObject X Y) Z ≫ overBaseProduct.fst X Y
    rw [pullback.lift_fst]

@[simp, reassoc] theorem overBaseProductAssoc_hom_snd_fst
      (X Y Z : Geometry.SmSchemeOver k) :
      (overBaseProductAssoc X Y Z).hom.hom ≫ overBaseProduct.snd X (overBaseProductObject Y Z) ≫
          overBaseProduct.fst Y Z =
        overBaseProduct.fst (overBaseProductObject X Y) Z ≫ overBaseProduct.snd X Y := by
    change
      (pullback.lift
          (overBaseProduct.fst (overBaseProductObject X Y) Z ≫ overBaseProduct.fst X Y)
          (pullback.lift
            (overBaseProduct.fst (overBaseProductObject X Y) Z ≫ overBaseProduct.snd X Y)
            (overBaseProduct.snd (overBaseProductObject X Y) Z) _) _ ≫
        pullback.snd X.structMap (overBaseProductObject Y Z).structMap) ≫
          pullback.fst Y.structMap Z.structMap =
      overBaseProduct.fst (overBaseProductObject X Y) Z ≫ overBaseProduct.snd X Y
    rw [pullback.lift_snd_assoc, pullback.lift_fst]

@[simp, reassoc] theorem overBaseProductAssoc_hom_snd_snd
      (X Y Z : Geometry.SmSchemeOver k) :
      (overBaseProductAssoc X Y Z).hom.hom ≫ overBaseProduct.snd X (overBaseProductObject Y Z) ≫
          overBaseProduct.snd Y Z =
        overBaseProduct.snd (overBaseProductObject X Y) Z := by
    change
      (pullback.lift
          (overBaseProduct.fst (overBaseProductObject X Y) Z ≫ overBaseProduct.fst X Y)
          (pullback.lift
            (overBaseProduct.fst (overBaseProductObject X Y) Z ≫ overBaseProduct.snd X Y)
            (overBaseProduct.snd (overBaseProductObject X Y) Z) _) _ ≫
        pullback.snd X.structMap (overBaseProductObject Y Z).structMap) ≫
          pullback.snd Y.structMap Z.structMap =
      overBaseProduct.snd (overBaseProductObject X Y) Z
    rw [pullback.lift_snd_assoc, pullback.lift_snd]

@[simp, reassoc] theorem overBaseProductAssoc_inv_fst_fst
      (X Y Z : Geometry.SmSchemeOver k) :
      (overBaseProductAssoc X Y Z).inv.hom ≫ overBaseProduct.fst (overBaseProductObject X Y) Z ≫
          overBaseProduct.fst X Y =
        overBaseProduct.fst X (overBaseProductObject Y Z) := by
    change
      (pullback.lift
          (pullback.lift
            (overBaseProduct.fst X (overBaseProductObject Y Z))
            (overBaseProduct.snd X (overBaseProductObject Y Z) ≫ overBaseProduct.fst Y Z) _)
          (overBaseProduct.snd X (overBaseProductObject Y Z) ≫ overBaseProduct.snd Y Z) _ ≫
        pullback.fst (overBaseProductObject X Y).structMap Z.structMap) ≫
          pullback.fst X.structMap Y.structMap =
      overBaseProduct.fst X (overBaseProductObject Y Z)
    rw [pullback.lift_fst_assoc, pullback.lift_fst]

@[simp, reassoc] theorem overBaseProductAssoc_inv_fst_snd
      (X Y Z : Geometry.SmSchemeOver k) :
      (overBaseProductAssoc X Y Z).inv.hom ≫ overBaseProduct.fst (overBaseProductObject X Y) Z ≫
          overBaseProduct.snd X Y =
        overBaseProduct.snd X (overBaseProductObject Y Z) ≫ overBaseProduct.fst Y Z := by
    change
      (pullback.lift
          (pullback.lift
            (overBaseProduct.fst X (overBaseProductObject Y Z))
            (overBaseProduct.snd X (overBaseProductObject Y Z) ≫ overBaseProduct.fst Y Z) _)
          (overBaseProduct.snd X (overBaseProductObject Y Z) ≫ overBaseProduct.snd Y Z) _ ≫
        pullback.fst (overBaseProductObject X Y).structMap Z.structMap) ≫
          pullback.snd X.structMap Y.structMap =
      overBaseProduct.snd X (overBaseProductObject Y Z) ≫ overBaseProduct.fst Y Z
    rw [pullback.lift_fst_assoc, pullback.lift_snd]

@[simp, reassoc] theorem overBaseProductAssoc_inv_snd
      (X Y Z : Geometry.SmSchemeOver k) :
      (overBaseProductAssoc X Y Z).inv.hom ≫ overBaseProduct.snd (overBaseProductObject X Y) Z =
        overBaseProduct.snd X (overBaseProductObject Y Z) ≫ overBaseProduct.snd Y Z := by
    change
      pullback.lift
          (pullback.lift
            (overBaseProduct.fst X (overBaseProductObject Y Z))
            (overBaseProduct.snd X (overBaseProductObject Y Z) ≫ overBaseProduct.fst Y Z) _)
          (overBaseProduct.snd X (overBaseProductObject Y Z) ≫ overBaseProduct.snd Y Z) _ ≫
        pullback.snd (overBaseProductObject X Y).structMap Z.structMap =
      overBaseProduct.snd X (overBaseProductObject Y Z) ≫ overBaseProduct.snd Y Z
    rw [pullback.lift_snd]

@[simp, reassoc] theorem overBaseProductSymm_hom_fst
    (X Y : Geometry.SmSchemeOver k) :
    (overBaseProductSymm X Y).hom.hom ≫ overBaseProduct.fst Y X =
      overBaseProduct.snd X Y := by
  change (pullbackSymmetry X.structMap Y.structMap).hom ≫
      pullback.fst Y.structMap X.structMap =
    pullback.snd X.structMap Y.structMap
  exact pullbackSymmetry_hom_comp_fst (f := X.structMap) (g := Y.structMap)

@[simp, reassoc] theorem overBaseProductSymm_hom_snd
    (X Y : Geometry.SmSchemeOver k) :
    (overBaseProductSymm X Y).hom.hom ≫ overBaseProduct.snd Y X =
      overBaseProduct.fst X Y := by
  change (pullbackSymmetry X.structMap Y.structMap).hom ≫
      pullback.snd Y.structMap X.structMap =
    pullback.fst X.structMap Y.structMap
  exact pullbackSymmetry_hom_comp_snd (f := X.structMap) (g := Y.structMap)

/-- An integral open-and-closed source subscheme of `X`. -/
structure IntegralClopenSourceSubscheme (X : Geometry.SmSchemeOver k) where
  carrier : Geometry.SmSchemeOver k
  immersion : carrier.scheme ⟶ X.scheme
  overBase : immersion ≫ X.structMap = carrier.structMap
  isOpenImmersion : IsOpenImmersion immersion
  isClosedImmersion : IsClosedImmersion immersion
  isIntegral : IsIntegral carrier.scheme

namespace IntegralClopenSourceSubscheme

abbrev toAmbient {X : Geometry.SmSchemeOver k}
    (sourceSubscheme : IntegralClopenSourceSubscheme X) :
    sourceSubscheme.carrier.scheme ⟶ X.scheme :=
  sourceSubscheme.immersion

/-- Compose a clopen integral source subscheme into a larger ambient smooth
scheme. -/
def comp {X : Geometry.SmSchemeOver k}
    (sourceSubscheme : IntegralClopenSourceSubscheme X)
    (inner : IntegralClopenSourceSubscheme sourceSubscheme.carrier) :
    IntegralClopenSourceSubscheme X where
  carrier := inner.carrier
  immersion := inner.toAmbient ≫ sourceSubscheme.toAmbient
    overBase := by
      calc
        inner.toAmbient ≫ sourceSubscheme.toAmbient ≫ X.structMap =
            inner.toAmbient ≫ (sourceSubscheme.toAmbient ≫ X.structMap) := by
              rw [Category.assoc]
      _ = inner.toAmbient ≫ sourceSubscheme.carrier.structMap := by
            rw [sourceSubscheme.overBase]
      _ = inner.carrier.structMap := by
            exact inner.overBase
  isOpenImmersion := by
    letI : IsOpenImmersion inner.toAmbient := inner.isOpenImmersion
    letI : IsOpenImmersion sourceSubscheme.toAmbient := sourceSubscheme.isOpenImmersion
    infer_instance
  isClosedImmersion := by
    letI : IsClosedImmersion inner.toAmbient := inner.isClosedImmersion
    letI : IsClosedImmersion sourceSubscheme.toAmbient := sourceSubscheme.isClosedImmersion
    infer_instance
  isIntegral := inner.isIntegral

/-- Package an open-and-closed smooth subscheme as an
`IntegralClopenSourceSubscheme`. -/
def ofOpen (X : Geometry.SmSchemeOver k) (U : X.scheme.Opens)
    [IsClosedImmersion U.ι] (hIntegral : IsIntegral U.toScheme) :
    IntegralClopenSourceSubscheme X where
  carrier := Geometry.SmSchemeOver.ofOpen X U
  immersion := U.ι
  overBase := rfl
  isOpenImmersion := inferInstance
  isClosedImmersion := inferInstance
  isIntegral := hIntegral

/-- Package a clopen integral smooth subscheme as an
`IntegralClopenSourceSubscheme`. -/
def ofClopen (X : Geometry.SmSchemeOver k) (U : X.scheme.Opens)
    (hU : IsClosed (U : Set X.scheme)) (hIntegral : IsIntegral U.toScheme) :
    IntegralClopenSourceSubscheme X := by
  letI : IsClosedImmersion U.ι := Geometry.SmSchemeOver.isClosedImmersion_ι_of_isClosed X U hU
  exact ofOpen X U hIntegral

end IntegralClopenSourceSubscheme

/-- A final-form source irreducible component of `X`.
This extends the integral clopen source subscheme layer with a genuine
componenthood field on the underlying topological space: the image must be an
irreducible component of `X.scheme`. -/
structure SourceIrreducibleComponent (X : Geometry.SmSchemeOver k)
    extends IntegralClopenSourceSubscheme X where
  range_mem_irreducibleComponents :
    Set.range immersion.base ∈ irreducibleComponents X.scheme

namespace SourceIrreducibleComponent

@[ext] theorem ext
    {X : Geometry.SmSchemeOver k}
    (C D : SourceIrreducibleComponent X)
    (hBase : C.toIntegralClopenSourceSubscheme = D.toIntegralClopenSourceSubscheme) :
    C = D := by
  cases C
  cases D
  cases hBase
  rfl

theorem extensionality
    {X : Geometry.SmSchemeOver k}
    (C D : SourceIrreducibleComponent X)
    (hBase : C.toIntegralClopenSourceSubscheme = D.toIntegralClopenSourceSubscheme) :
    C = D :=
  ext C D hBase

abbrev toAmbient {X : Geometry.SmSchemeOver k}
    (component : SourceIrreducibleComponent X) :
    component.carrier.scheme ⟶ X.scheme :=
  component.immersion

theorem range_eq_of_subset_range
    {X : Geometry.SmSchemeOver k}
    (C D : SourceIrreducibleComponent X)
    (hCD : Set.range C.toAmbient.base ⊆ Set.range D.toAmbient.base) :
    Set.range C.toAmbient.base = Set.range D.toAmbient.base := by
  exact Set.Subset.antisymm hCD <|
    by
      exact C.range_mem_irreducibleComponents.2
        D.range_mem_irreducibleComponents.1 hCD

/-- Package an open-and-closed integral subscheme whose image is a topological
irreducible component as a `SourceIrreducibleComponent`. -/
def ofOpen (X : Geometry.SmSchemeOver k) (U : X.scheme.Opens)
    [IsClosedImmersion U.ι] (hIntegral : IsIntegral U.toScheme)
    (hComponent : (U : Set X.scheme) ∈ irreducibleComponents X.scheme) :
    SourceIrreducibleComponent X where
  toIntegralClopenSourceSubscheme :=
    IntegralClopenSourceSubscheme.ofOpen X U hIntegral
  range_mem_irreducibleComponents := by
    convert hComponent using 1
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact u.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩

/-- Package a clopen integral smooth subscheme whose underlying set is an
irreducible component as a `SourceIrreducibleComponent`. -/
def ofClopen (X : Geometry.SmSchemeOver k) (U : X.scheme.Opens)
    (hU : IsClosed (U : Set X.scheme)) (hIntegral : IsIntegral U.toScheme)
    (hComponent : (U : Set X.scheme) ∈ irreducibleComponents X.scheme) :
    SourceIrreducibleComponent X := by
  letI : IsClosedImmersion U.ι := Geometry.SmSchemeOver.isClosedImmersion_ι_of_isClosed X U hU
  exact ofOpen X U hIntegral hComponent

/-- Package one topological irreducible component of a smooth scheme as a
source component, once that topological component has been identified as open,
closed, and integral as an open subscheme. -/
def ofTopologicalComponent (X : Geometry.SmSchemeOver k)
    (C : { C : Set X.scheme // C ∈ irreducibleComponents X.scheme })
    (hOpen : IsOpen C.1) (hClosed : IsClosed C.1)
    (hIntegral : IsIntegral (Scheme.Opens.toScheme (⟨C.1, hOpen⟩ : X.scheme.Opens))) :
    SourceIrreducibleComponent X :=
  ofClopen X (⟨C.1, hOpen⟩ : X.scheme.Opens) hClosed hIntegral C.2

@[simp] theorem range_ofTopologicalComponent
    (X : Geometry.SmSchemeOver k)
    (C : { C : Set X.scheme // C ∈ irreducibleComponents X.scheme })
    (hOpen : IsOpen C.1) (hClosed : IsClosed C.1)
    (hIntegral : IsIntegral (Scheme.Opens.toScheme (⟨C.1, hOpen⟩ : X.scheme.Opens))) :
    Set.range (ofTopologicalComponent X C hOpen hClosed hIntegral).toAmbient.base = C.1 := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact u.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

theorem toAmbient_overBase {X : Geometry.SmSchemeOver k}
    (component : SourceIrreducibleComponent X) :
    component.toAmbient ≫ X.structMap = component.carrier.structMap :=
  component.overBase

/-- Push a source irreducible component forward along a clopen immersion of
smooth schemes over the base field. Unlike `comp`, the intermediate ambient
scheme need not itself be integral. -/
def mapAlongClopen
    {X Y : Geometry.SmSchemeOver k}
    (f : SmOverHom Y X)
    [IsOpenImmersion f.hom]
    [IsClosedImmersion f.hom]
    (component : SourceIrreducibleComponent Y) :
    SourceIrreducibleComponent X where
  toIntegralClopenSourceSubscheme :=
    { carrier := component.carrier
        immersion := component.toAmbient ≫ f.hom
        overBase := by
          calc
            component.toAmbient ≫ f.hom ≫ X.structMap =
                component.toAmbient ≫ (f.hom ≫ X.structMap) := by
                  rw [Category.assoc]
          _ = component.toAmbient ≫ Y.structMap := by
                rw [f.over]
          _ = component.carrier.structMap := by
                exact component.toAmbient_overBase
      isOpenImmersion := by
        letI : IsOpenImmersion component.toAmbient := component.isOpenImmersion
        infer_instance
      isClosedImmersion := by
        letI : IsClosedImmersion component.toAmbient := component.isClosedImmersion
        infer_instance
      isIntegral := component.isIntegral }
  range_mem_irreducibleComponents := by
    rw [irreducibleComponents_eq_maximals_closed]
    refine ⟨⟨?_, ?_⟩, ?_⟩
      · letI : IsClosedImmersion (component.toAmbient ≫ f.hom) := by
          letI : IsClosedImmersion component.toAmbient := component.isClosedImmersion
          infer_instance
        exact (IsClosedImmersion.base_closed (f := component.toAmbient ≫ f.hom)).2
    · letI : IsIntegral component.carrier.scheme := component.isIntegral
      letI : IrreducibleSpace component.carrier.scheme := inferInstance
        have hcarrier : IsIrreducible (Set.univ : Set component.carrier.scheme) :=
          IrreducibleSpace.isIrreducible_univ component.carrier.scheme
        rw [show
            Set.range (component.toAmbient ≫ f.hom).base =
              (component.toAmbient ≫ f.hom).base '' Set.univ by
          ext y
          constructor
          · intro hy
            rcases hy with ⟨x, rfl⟩
            exact ⟨x, Set.mem_univ x, rfl⟩
          · intro hy
            rcases hy with ⟨x, _hx, rfl⟩
            exact ⟨x, rfl⟩]
        exact hcarrier.image
          ((component.toAmbient ≫ f.hom).base)
          (component.toAmbient ≫ f.hom).base.continuous.continuousOn
    · intro t ht hsubset
      have hsNonempty :
          (Set.range (component.toAmbient ≫ f.hom).base).Nonempty := by
        rcases component.range_mem_irreducibleComponents.1.nonempty with ⟨x, hx⟩
        exact ⟨f.hom.base x, by
          rcases hx with ⟨y, rfl⟩
          exact ⟨y, rfl⟩⟩
      rcases hsNonempty with ⟨x, hx⟩
      have hxt : x ∈ t := hsubset hx
        have hsOpen : IsOpen (Set.range (component.toAmbient ≫ f.hom).base) := by
          letI : IsOpenImmersion (component.toAmbient ≫ f.hom) := by
            letI : IsOpenImmersion component.toAmbient := component.isOpenImmersion
            infer_instance
          exact IsOpenImmersion.isOpen_range (component.toAmbient ≫ f.hom)
      have htSubsetClosure :
          t ⊆ closure (t ∩ Set.range (component.toAmbient ≫ f.hom).base) :=
        subset_closure_inter_of_isPreirreducible_of_isOpen
          ht.2.isPreirreducible hsOpen ⟨x, hxt, hx⟩
      have htsEq :
          t ∩ Set.range (component.toAmbient ≫ f.hom).base =
            Set.range (component.toAmbient ≫ f.hom).base := by
        ext y
        constructor
        · exact fun hy => hy.2
        · exact fun hy => ⟨hsubset hy, hy⟩
        have hclosure :
            closure (t ∩ Set.range (component.toAmbient ≫ f.hom).base) =
              Set.range (component.toAmbient ≫ f.hom).base := by
        rw [htsEq]
        letI : IsClosedImmersion (component.toAmbient ≫ f.hom) := by
          letI : IsClosedImmersion component.toAmbient := component.isClosedImmersion
          infer_instance
          exact (IsClosedImmersion.base_closed
            (f := component.toAmbient ≫ f.hom)).2.closure_eq
        rw [hclosure] at htSubsetClosure
        exact htSubsetClosure

@[simp] theorem mapAlongClopen_toAmbient
    {X Y : Geometry.SmSchemeOver k}
    (f : SmOverHom Y X)
    [IsOpenImmersion f.hom]
    [IsClosedImmersion f.hom]
    (component : SourceIrreducibleComponent Y) :
    (mapAlongClopen f component).toAmbient = component.toAmbient ≫ f.hom := rfl

@[simp] theorem range_mapAlongClopen
    {X Y : Geometry.SmSchemeOver k}
    (f : SmOverHom Y X)
    [IsOpenImmersion f.hom]
    [IsClosedImmersion f.hom]
    (component : SourceIrreducibleComponent Y) :
    Set.range (mapAlongClopen f component).toAmbient.base =
      Set.image f.hom.base (Set.range component.toAmbient.base) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨component.toAmbient.base y, ⟨y, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, rfl⟩

theorem isoOverAmbient_mapAlongClopen
    {X Y : Geometry.SmSchemeOver k}
    (f : SmOverHom Y X)
    [IsOpenImmersion f.hom]
    [IsClosedImmersion f.hom]
    {C D : SourceIrreducibleComponent Y}
    (h : SourceIrreducibleComponent.IsoOverAmbient C D) :
    SourceIrreducibleComponent.IsoOverAmbient
      (mapAlongClopen f C)
      (mapAlongClopen f D) where
    iso := h.iso
    hom_toAmbient := by
      change h.iso.hom ≫ (D.toAmbient ≫ f.hom) = C.toAmbient ≫ f.hom
      rw [← Category.assoc]
      exact congrArg (fun g => g ≫ f.hom) h.hom_toAmbient

theorem isoOverAmbient_of_mapAlongClopen
    {X Y : Geometry.SmSchemeOver k}
    (f : SmOverHom Y X)
    [IsOpenImmersion f.hom]
    [IsClosedImmersion f.hom]
    {C D : SourceIrreducibleComponent Y}
    (h :
      SourceIrreducibleComponent.IsoOverAmbient
        (mapAlongClopen f C)
        (mapAlongClopen f D)) :
    SourceIrreducibleComponent.IsoOverAmbient C D where
    iso := h.iso
    hom_toAmbient := by
      have hmapped : h.iso.hom ≫ (D.toAmbient ≫ f.hom) = C.toAmbient ≫ f.hom := by
        exact h.hom_toAmbient
      exact (cancel_mono f.hom).1 <| by
        rw [Category.assoc]
        exact hmapped

/-- Compose a source irreducible component of a clopen source subscheme into
the ambient smooth scheme. -/
def comp {X : Geometry.SmSchemeOver k}
    (sourceSubscheme : IntegralClopenSourceSubscheme X)
    (component : SourceIrreducibleComponent sourceSubscheme.carrier) :
    SourceIrreducibleComponent X where
  mapAlongClopen
    { hom := sourceSubscheme.toAmbient
      over := sourceSubscheme.overBase }
    component

/-- The carrier of a source irreducible component is itself locally
irreducible, because it is an irreducible space. -/
theorem locallyIrreducible_carrier
    {X : Geometry.SmSchemeOver k}
    (component : SourceIrreducibleComponent X) :
    Geometry.Topology.LocallyIrreducibleSpace component.carrier.scheme := by
  letI : IsIntegral component.carrier.scheme := component.isIntegral
  letI : IrreducibleSpace component.carrier.scheme := inferInstance
  intro x
  refine ⟨Set.univ, isOpen_univ, by trivial, ?_⟩
  exact
    (IrreducibleSpace.isIrreducible_univ component.carrier.scheme)

structure IsoOverAmbient {X : Geometry.SmSchemeOver k}
    (C D : SourceIrreducibleComponent X) where
  iso : C.carrier.scheme ≅ D.carrier.scheme
  hom_toAmbient : iso.hom ≫ D.toAmbient = C.toAmbient

noncomputable def isoOverAmbient_of_range_eq
    {X : Geometry.SmSchemeOver k}
    (C D : SourceIrreducibleComponent X)
    (hCD : Set.range C.toAmbient.base = Set.range D.toAmbient.base) :
    IsoOverAmbient C D where
  iso := by
    letI : IsOpenImmersion C.toAmbient := C.isOpenImmersion
    letI : IsOpenImmersion D.toAmbient := D.isOpenImmersion
    exact IsOpenImmersion.isoOfRangeEq C.toAmbient D.toAmbient hCD
  hom_toAmbient := by
    letI : IsOpenImmersion C.toAmbient := C.isOpenImmersion
    letI : IsOpenImmersion D.toAmbient := D.isOpenImmersion
    exact IsOpenImmersion.isoOfRangeEq_hom_fac C.toAmbient D.toAmbient hCD

noncomputable def isoOverAmbient_of_subset_range
    {X : Geometry.SmSchemeOver k}
    (C D : SourceIrreducibleComponent X)
    (hCD : Set.range C.toAmbient.base ⊆ Set.range D.toAmbient.base) :
    IsoOverAmbient C D :=
  isoOverAmbient_of_range_eq C D (range_eq_of_subset_range C D hCD)

namespace IsoOverAmbient

def refl {X : Geometry.SmSchemeOver k}
    (C : SourceIrreducibleComponent X) : IsoOverAmbient C C where
  iso := Iso.refl _
  hom_toAmbient := by rw [Category.id_comp]

theorem range_eq {X : Geometry.SmSchemeOver k}
    {C D : SourceIrreducibleComponent X}
    (h : IsoOverAmbient C D) :
    Set.range C.toAmbient.base = Set.range D.toAmbient.base := by
  apply SourceIrreducibleComponent.range_eq_of_subset_range C D
  rintro x ⟨y, rfl⟩
    refine ⟨h.iso.inv.base y, ?_⟩
    have := congrArg Scheme.Hom.base h.hom_toAmbient
    change (h.iso.hom ≫ D.toAmbient).base = C.toAmbient.base at this
    have hpoint := congrArg (fun f => f (h.iso.inv.base y)) this.symm
    change C.toAmbient.base (h.iso.inv.base y) =
      D.toAmbient.base (h.iso.hom.base (h.iso.inv.base y)) at hpoint
    rw [Iso.hom_inv_id_assoc] at hpoint
    exact hpoint

def symm {X : Geometry.SmSchemeOver k}
    {C D : SourceIrreducibleComponent X} (h : IsoOverAmbient C D) :
    IsoOverAmbient D C where
  iso := h.iso.symm
    hom_toAmbient := by
      calc
        h.iso.inv ≫ C.toAmbient = h.iso.inv ≫ (h.iso.hom ≫ D.toAmbient) := by
          rw [h.hom_toAmbient]
        _ = D.toAmbient := by
          rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

def trans {X : Geometry.SmSchemeOver k}
    {C D E : SourceIrreducibleComponent X}
    (hCD : IsoOverAmbient C D) (hDE : IsoOverAmbient D E) :
    IsoOverAmbient C E where
  iso := hCD.iso ≪≫ hDE.iso
    hom_toAmbient := by
      calc
        (hCD.iso ≪≫ hDE.iso).hom ≫ E.toAmbient = hCD.iso.hom ≫ (hDE.iso.hom ≫ E.toAmbient) := by
          rfl
      _ = hCD.iso.hom ≫ D.toAmbient := by rw [hDE.hom_toAmbient]
      _ = C.toAmbient := by rw [hCD.hom_toAmbient]

theorem hom_structMap {X : Geometry.SmSchemeOver k}
    {C D : SourceIrreducibleComponent X} (h : IsoOverAmbient C D) :
    h.iso.hom ≫ D.carrier.structMap = C.carrier.structMap := by
  calc
      h.iso.hom ≫ D.carrier.structMap = h.iso.hom ≫ (D.toAmbient ≫ X.structMap) := by
        rw [D.toAmbient_overBase]
      _ = (h.iso.hom ≫ D.toAmbient) ≫ X.structMap := by rw [Category.assoc]
    _ = C.toAmbient ≫ X.structMap := by rw [h.hom_toAmbient]
    _ = C.carrier.structMap := C.toAmbient_overBase

noncomputable def overBaseProductIso {X : Geometry.SmSchemeOver k} {Y : Geometry.SmSchemeOver k}
    {C D : SourceIrreducibleComponent X} (h : IsoOverAmbient C D) :
    pullback C.carrier.structMap Y.structMap ≅ pullback D.carrier.structMap Y.structMap := by
    refine asIso <|
      pullback.map C.carrier.structMap Y.structMap D.carrier.structMap Y.structMap
        h.iso.hom (𝟙 Y.scheme) (𝟙 (Spec (CommRingCat.of k))) ?_ ?_
    · exact h.hom_structMap.symm
    · rw [Category.id_comp, Category.comp_id]

@[simp] theorem overBaseProductIso_hom_fst {X : Geometry.SmSchemeOver k}
    {Y : Geometry.SmSchemeOver k} {C D : SourceIrreducibleComponent X}
      (h : IsoOverAmbient C D) :
      (h.overBaseProductIso (Y := Y)).hom ≫ pullback.fst D.carrier.structMap Y.structMap =
        pullback.fst C.carrier.structMap Y.structMap ≫ h.iso.hom := by
    change
      pullback.map C.carrier.structMap Y.structMap D.carrier.structMap Y.structMap
          h.iso.hom (𝟙 Y.scheme) (𝟙 (Spec (CommRingCat.of k))) _ _ ≫
        pullback.fst D.carrier.structMap Y.structMap =
      pullback.fst C.carrier.structMap Y.structMap ≫ h.iso.hom
    rw [pullback.map_fst]

@[simp] theorem overBaseProductIso_hom_snd {X : Geometry.SmSchemeOver k}
    {Y : Geometry.SmSchemeOver k} {C D : SourceIrreducibleComponent X}
      (h : IsoOverAmbient C D) :
      (h.overBaseProductIso (Y := Y)).hom ≫ pullback.snd D.carrier.structMap Y.structMap =
        pullback.snd C.carrier.structMap Y.structMap := by
    change
      pullback.map C.carrier.structMap Y.structMap D.carrier.structMap Y.structMap
          h.iso.hom (𝟙 Y.scheme) (𝟙 (Spec (CommRingCat.of k))) _ _ ≫
        pullback.snd D.carrier.structMap Y.structMap =
      pullback.snd C.carrier.structMap Y.structMap
    rw [pullback.map_snd]
    rw [Category.comp_id]

/-- Explicit compatibility between represented source components and the
induced fiber products with a target. -/
structure CompatibleOverBaseProductIso {X : Geometry.SmSchemeOver k}
    {Y : Geometry.SmSchemeOver k}
    (C D : SourceIrreducibleComponent X) where
  sourceIso : IsoOverAmbient C D
  iso : overBaseProduct C.carrier Y ≅ overBaseProduct D.carrier Y
  hom_fst :
    iso.hom ≫ overBaseProduct.fst D.carrier Y =
      overBaseProduct.fst C.carrier Y ≫ sourceIso.iso.hom
  hom_snd :
    iso.hom ≫ overBaseProduct.snd D.carrier Y =
      overBaseProduct.snd C.carrier Y

namespace CompatibleOverBaseProductIso

  /-- Reflexive compatibility of source components and their fiber products. -/
  def refl {X : Geometry.SmSchemeOver k} {Y : Geometry.SmSchemeOver k}
      (C : SourceIrreducibleComponent X) : CompatibleOverBaseProductIso (Y := Y) C C where
    sourceIso := IsoOverAmbient.refl C
    iso := Iso.refl _
    hom_fst := by rw [Category.id_comp, Category.comp_id]
    hom_snd := by rw [Category.id_comp]

/-- Symmetry of compatibility of source components and their fiber products. -/
def symm {X : Geometry.SmSchemeOver k} {Y : Geometry.SmSchemeOver k}
    {C D : SourceIrreducibleComponent X}
    (h : CompatibleOverBaseProductIso (Y := Y) C D) :
    CompatibleOverBaseProductIso (Y := Y) D C where
  sourceIso := h.sourceIso.symm
  iso := h.iso.symm
    hom_fst := by
      have hleft :
          h.iso.inv ≫ overBaseProduct.fst C.carrier Y ≫ h.sourceIso.iso.hom =
            overBaseProduct.fst D.carrier Y := by
        rw [Category.assoc]
        rw [h.hom_fst]
        rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      have hright :
          h.iso.inv ≫ overBaseProduct.fst C.carrier Y =
            overBaseProduct.fst D.carrier Y ≫ h.sourceIso.iso.inv := by
        rw [← hleft]
        rw [← Category.assoc, Iso.hom_inv_id, Category.comp_id]
      exact hright
    hom_snd := by
      rw [Category.assoc]
      rw [h.hom_snd]
      rw [Iso.inv_hom_id_assoc]

/-- Transitivity of compatibility of source components and their fiber products. -/
def trans {X : Geometry.SmSchemeOver k} {Y : Geometry.SmSchemeOver k}
    {C D E : SourceIrreducibleComponent X}
    (hCD : CompatibleOverBaseProductIso (Y := Y) C D)
    (hDE : CompatibleOverBaseProductIso (Y := Y) D E) :
    CompatibleOverBaseProductIso (Y := Y) C E where
  sourceIso := hCD.sourceIso.trans hDE.sourceIso
  iso := hCD.iso ≪≫ hDE.iso
  hom_fst := by
    calc
        (hCD.iso ≪≫ hDE.iso).hom ≫ overBaseProduct.fst E.carrier Y
            = hCD.iso.hom ≫ (hDE.iso.hom ≫ overBaseProduct.fst E.carrier Y) := by
              rfl
      _ = hCD.iso.hom ≫
          (overBaseProduct.fst D.carrier Y ≫ hDE.sourceIso.iso.hom) := by
            rw [hDE.hom_fst]
        _ = (hCD.iso.hom ≫ overBaseProduct.fst D.carrier Y) ≫ hDE.sourceIso.iso.hom := by
              rw [Category.assoc]
      _ = (overBaseProduct.fst C.carrier Y ≫ hCD.sourceIso.iso.hom) ≫
          hDE.sourceIso.iso.hom := by
            rw [hCD.hom_fst]
        _ = overBaseProduct.fst C.carrier Y ≫
            (hCD.sourceIso.iso ≪≫ hDE.sourceIso.iso).hom := by
              rw [Category.assoc]
  hom_snd := by
    calc
        (hCD.iso ≪≫ hDE.iso).hom ≫ overBaseProduct.snd E.carrier Y
            = hCD.iso.hom ≫ (hDE.iso.hom ≫ overBaseProduct.snd E.carrier Y) := by
              rfl
      _ = hCD.iso.hom ≫ overBaseProduct.snd D.carrier Y := by rw [hDE.hom_snd]
      _ = overBaseProduct.snd C.carrier Y := by rw [hCD.hom_snd]

/-- The canonical fiber-product compatibility induced by a source-component
isomorphism over the ambient source. -/
def ofIsoOverAmbient {X : Geometry.SmSchemeOver k} {Y : Geometry.SmSchemeOver k}
    {C D : SourceIrreducibleComponent X} (h : IsoOverAmbient C D) :
    CompatibleOverBaseProductIso (Y := Y) C D where
  sourceIso := h
  iso := h.overBaseProductIso (Y := Y)
  hom_fst := by exact h.overBaseProductIso_hom_fst (Y := Y)
  hom_snd := by exact h.overBaseProductIso_hom_snd (Y := Y)

end CompatibleOverBaseProductIso

end IsoOverAmbient

end SourceIrreducibleComponent

/-- Product of two integral clopen source subschemes over `Spec k`. -/
def productIntegralClopenSourceSubscheme
    {X Y : Geometry.SmSchemeOver k}
    (C : IntegralClopenSourceSubscheme X)
    (D : IntegralClopenSourceSubscheme Y)
    (hIntegral : IsIntegral (overBaseProduct C.carrier D.carrier)) :
    IntegralClopenSourceSubscheme (overBaseProductObject X Y) where
  carrier := overBaseProductObject C.carrier D.carrier
  immersion :=
    (overBaseProductMap
      { hom := C.toAmbient
        over := C.overBase }
      { hom := D.toAmbient
        over := D.overBase }).hom
    overBase := by
      change
        (overBaseProductMap
          { hom := C.toAmbient
            over := C.overBase }
          { hom := D.toAmbient
            over := D.overBase }).hom ≫
          (overBaseProductObject X Y).structMap =
        (overBaseProductObject C.carrier D.carrier).structMap
      exact (overBaseProductMap
        { hom := C.toAmbient
          over := C.overBase }
        { hom := D.toAmbient
          over := D.overBase }).over
  isOpenImmersion := by
    letI : MorphismProperty.IsStableUnderBaseChange @IsOpenImmersion :=
      AlgebraicGeometry.isOpenImmersion_stableUnderBaseChange
    letI : MorphismProperty.IsStableUnderComposition @IsOpenImmersion := inferInstance
    dsimp [overBaseProductMap]
    exact MorphismProperty.pullback_map
      (P := @IsOpenImmersion)
      C.isOpenImmersion D.isOpenImmersion C.overBase.symm D.overBase.symm
  isClosedImmersion := by
    letI : MorphismProperty.IsStableUnderBaseChange @IsClosedImmersion :=
      IsClosedImmersion.isStableUnderBaseChange
    letI : MorphismProperty.IsStableUnderComposition @IsClosedImmersion := inferInstance
    dsimp [overBaseProductMap]
    exact MorphismProperty.pullback_map
      (P := @IsClosedImmersion)
      C.isClosedImmersion D.isClosedImmersion C.overBase.symm D.overBase.symm
  isIntegral := hIntegral

@[simp] theorem productIntegralClopenSourceSubscheme_toAmbient
    {X Y : Geometry.SmSchemeOver k}
    (C : IntegralClopenSourceSubscheme X)
    (D : IntegralClopenSourceSubscheme Y)
    (hIntegral : IsIntegral (overBaseProduct C.carrier D.carrier)) :
    (productIntegralClopenSourceSubscheme C D hIntegral).toAmbient =
      (overBaseProductMap
        { hom := C.toAmbient
          over := C.overBase }
        { hom := D.toAmbient
          over := D.overBase }).hom := by
  rfl

@[simp, reassoc] theorem productIntegralClopenSourceSubscheme_fst
    {X Y : Geometry.SmSchemeOver k}
    (C : IntegralClopenSourceSubscheme X)
    (D : IntegralClopenSourceSubscheme Y)
    (hIntegral : IsIntegral (overBaseProduct C.carrier D.carrier)) :
    (productIntegralClopenSourceSubscheme C D hIntegral).toAmbient ≫
        overBaseProduct.fst X Y =
      overBaseProduct.fst C.carrier D.carrier ≫ C.toAmbient := by
  change
    (overBaseProductMap
      { hom := C.toAmbient
        over := C.overBase }
      { hom := D.toAmbient
        over := D.overBase }).hom ≫ overBaseProduct.fst X Y =
        overBaseProduct.fst C.carrier D.carrier ≫ C.toAmbient
    rw [pullback.map_fst]

@[simp, reassoc] theorem productIntegralClopenSourceSubscheme_snd
    {X Y : Geometry.SmSchemeOver k}
    (C : IntegralClopenSourceSubscheme X)
    (D : IntegralClopenSourceSubscheme Y)
    (hIntegral : IsIntegral (overBaseProduct C.carrier D.carrier)) :
      (productIntegralClopenSourceSubscheme C D hIntegral).toAmbient ≫
          overBaseProduct.snd X Y =
        overBaseProduct.snd C.carrier D.carrier ≫ D.toAmbient := by
    change
      (overBaseProductMap
        { hom := C.toAmbient
          over := C.overBase }
        { hom := D.toAmbient
          over := D.overBase }).hom ≫ overBaseProduct.snd X Y =
        overBaseProduct.snd C.carrier D.carrier ≫ D.toAmbient
    rw [pullback.map_snd]

/-- A restricted owner hypothesis asserting that a source irreducible component
remains integral after product with any source irreducible component. This is
the exact extra data needed for the current product-source-component route,
without asserting any false global product-integrality theorem. -/
structure ProductStableSourceComponent (X : Geometry.SmSchemeOver k) where
  component : SourceIrreducibleComponent X
  product_isIntegral :
    ∀ {Y : Geometry.SmSchemeOver k} (other : SourceIrreducibleComponent Y),
      IsIntegral (overBaseProduct component.carrier other.carrier)

theorem productStableSourceComponent_product
    {X Y : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y) :
    IsIntegral (overBaseProduct C.component.carrier D.carrier) :=
  C.product_isIntegral D

private theorem isIrreducibleComponent_of_clopen_irreducible
    {T : Type u} [TopologicalSpace T]
    {s : Set T}
    (hsClosed : IsClosed s)
    (hsOpen : IsOpen s)
    (hsIrred : IsIrreducible s) :
    s ∈ irreducibleComponents T := by
  rw [irreducibleComponents_eq_maximals_closed]
  refine ⟨⟨hsClosed, hsIrred⟩, ?_⟩
  intro t ht hst
  have hsNonempty : s.Nonempty := hsIrred.nonempty
  rcases hsNonempty with ⟨x, hx⟩
  have hxt : x ∈ t := hst hx
  have htSubsetClosure :
      t ⊆ closure (t ∩ s) :=
    subset_closure_inter_of_isPreirreducible_of_isOpen
      ht.2.isPreirreducible hsOpen ⟨x, hxt, hx⟩
  have htsEq : t ∩ s = s := by
    ext y
    constructor
    · exact fun hy => hy.2
    · exact fun hy => ⟨hst hy, hy⟩
    have hclosure : closure (t ∩ s) = s := by
      rw [htsEq]
      exact hsClosed.closure_eq
    rw [hclosure] at htSubsetClosure
    exact htSubsetClosure

/-- Product source component constructed from a product-stable source component
and an arbitrary source irreducible component in the second factor. -/
def productSourceIrreducibleComponent_of_geometricallyIntegral
    {X Y : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y) :
    SourceIrreducibleComponent (overBaseProductObject X Y) where
  toIntegralClopenSourceSubscheme :=
    productIntegralClopenSourceSubscheme
      C.component.toIntegralClopenSourceSubscheme
      D.toIntegralClopenSourceSubscheme
      (C.product_isIntegral D)
  range_mem_irreducibleComponents := by
    let S :=
      productIntegralClopenSourceSubscheme
        C.component.toIntegralClopenSourceSubscheme
        D.toIntegralClopenSourceSubscheme
        (C.product_isIntegral D)
    refine isIrreducibleComponent_of_clopen_irreducible ?_ ?_ ?_
    · letI : IsClosedImmersion S.immersion := S.isClosedImmersion
      exact (IsClosedImmersion.base_closed (f := S.immersion)).2
      · letI : IsOpenImmersion S.immersion := S.isOpenImmersion
        exact IsOpenImmersion.isOpen_range S.immersion
      · letI : IsIntegral S.carrier.scheme := S.isIntegral
        letI : IrreducibleSpace S.carrier.scheme := inferInstance
        have hcarrier : IsIrreducible (Set.univ : Set S.carrier.scheme) :=
          IrreducibleSpace.isIrreducible_univ S.carrier.scheme
        rw [show Set.range S.immersion.base = S.immersion.base '' Set.univ by
          ext y
          constructor
          · intro hy
            rcases hy with ⟨x, rfl⟩
            exact ⟨x, Set.mem_univ x, rfl⟩
          · intro hy
            rcases hy with ⟨x, _hx, rfl⟩
            exact ⟨x, rfl⟩]
        exact hcarrier.image S.immersion.base S.immersion.base.continuous.continuousOn

/-- Product source component constructed from a product-stable left factor. -/
abbrev productSourceIrreducibleComponent
    {X Y : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y) :
    SourceIrreducibleComponent (overBaseProductObject X Y) :=
  productSourceIrreducibleComponent_of_geometricallyIntegral C D

@[simp] theorem productSourceIrreducibleComponent_fst_image
    {X Y : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y) :
    (productSourceIrreducibleComponent C D).toAmbient ≫ overBaseProduct.fst X Y =
      overBaseProduct.fst C.component.carrier D.carrier ≫ C.component.toAmbient := by
  exact productIntegralClopenSourceSubscheme_fst
    C.component.toIntegralClopenSourceSubscheme
    D.toIntegralClopenSourceSubscheme
    (C.product_isIntegral D)

@[simp] theorem productSourceIrreducibleComponent_snd_image
    {X Y : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y) :
    (productSourceIrreducibleComponent C D).toAmbient ≫ overBaseProduct.snd X Y =
      overBaseProduct.snd C.component.carrier D.carrier ≫ D.toAmbient := by
  exact productIntegralClopenSourceSubscheme_snd
    C.component.toIntegralClopenSourceSubscheme
    D.toIntegralClopenSourceSubscheme
    (C.product_isIntegral D)

lemma productSourceIrreducibleComponent_toAmbient_fst_apply
    {X Y : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y)
    (w : (productSourceIrreducibleComponent C D).carrier.scheme.carrier) :
    C.component.toAmbient.base ((overBaseProduct.fst C.component.carrier D.carrier).base w) =
      (overBaseProduct.fst X Y).base
        ((productSourceIrreducibleComponent C D).toAmbient.base w) := by
  change
    (overBaseProduct.fst C.component.carrier D.carrier ≫ C.component.toAmbient).base w =
      ((productSourceIrreducibleComponent C D).toAmbient ≫ overBaseProduct.fst X Y).base w
  rw [productSourceIrreducibleComponent_fst_image]
  rfl

lemma productSourceIrreducibleComponent_toAmbient_snd_apply
    {X Y : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y)
    (w : (productSourceIrreducibleComponent C D).carrier.scheme.carrier) :
    D.toAmbient.base ((overBaseProduct.snd C.component.carrier D.carrier).base w) =
      (overBaseProduct.snd X Y).base
        ((productSourceIrreducibleComponent C D).toAmbient.base w) := by
  change
    (overBaseProduct.snd C.component.carrier D.carrier ≫ D.toAmbient).base w =
      ((productSourceIrreducibleComponent C D).toAmbient ≫ overBaseProduct.snd X Y).base w
  rw [productSourceIrreducibleComponent_snd_image]
  rfl

@[simp] theorem productSourceIrreducibleComponent_support_eq
    {X Y : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y) :
    (productSourceIrreducibleComponent C D).carrier =
      overBaseProductObject C.component.carrier D.carrier := by
  rfl

theorem productSourceIrreducibleComponent_proj_mem_of_mem_range
    {X Y : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y)
    {x : (overBaseProductObject X Y).scheme.carrier}
    (hx : x ∈ Set.range (productSourceIrreducibleComponent C D).toAmbient.base) :
    (overBaseProduct.fst X Y).base x ∈ Set.range C.component.toAmbient.base ∧
      (overBaseProduct.snd X Y).base x ∈ Set.range D.toAmbient.base := by
  rcases hx with ⟨z, rfl⟩
  constructor
  · refine ⟨(overBaseProduct.fst C.component.carrier D.carrier).base z, ?_⟩
    exact productSourceIrreducibleComponent_toAmbient_fst_apply (C := C) (D := D) z
  · refine ⟨(overBaseProduct.snd C.component.carrier D.carrier).base z, ?_⟩
    exact productSourceIrreducibleComponent_toAmbient_snd_apply (C := C) (D := D) z

theorem productSourceIrreducibleComponent_mem_range_of_proj_mem
    {X Y : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y)
    {x : (overBaseProductObject X Y).scheme.carrier}
    (hfst : (overBaseProduct.fst X Y).base x ∈ Set.range C.component.toAmbient.base)
    (hsnd : (overBaseProduct.snd X Y).base x ∈ Set.range D.toAmbient.base) :
    x ∈ Set.range (productSourceIrreducibleComponent C D).toAmbient.base := by
  have hRange :
      Set.range (productSourceIrreducibleComponent C D).toAmbient.base =
        (overBaseProduct.fst X Y).base ⁻¹' Set.range C.component.toAmbient.base ∩
          (overBaseProduct.snd X Y).base ⁻¹' Set.range D.toAmbient.base := by
    change
      Set.range
          (pullback.map C.component.carrier.structMap D.carrier.structMap
            X.structMap Y.structMap C.component.toAmbient D.toAmbient (𝟙 _)
            (by
              rw [Category.comp_id]
              exact C.component.overBase.symm)
            (by
              rw [Category.comp_id]
              exact D.overBase.symm)).base =
        (pullback.fst X.structMap Y.structMap).base ⁻¹'
            Set.range C.component.toAmbient.base ∩
          (pullback.snd X.structMap Y.structMap).base ⁻¹'
            Set.range D.toAmbient.base
    change Set.range
        (productIntegralClopenSourceSubscheme C D).toAmbient.base =
      (overBaseProduct.fst X Y).base ⁻¹'
          Set.range C.component.toAmbient.base ∩
        (overBaseProduct.snd X Y).base ⁻¹'
          Set.range D.toAmbient.base
    exact
      AlgebraicGeometry.Scheme.Pullback.range_map
        C.component.carrier.structMap D.carrier.structMap
        X.structMap Y.structMap C.component.toAmbient D.toAmbient (𝟙 _)
        (by
          rw [Category.comp_id]
          exact C.component.overBase.symm)
        (by
          rw [Category.comp_id]
          exact D.overBase.symm)
  rw [hRange]
  exact ⟨hfst, hsnd⟩

theorem productSourceIrreducibleComponent_mem_range_iff
    {X Y : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y)
    {x : (overBaseProductObject X Y).scheme.carrier} :
    x ∈ Set.range (productSourceIrreducibleComponent C D).toAmbient.base ↔
      (overBaseProduct.fst X Y).base x ∈ Set.range C.component.toAmbient.base ∧
        (overBaseProduct.snd X Y).base x ∈ Set.range D.toAmbient.base := by
  constructor
  · exact productSourceIrreducibleComponent_proj_mem_of_mem_range C D
  · intro hx
    exact productSourceIrreducibleComponent_mem_range_of_proj_mem C D hx.1 hx.2

private theorem exists_product_component_point
    {X Y : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y)
    (xC : C.component.carrier.scheme.carrier)
    (yD : D.carrier.scheme.carrier)
    (hbase : C.component.carrier.structMap.base xC =
      D.carrier.structMap.base yD) :
    ∃ z : (productSourceIrreducibleComponent C D).carrier.scheme.carrier,
      (overBaseProduct.fst C.component.carrier D.carrier).base z = xC ∧
      (overBaseProduct.snd C.component.carrier D.carrier).base z = yD := by
  rcases AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback
      (f := C.component.carrier.structMap)
      (g := D.carrier.structMap) xC yD hbase with ⟨z, hzfst, hzsnd⟩
  exact ⟨z, hzfst, hzsnd⟩

theorem productSourceIrreducibleComponent_range_image_fst
    {X Y : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y) :
    Set.image (overBaseProduct.fst X Y).base
        (Set.range (productSourceIrreducibleComponent C D).toAmbient.base) =
      Set.range C.component.toAmbient.base := by
  ext x
  constructor
  · rintro ⟨z, ⟨w, rfl⟩, rfl⟩
    refine ⟨(overBaseProduct.fst C.component.carrier D.carrier).base w, ?_⟩
    exact productSourceIrreducibleComponent_toAmbient_fst_apply (C := C) (D := D) w
  · intro hx
    rcases D.range_mem_irreducibleComponents.1.nonempty with ⟨y, hy⟩
    rcases hy with ⟨yD, hyD⟩
    rcases hx with ⟨xC, rfl⟩
    have hbase :
        C.component.carrier.structMap.base xC =
          D.carrier.structMap.base yD := by
      exact Subsingleton.elim _ _
    rcases exists_product_component_point C D xC yD hbase with ⟨z, hzfst, _⟩
    refine ⟨(productSourceIrreducibleComponent C D).toAmbient.base z, ?_, ?_⟩
    · exact ⟨z, rfl⟩
    · calc
        (overBaseProduct.fst X Y).base ((productSourceIrreducibleComponent C D).toAmbient.base z)
            = C.component.toAmbient.base
                ((overBaseProduct.fst C.component.carrier D.carrier).base z) := by
                  exact (productSourceIrreducibleComponent_toAmbient_fst_apply
                    (C := C) (D := D) z).symm
        _ = C.component.toAmbient.base xC := by rw [hzfst]

theorem productSourceIrreducibleComponent_range_image_snd
    {X Y : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y) :
    Set.image (overBaseProduct.snd X Y).base
        (Set.range (productSourceIrreducibleComponent C D).toAmbient.base) =
      Set.range D.toAmbient.base := by
  ext y
  constructor
  · rintro ⟨z, ⟨w, rfl⟩, rfl⟩
    refine ⟨(overBaseProduct.snd C.component.carrier D.carrier).base w, ?_⟩
    exact productSourceIrreducibleComponent_toAmbient_snd_apply (C := C) (D := D) w
  · intro hy
    rcases C.component.range_mem_irreducibleComponents.1.nonempty with ⟨x, hx⟩
    rcases hx with ⟨xC, hxC⟩
    rcases hy with ⟨yD, rfl⟩
    have hbase :
        C.component.carrier.structMap.base xC =
          D.carrier.structMap.base yD := by
      exact Subsingleton.elim _ _
    rcases exists_product_component_point C D xC yD hbase with ⟨z, _, hzsnd⟩
    refine ⟨(productSourceIrreducibleComponent C D).toAmbient.base z, ?_, ?_⟩
    · exact ⟨z, rfl⟩
    · calc
        (overBaseProduct.snd X Y).base ((productSourceIrreducibleComponent C D).toAmbient.base z)
            = D.toAmbient.base
                ((overBaseProduct.snd C.component.carrier D.carrier).base z) := by
                  exact (productSourceIrreducibleComponent_toAmbient_snd_apply
                    (C := C) (D := D) z).symm
        _ = D.toAmbient.base yD := by rw [hzsnd]

private theorem subset_of_irreducible_inter_clopen_nonempty
    {T : Type u} [TopologicalSpace T]
    {s t : Set T}
    (hs : IsIrreducible s)
    (htOpen : IsOpen t)
    (htClosed : IsClosed t)
    (hst : (s ∩ t).Nonempty) :
    s ⊆ t := by
  have hsPre : IsPreirreducible s := hs.isPreirreducible
  have hsUnion : s ⊆ t ∪ tᶜ := by
    intro x hx
    by_cases hxt : x ∈ t
    · exact Set.mem_union_left _ hxt
    · exact Set.mem_union_right _ hxt
  rcases (isPreirreducible_iff_isClosed_union_isClosed.mp hsPre)
      t tᶜ htClosed htOpen.isClosed_compl hsUnion with hsT | hsTc
  · exact hsT
  · exfalso
    rcases hst with ⟨x, hxS, hxT⟩
    exact hsTc hxS hxT

/-- A certified finite irreducible-component decomposition of `X`.
This is the first abstraction strong enough to state the component-sum identity
canonically enough for downstream use: the chosen finite family must represent
every source irreducible component up to isomorphism over `X`, and it must not
contain duplicate representatives up to that same equivalence. The record also
stores the honest topological content of the decomposition: the listed
component images cover `X`, and distinct listed components have disjoint
images. -/
structure FiniteIrreducibleComponentDecomposition (X : Geometry.SmSchemeOver k) where
  components : Finset (SourceIrreducibleComponent X)
  covers :
    ∀ x : X.scheme.carrier,
      ∃ component ∈ components, x ∈ Set.range component.toAmbient.base
  pairwise_disjoint :
    ∀ {C D : SourceIrreducibleComponent X},
      C ∈ components →
      D ∈ components →
      C ≠ D →
        Disjoint (Set.range C.toAmbient.base) (Set.range D.toAmbient.base)
  exhaustive :
    (component : SourceIrreducibleComponent X) →
      Σ listed : { listed : SourceIrreducibleComponent X // listed ∈ components },
        SourceIrreducibleComponent.IsoOverAmbient component listed.1
  no_equivalent_duplicates :
    ∀ {C D : SourceIrreducibleComponent X},
      C ∈ components →
      D ∈ components →
      SourceIrreducibleComponent.IsoOverAmbient C D →
        C = D

namespace FiniteIrreducibleComponentDecomposition

variable {X : Geometry.SmSchemeOver k}

/-- Choose the listed representative supplied by exhaustivity for any source
component. -/
def listedRepresentative (D : FiniteIrreducibleComponentDecomposition X)
    (component : SourceIrreducibleComponent X) :
    { listed : SourceIrreducibleComponent X // listed ∈ D.components } :=
  (D.exhaustive component).1

/-- The ambient-compatible isomorphism from a source component to its chosen
listed representative. -/
def listedRepresentativeIso (D : FiniteIrreducibleComponentDecomposition X)
    (component : SourceIrreducibleComponent X) :
    SourceIrreducibleComponent.IsoOverAmbient component (D.listedRepresentative component).1 :=
  (D.exhaustive component).2

@[simp] theorem listedRepresentative_mem
    (D : FiniteIrreducibleComponentDecomposition X)
    (component : SourceIrreducibleComponent X) :
    (D.listedRepresentative component).1 ∈ D.components :=
  (D.listedRepresentative component).2

theorem listedRepresentative_eq_of_iso
    (D : FiniteIrreducibleComponentDecomposition X)
    {component listed : SourceIrreducibleComponent X}
    (hlisted : listed ∈ D.components)
    (hiso : SourceIrreducibleComponent.IsoOverAmbient component listed) :
    (D.listedRepresentative component).1 = listed := by
  exact D.no_equivalent_duplicates
    (D.listedRepresentative_mem component) hlisted
    ((D.listedRepresentativeIso component).symm.trans hiso)

theorem listedRepresentative_eq_self_of_mem
    (D : FiniteIrreducibleComponentDecomposition X)
    {component : SourceIrreducibleComponent X}
    (hcomponent : component ∈ D.components) :
    (D.listedRepresentative component).1 = component :=
  D.listedRepresentative_eq_of_iso hcomponent
    (SourceIrreducibleComponent.IsoOverAmbient.refl component)

theorem disjoint_of_mem_ne
    (D : FiniteIrreducibleComponentDecomposition X)
    {C D' : SourceIrreducibleComponent X}
    (hC : C ∈ D.components) (hD' : D' ∈ D.components) (hneq : C ≠ D') :
    Disjoint (Set.range C.toAmbient.base) (Set.range D'.toAmbient.base) :=
  D.pairwise_disjoint hC hD' hneq

/-- Construct a finite source-component decomposition directly from the
topological irreducible components of `X`.  The hypotheses are exactly the
geometric content needed to turn those topological components into clopen
integral source subschemes; the finiteness, cover, disjointness, exhaustivity,
and uniqueness clauses are then consequences of irreducible-component
maximality. -/
noncomputable def ofTopologicalComponents
    (X : Geometry.SmSchemeOver k)
    (hFinite : (irreducibleComponents X.scheme).Finite)
    (hOpen :
      ∀ C : { C : Set X.scheme // C ∈ irreducibleComponents X.scheme },
        IsOpen C.1)
    (hClosed :
      ∀ C : { C : Set X.scheme // C ∈ irreducibleComponents X.scheme },
        IsClosed C.1)
    (hIntegral :
      ∀ C : { C : Set X.scheme // C ∈ irreducibleComponents X.scheme },
        IsIntegral (Scheme.Opens.toScheme (⟨C.1, hOpen C⟩ : X.scheme.Opens))) :
    FiniteIrreducibleComponentDecomposition X := by
  classical
  let Index := { C : Set X.scheme // C ∈ irreducibleComponents X.scheme }
  letI : Fintype Index := hFinite.fintype
  letI : DecidableEq Index := Classical.decEq Index
  let source : Index → SourceIrreducibleComponent X :=
    fun C => SourceIrreducibleComponent.ofTopologicalComponent
      X C (hOpen C) (hClosed C) (hIntegral C)
  let components : Finset (SourceIrreducibleComponent X) :=
    Finset.univ.image source
  have hsource_range :
      ∀ C : Index, Set.range (source C).toAmbient.base = C.1 := by
    intro C
    exact SourceIrreducibleComponent.range_ofTopologicalComponent
      X C (hOpen C) (hClosed C) (hIntegral C)
  refine
    { components := components
      covers := ?_
      pairwise_disjoint := ?_
      exhaustive := ?_
      no_equivalent_duplicates := ?_ }
  · intro x
    let C : Index :=
      ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
    refine ⟨source C, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨C, Finset.mem_univ C, rfl⟩
    · rw [hsource_range C]
      exact mem_irreducibleComponent
  · intro C D hC hD hneq
    rw [Set.disjoint_left]
    intro x hxC hxD
    rcases Finset.mem_image.mp hC with ⟨Ctop, _hCtop, hCeq⟩
    rcases Finset.mem_image.mp hD with ⟨Dtop, _hDtop, hDeq⟩
    subst C
    subst D
    have hsubset :
        Ctop.1 ⊆ Dtop.1 := by
      apply subset_of_irreducible_inter_clopen_nonempty Ctop.2.1
      · exact hOpen Dtop
      · exact hClosed Dtop
      · refine ⟨x, ?_, ?_⟩
        · rw [← hsource_range Ctop]
          exact hxC
        · rw [← hsource_range Dtop]
          exact hxD
    have hsets_eq : Ctop.1 = Dtop.1 :=
      Set.Subset.antisymm hsubset (Ctop.2.2 Dtop.2.1 hsubset)
    have htops_eq : Ctop = Dtop := by
      exact Subtype.ext hsets_eq
    exact hneq (by rw [htops_eq])
  · intro component
    let C : Index :=
      ⟨Set.range component.toAmbient.base, component.range_mem_irreducibleComponents⟩
    refine ⟨⟨source C, ?_⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨C, Finset.mem_univ C, rfl⟩
    · exact SourceIrreducibleComponent.isoOverAmbient_of_range_eq component (source C)
        (by
          rw [hsource_range C])
  · intro C D hC hD hiso
    rcases Finset.mem_image.mp hC with ⟨Ctop, _hCtop, hCeq⟩
    rcases Finset.mem_image.mp hD with ⟨Dtop, _hDtop, hDeq⟩
    subst C
    subst D
    have hsubset :
        Ctop.1 ⊆ Dtop.1 := by
      intro x hx
      rw [← hsource_range Ctop] at hx
      rcases hx with ⟨z, rfl⟩
      rw [← hsource_range Dtop]
      exact ⟨hiso.iso.hom.base z,
        by
          change ((hiso.iso.hom ≫ (source Dtop).toAmbient).base z) =
            (source Ctop).toAmbient.base z
          exact congrArg (fun f => f.base z) hiso.hom_toAmbient⟩
    have hsets_eq : Ctop.1 = Dtop.1 :=
      Set.Subset.antisymm hsubset (Ctop.2.2 Dtop.2.1 hsubset)
    have htops_eq : Ctop = Dtop := by
      exact Subtype.ext hsets_eq
    rw [htops_eq]

end FiniteIrreducibleComponentDecomposition

lemma stableDX_component_eq
    {X : Geometry.SmSchemeOver k}
    {DX : FiniteIrreducibleComponentDecomposition X}
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1)
    (listedX : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) :
    (stableDX listedX).component = listedX.1 := by
  exact hstableDX listedX

lemma stableDX_component_range_eq
    {X : Geometry.SmSchemeOver k}
    {DX : FiniteIrreducibleComponentDecomposition X}
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1)
    (listedX : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) :
    Set.range (stableDX listedX).component.toAmbient.base =
      Set.range listedX.1.toAmbient.base := by
  rw [stableDX_component_eq stableDX hstableDX listedX]

lemma isoOverAmbient_hom_toAmbient_base_apply
    {X : Geometry.SmSchemeOver k}
    {P Q : SourceIrreducibleComponent X}
    (hiso : SourceIrreducibleComponent.IsoOverAmbient P Q)
    (z : P.carrier.scheme.carrier) :
    Q.toAmbient.base (hiso.iso.hom.base z) = P.toAmbient.base z := by
  change ((hiso.iso.hom ≫ Q.toAmbient).base z) = P.toAmbient.base z
  exact congrArg (fun f => f.base z) hiso.hom_toAmbient

/- Exhaustivity of listed product source components: any source irreducible
component of the product ambient is isomorphic over the ambient product to one
of the listed products of the chosen factor decompositions. -/
noncomputable def productSourceIrreducibleComponent_exhaustive
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1)
    (component : SourceIrreducibleComponent (overBaseProductObject X Y)) :
    Σ listedX : { listed : SourceIrreducibleComponent X // listed ∈ DX.components },
      Σ listedY : { listed : SourceIrreducibleComponent Y // listed ∈ DY.components },
        SourceIrreducibleComponent.IsoOverAmbient component
          (productSourceIrreducibleComponent (stableDX listedX) listedY.1) := by
  classical
  have h :
      Nonempty (Σ listedX : { listed : SourceIrreducibleComponent X // listed ∈ DX.components },
        Σ listedY : { listed : SourceIrreducibleComponent Y // listed ∈ DY.components },
          SourceIrreducibleComponent.IsoOverAmbient component
            (productSourceIrreducibleComponent (stableDX listedX) listedY.1)) := by
    rcases component.range_mem_irreducibleComponents.1.nonempty with ⟨x, hxComponent⟩
    rcases DX.covers ((overBaseProduct.fst X Y).base x) with ⟨CX, hCXmem, hxCX⟩
    rcases DY.covers ((overBaseProduct.snd X Y).base x) with ⟨DY', hDYmem, hxDY⟩
    let listedX : { listed : SourceIrreducibleComponent X // listed ∈ DX.components } := ⟨CX, hCXmem⟩
    let listedY : { listed : SourceIrreducibleComponent Y // listed ∈ DY.components } := ⟨DY', hDYmem⟩
    let productListed :
        SourceIrreducibleComponent (overBaseProductObject X Y) :=
      productSourceIrreducibleComponent (stableDX listedX) listedY.1
    have hxProduct :
        x ∈ Set.range productListed.toAmbient.base := by
      have hx :
          (overBaseProduct.fst X Y).base x ∈ Set.range (stableDX listedX).component.toAmbient.base ∧
            (overBaseProduct.snd X Y).base x ∈ Set.range listedY.1.toAmbient.base := by
        constructor
        · have hxCX' :
              (overBaseProduct.fst X Y).base x ∈ Set.range listedX.1.toAmbient.base := hxCX
          rw [← stableDX_component_range_eq stableDX hstableDX listedX]
          exact hxCX'
        · exact hxDY
      change x ∈ Set.range
        (productSourceIrreducibleComponent (stableDX listedX) listedY.1).toAmbient.base
      exact (productSourceIrreducibleComponent_mem_range_iff
        (C := stableDX listedX) (D := listedY.1) (x := x)).2 hx
    have hsubset :
        Set.range component.toAmbient.base ⊆ Set.range productListed.toAmbient.base := by
      apply subset_of_irreducible_inter_clopen_nonempty
        component.range_mem_irreducibleComponents.1
      · exact productListed.isOpenImmersion.isOpen_range
      · exact
          (AlgebraicGeometry.IsClosedImmersion.iff_isPreimmersion.mp
            productListed.isClosedImmersion).2
      · exact ⟨x, hxComponent, hxProduct⟩
    exact ⟨⟨listedX, listedY,
      SourceIrreducibleComponent.isoOverAmbient_of_subset_range component productListed hsubset⟩⟩
  rcases Classical.choice h with ⟨listedX, listedY, hIso⟩
  exact ⟨listedX, listedY, hIso⟩

/-- Any ambient product component is contained in the clopen product of some
listed component of `X` with some listed component of `Y`. This is the basic
owner theorem behind sigma-index surjectivity for product decompositions. -/
theorem ambient_product_component_subset_product_of_listed
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (component : SourceIrreducibleComponent (overBaseProductObject X Y)) :
    ∃ listedX : { listed : SourceIrreducibleComponent X // listed ∈ DX.components },
      ∃ listedY : { listed : SourceIrreducibleComponent Y // listed ∈ DY.components },
        Set.range component.toAmbient.base ⊆
          (overBaseProduct.fst X Y).base ⁻¹' Set.range listedX.1.toAmbient.base ∩
            (overBaseProduct.snd X Y).base ⁻¹' Set.range listedY.1.toAmbient.base := by
  rcases component.range_mem_irreducibleComponents.1.nonempty with ⟨x, hxComponent⟩
  rcases DX.covers ((overBaseProduct.fst X Y).base x) with ⟨CX, hCXmem, hxCX⟩
  rcases DY.covers ((overBaseProduct.snd X Y).base x) with ⟨CY, hCYmem, hxCY⟩
  let listedX : { listed : SourceIrreducibleComponent X // listed ∈ DX.components } :=
    ⟨CX, hCXmem⟩
  let listedY : { listed : SourceIrreducibleComponent Y // listed ∈ DY.components } :=
    ⟨CY, hCYmem⟩
  have hOpenX : IsOpen (Set.range listedX.1.toAmbient.base) := by
    exact listedX.1.isOpenImmersion.isOpen_range
  have hClosedX : IsClosed (Set.range listedX.1.toAmbient.base) := by
    exact listedX.1.isClosedImmersion.base_closed.isClosed_range
  have hOpenY : IsOpen (Set.range listedY.1.toAmbient.base) := by
    exact listedY.1.isOpenImmersion.isOpen_range
  have hClosedY : IsClosed (Set.range listedY.1.toAmbient.base) := by
    exact listedY.1.isClosedImmersion.base_closed.isClosed_range
  have hOpenProduct :
      IsOpen
        ((overBaseProduct.fst X Y).base ⁻¹' Set.range listedX.1.toAmbient.base ∩
          (overBaseProduct.snd X Y).base ⁻¹' Set.range listedY.1.toAmbient.base) := by
    exact (hOpenX.preimage (overBaseProduct.fst X Y).base.continuous).inter
      (hOpenY.preimage (overBaseProduct.snd X Y).base.continuous)
  have hClosedProduct :
      IsClosed
        ((overBaseProduct.fst X Y).base ⁻¹' Set.range listedX.1.toAmbient.base ∩
          (overBaseProduct.snd X Y).base ⁻¹' Set.range listedY.1.toAmbient.base) := by
    exact (hClosedX.preimage (overBaseProduct.fst X Y).base.continuous).inter
      (hClosedY.preimage (overBaseProduct.snd X Y).base.continuous)
  have hxProduct :
      x ∈
        (overBaseProduct.fst X Y).base ⁻¹' Set.range listedX.1.toAmbient.base ∩
          (overBaseProduct.snd X Y).base ⁻¹' Set.range listedY.1.toAmbient.base := by
    exact ⟨hxCX, hxCY⟩
  refine ⟨listedX, listedY, ?_⟩
  exact subset_of_irreducible_inter_clopen_nonempty
    component.range_mem_irreducibleComponents.1
    hOpenProduct hClosedProduct
    ⟨x, hxComponent, hxProduct⟩

/-- Projecting an ambient product component contained in a listed clopen
product shows that its first projection lands inside the chosen listed
component of `X`. -/
theorem ambient_product_component_fst_subset_of_subset_product
    {X Y : Geometry.SmSchemeOver k}
    (component : SourceIrreducibleComponent (overBaseProductObject X Y))
    {listedX : SourceIrreducibleComponent X}
    {listedY : SourceIrreducibleComponent Y}
    (hsubset :
      Set.range component.toAmbient.base ⊆
        (overBaseProduct.fst X Y).base ⁻¹' Set.range listedX.toAmbient.base ∩
          (overBaseProduct.snd X Y).base ⁻¹' Set.range listedY.toAmbient.base) :
    Set.image (overBaseProduct.fst X Y).base (Set.range component.toAmbient.base) ⊆
      Set.range listedX.toAmbient.base := by
  intro x hx
  rcases hx with ⟨z, hz, rfl⟩
  exact (hsubset hz).1

/-- Projecting an ambient product component contained in a listed clopen
product shows that its second projection lands inside the chosen listed
component of `Y`. -/
theorem ambient_product_component_snd_subset_of_subset_product
    {X Y : Geometry.SmSchemeOver k}
    (component : SourceIrreducibleComponent (overBaseProductObject X Y))
    {listedX : SourceIrreducibleComponent X}
    {listedY : SourceIrreducibleComponent Y}
    (hsubset :
      Set.range component.toAmbient.base ⊆
        (overBaseProduct.fst X Y).base ⁻¹' Set.range listedX.toAmbient.base ∩
          (overBaseProduct.snd X Y).base ⁻¹' Set.range listedY.toAmbient.base) :
    Set.image (overBaseProduct.snd X Y).base (Set.range component.toAmbient.base) ⊆
      Set.range listedY.toAmbient.base := by
  intro y hy
  rcases hy with ⟨z, hz, rfl⟩
  exact (hsubset hz).2

theorem product_range_eq_left_of_product_range_eq
    {X Y : Geometry.SmSchemeOver k}
    {DX : FiniteIrreducibleComponentDecomposition X}
    {DY : FiniteIrreducibleComponentDecomposition Y}
    {listedX₁ listedX₂ : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }}
    {listedY₁ listedY₂ : { listed : SourceIrreducibleComponent Y // listed ∈ DY.components }}
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1)
    (hRange :
      Set.range (productSourceIrreducibleComponent (stableDX listedX₁) listedY₁.1).toAmbient.base =
      Set.range (productSourceIrreducibleComponent (stableDX listedX₂) listedY₂.1).toAmbient.base) :
    Set.range listedX₁.1.toAmbient.base = Set.range listedX₂.1.toAmbient.base := by
  calc
    Set.range listedX₁.1.toAmbient.base
      = Set.image (overBaseProduct.fst X Y).base
          (Set.range (productSourceIrreducibleComponent (stableDX listedX₁) listedY₁.1).toAmbient.base) := by
          rw [← stableDX_component_range_eq stableDX hstableDX listedX₁]
          exact (productSourceIrreducibleComponent_range_image_fst
            (C := stableDX listedX₁) (D := listedY₁.1)).symm
    _ = Set.image (overBaseProduct.fst X Y).base
          (Set.range (productSourceIrreducibleComponent (stableDX listedX₂) listedY₂.1).toAmbient.base) := by
          rw [hRange]
    _ = Set.range listedX₂.1.toAmbient.base := by
          rw [← stableDX_component_range_eq stableDX hstableDX listedX₂]
          exact productSourceIrreducibleComponent_range_image_fst
            (C := stableDX listedX₂) (D := listedY₂.1)

theorem product_range_eq_right_of_product_range_eq
    {X Y : Geometry.SmSchemeOver k}
    {DX : FiniteIrreducibleComponentDecomposition X}
    {DY : FiniteIrreducibleComponentDecomposition Y}
    {listedX₁ listedX₂ : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }}
    {listedY₁ listedY₂ : { listed : SourceIrreducibleComponent Y // listed ∈ DY.components }}
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hRange :
      Set.range (productSourceIrreducibleComponent (stableDX listedX₁) listedY₁.1).toAmbient.base =
      Set.range (productSourceIrreducibleComponent (stableDX listedX₂) listedY₂.1).toAmbient.base) :
    Set.range listedY₁.1.toAmbient.base = Set.range listedY₂.1.toAmbient.base := by
  calc
    Set.range listedY₁.1.toAmbient.base
      = Set.image (overBaseProduct.snd X Y).base
          (Set.range (productSourceIrreducibleComponent (stableDX listedX₁) listedY₁.1).toAmbient.base) := by
          symm
          exact productSourceIrreducibleComponent_range_image_snd
            (C := stableDX listedX₁) (D := listedY₁.1)
    _ = Set.image (overBaseProduct.snd X Y).base
          (Set.range (productSourceIrreducibleComponent (stableDX listedX₂) listedY₂.1).toAmbient.base) := by
          rw [hRange]
    _ = Set.range listedY₂.1.toAmbient.base := by
          exact productSourceIrreducibleComponent_range_image_snd
            (C := stableDX listedX₂) (D := listedY₂.1)

/-- Uniqueness of listed product source components: if two listed products are
isomorphic over the ambient product, then the listed factors agree. -/
theorem productSourceIrreducibleComponent_unique
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1)
    {listedX₁ listedX₂ : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }}
    {listedY₁ listedY₂ : { listed : SourceIrreducibleComponent Y // listed ∈ DY.components }}
    (hiso :
      SourceIrreducibleComponent.IsoOverAmbient
        (productSourceIrreducibleComponent (stableDX listedX₁) listedY₁.1)
        (productSourceIrreducibleComponent (stableDX listedX₂) listedY₂.1)) :
    listedX₁ = listedX₂ ∧ listedY₁ = listedY₂ := by
  let P₁ := productSourceIrreducibleComponent (stableDX listedX₁) listedY₁.1
  let P₂ := productSourceIrreducibleComponent (stableDX listedX₂) listedY₂.1
  have hsubset :
      Set.range P₁.toAmbient.base ⊆ Set.range P₂.toAmbient.base := by
    rintro x ⟨z, rfl⟩
    refine ⟨hiso.iso.hom.base z, ?_⟩
    change P₂.toAmbient.base (hiso.iso.hom.base z) = P₁.toAmbient.base z
    exact isoOverAmbient_hom_toAmbient_base_apply hiso z
  have hRange :
      Set.range P₁.toAmbient.base = Set.range P₂.toAmbient.base :=
    SourceIrreducibleComponent.range_eq_of_subset_range P₁ P₂ hsubset
  have hLeft :
      Set.range listedX₁.1.toAmbient.base = Set.range listedX₂.1.toAmbient.base :=
    product_range_eq_left_of_product_range_eq (DX := DX) (DY := DY) stableDX hstableDX hRange
  have hRight :
      Set.range listedY₁.1.toAmbient.base = Set.range listedY₂.1.toAmbient.base :=
    product_range_eq_right_of_product_range_eq (DX := DX) (DY := DY) stableDX hRange
  have hXeq := DX.no_equivalent_duplicates listedX₁.2 listedX₂.2
    (SourceIrreducibleComponent.isoOverAmbient_of_range_eq listedX₁.1 listedX₂.1 hLeft)
  have hYeq := DY.no_equivalent_duplicates listedY₁.2 listedY₂.2
    (SourceIrreducibleComponent.isoOverAmbient_of_range_eq listedY₁.1 listedY₂.1 hRight)
  exact ⟨Subtype.ext hXeq, Subtype.ext hYeq⟩

noncomputable def productSourceIrreducibleComponent_exhaustive_packaged
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1)
    (components :
      Finset (SourceIrreducibleComponent (overBaseProductObject X Y)))
    (hcomponents :
      components = @Finset.image _ _ (Classical.decEq _)
        (fun (p :
            { listed : SourceIrreducibleComponent X // listed ∈ DX.components } ×
              { listed : SourceIrreducibleComponent Y // listed ∈ DY.components }) =>
        productSourceIrreducibleComponent (stableDX p.1) p.2.1)
        (DX.components.attach.product DY.components.attach))
    (component : SourceIrreducibleComponent (overBaseProductObject X Y)) :
    Σ listed : { listed : SourceIrreducibleComponent (overBaseProductObject X Y) // listed ∈ components },
      SourceIrreducibleComponent.IsoOverAmbient component listed.1 := by
  classical
  letI : DecidableEq (SourceIrreducibleComponent (overBaseProductObject X Y)) := Classical.decEq _
  rcases productSourceIrreducibleComponent_exhaustive DX DY stableDX hstableDX component with
    ⟨listedX, listedY, hIso⟩
  refine ⟨⟨productSourceIrreducibleComponent (stableDX listedX) listedY.1, ?_⟩, ?_⟩
  · rw [hcomponents]
    refine Finset.mem_image.mpr ?_
    refine ⟨(listedX, listedY), ?_, rfl⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_attach _ _, Finset.mem_attach _ _⟩
  · exact hIso

/-- The finite irreducible-component decomposition of `X ×_k Y` obtained by
forming the listed products of a finite decomposition of `X` with a finite
decomposition of `Y`, under the explicit product-stability data carried by the
listed left components. -/
noncomputable def finiteProductSourceIrreducibleComponentDecomposition
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1) :
    FiniteIrreducibleComponentDecomposition (overBaseProductObject X Y) := by
  classical
  letI : DecidableEq (SourceIrreducibleComponent (overBaseProductObject X Y)) := Classical.decEq _
  let listedPairs :=
    DX.components.attach.product DY.components.attach
  let components :
      Finset (SourceIrreducibleComponent (overBaseProductObject X Y)) :=
    @Finset.image _ _ (Classical.decEq _) (fun (p :
        { listed : SourceIrreducibleComponent X // listed ∈ DX.components } ×
          { listed : SourceIrreducibleComponent Y // listed ∈ DY.components }) =>
      productSourceIrreducibleComponent (stableDX p.1) p.2.1) listedPairs
  refine
    { components := components
      covers := ?_
      pairwise_disjoint := ?_
      exhaustive := ?_
      no_equivalent_duplicates := ?_ }
  · intro x
    rcases DX.covers ((overBaseProduct.fst X Y).base x) with ⟨CX, hCXmem, hxCX⟩
    rcases DY.covers ((overBaseProduct.snd X Y).base x) with ⟨CY, hCYmem, hxCY⟩
    let listedX : { listed : SourceIrreducibleComponent X // listed ∈ DX.components } :=
      ⟨CX, hCXmem⟩
    let listedY : { listed : SourceIrreducibleComponent Y // listed ∈ DY.components } :=
      ⟨CY, hCYmem⟩
    refine ⟨productSourceIrreducibleComponent (stableDX listedX) listedY.1, ?_, ?_⟩
    · refine Finset.mem_image.mpr ?_
      refine ⟨(listedX, listedY), ?_, rfl⟩
      change (listedX, listedY) ∈ listedPairs
      exact Finset.mem_product.mpr ⟨Finset.mem_attach _ _, Finset.mem_attach _ _⟩
    · have hxCX' :
          (overBaseProduct.fst X Y).base x ∈ Set.range (stableDX listedX).component.toAmbient.base := by
          have hxCX'' :
              (overBaseProduct.fst X Y).base x ∈ Set.range listedX.1.toAmbient.base := hxCX
          rw [← stableDX_component_range_eq stableDX hstableDX listedX]
          exact hxCX''
      change x ∈ Set.range
        (productSourceIrreducibleComponent (stableDX listedX) listedY.1).toAmbient.base
      exact (productSourceIrreducibleComponent_mem_range_iff
        (C := stableDX listedX) (D := listedY.1) (x := x)).2
        ⟨hxCX', hxCY⟩
  · intro C D hC hD hneq
    rcases Finset.mem_image.mp hC with ⟨p, hpMem, rfl⟩
    rcases Finset.mem_image.mp hD with ⟨q, hqMem, hqEq⟩
    subst D
    by_cases hpqX : p.1 = q.1
    · have hpqY : p.2 ≠ q.2 := by
        intro hpqY
        apply hneq
        rw [hpqX, hpqY]
      rw [Set.disjoint_left]
      intro x hxP hxQ
      have hprojP :=
        productSourceIrreducibleComponent_proj_mem_of_mem_range
          (C := stableDX p.1) (D := p.2.1) hxP
      have hprojQ :=
        productSourceIrreducibleComponent_proj_mem_of_mem_range
          (C := stableDX q.1) (D := q.2.1) hxQ
      have hdisj :=
        DY.disjoint_of_mem_ne p.2.2 q.2.2 (by
          intro hEq
          exact hpqY (Subtype.ext hEq))
      exact hdisj.le_bot ⟨hprojP.2, hprojQ.2⟩
    · rw [Set.disjoint_left]
      intro x hxP hxQ
      have hprojP :=
        productSourceIrreducibleComponent_proj_mem_of_mem_range
          (C := stableDX p.1) (D := p.2.1) hxP
      have hprojQ :=
        productSourceIrreducibleComponent_proj_mem_of_mem_range
          (C := stableDX q.1) (D := q.2.1) hxQ
      have hdisj :=
        DX.disjoint_of_mem_ne p.1.2 q.1.2 (by
          intro hEq
          exact hpqX (Subtype.ext hEq))
      exact hdisj.le_bot
        ⟨by
            rw [← stableDX_component_range_eq stableDX hstableDX p.1]
            exact hprojP.1,
          by
            rw [← stableDX_component_range_eq stableDX hstableDX q.1]
            exact hprojQ.1⟩
  · intro component
    exact productSourceIrreducibleComponent_exhaustive_packaged
      DX DY stableDX hstableDX components rfl component
  · intro C D hC hD hiso
    rcases Finset.mem_image.mp hC with ⟨p, hpMem, hpEq⟩
    rcases Finset.mem_image.mp hD with ⟨q, hqMem, hqEq⟩
    subst C
    have hiso' :
        SourceIrreducibleComponent.IsoOverAmbient
          (productSourceIrreducibleComponent (stableDX p.1) p.2.1)
          (productSourceIrreducibleComponent (stableDX q.1) q.2.1) := by
      rw [hqEq]
      exact hiso
    rcases productSourceIrreducibleComponent_unique DX DY stableDX hstableDX hiso' with
      ⟨hpqX, hpqY⟩
    have hpq : p = q := Prod.ext hpqX hpqY
    subst q
    exact hqEq

/-- Smooth schemes of finite type over a field have finitely many topological
irreducible components. This supplies the finite-index part of a canonical
`FiniteIrreducibleComponentDecomposition`; the geometric packaging of each
component as a clopen integral smooth subscheme is the separate constructor
needed for that decomposition. -/
theorem finite_irreducibleComponents (X : Geometry.SmSchemeOver k) :
    (irreducibleComponents X.scheme).Finite :=
  AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian

/-- The finite source-component decomposition obtained by listing the actual
topological irreducible components of a smooth finite-type scheme, once those
components have been realized as open, closed, integral source subschemes. -/
noncomputable def finiteSourceIrreducibleComponentDecompositionOfTopologicalComponents
    (X : Geometry.SmSchemeOver k)
    (hOpen :
      ∀ C : { C : Set X.scheme // C ∈ irreducibleComponents X.scheme },
        IsOpen C.1)
    (hClosed :
      ∀ C : { C : Set X.scheme // C ∈ irreducibleComponents X.scheme },
        IsClosed C.1)
    (hIntegral :
      ∀ C : { C : Set X.scheme // C ∈ irreducibleComponents X.scheme },
        IsIntegral (Scheme.Opens.toScheme (⟨C.1, hOpen C⟩ : X.scheme.Opens))) :
    FiniteIrreducibleComponentDecomposition X :=
  FiniteIrreducibleComponentDecomposition.ofTopologicalComponents
    X (finite_irreducibleComponents X) hOpen hClosed hIntegral

/-- The finite source-component decomposition obtained from the actual
irreducible components once those components are known to be clopen.  The
remaining hypothesis is the genuine scheme-theoretic integrality of the
corresponding open component schemes. -/
noncomputable def finiteSourceIrreducibleComponentDecompositionOfClopenComponents
    (X : Geometry.SmSchemeOver k)
    (hClopen :
      ∀ C : { C : Set X.scheme // C ∈ irreducibleComponents X.scheme },
        IsClopen C.1)
    (hIntegral :
      ∀ C : { C : Set X.scheme // C ∈ irreducibleComponents X.scheme },
        IsIntegral
          (Scheme.Opens.toScheme (⟨C.1, (hClopen C).right⟩ : X.scheme.Opens))) :
    FiniteIrreducibleComponentDecomposition X :=
  finiteSourceIrreducibleComponentDecompositionOfTopologicalComponents X
    (fun C => (hClopen C).right)
    (fun C => (hClopen C).left)
    hIntegral

/-- The canonical decomposition built from clopen topological irreducible
components has exactly those topological components as its listed components,
up to the owner decomposition API. -/
noncomputable def finiteSourceIrreducibleComponentDecompositionOfClopenComponents_listedEquiv
    (X : Geometry.SmSchemeOver k)
    (hClopen :
      ∀ C : { C : Set X.scheme // C ∈ irreducibleComponents X.scheme },
        IsClopen C.1)
    (hIntegral :
      ∀ C : { C : Set X.scheme // C ∈ irreducibleComponents X.scheme },
        IsIntegral
          (Scheme.Opens.toScheme (⟨C.1, (hClopen C).right⟩ : X.scheme.Opens))) :
    { C : Set X.scheme // C ∈ irreducibleComponents X.scheme } ≃
      { listed : SourceIrreducibleComponent X //
          listed ∈ (finiteSourceIrreducibleComponentDecompositionOfClopenComponents
            X hClopen hIntegral).components } := by
  classical
  let D := finiteSourceIrreducibleComponentDecompositionOfClopenComponents X hClopen hIntegral
  let source :
      { C : Set X.scheme // C ∈ irreducibleComponents X.scheme } →
        SourceIrreducibleComponent X :=
    fun C =>
      SourceIrreducibleComponent.ofTopologicalComponent
        X C (hClopen C).right (hClopen C).left (hIntegral C)
  refine Equiv.ofBijective
    (fun C => D.listedRepresentative (source C)) ?_
  constructor
  · intro C1 C2 hEq
    have hVal : (D.listedRepresentative (source C1)).1 = (D.listedRepresentative (source C2)).1 :=
      congrArg Subtype.val hEq
    have hiso :
        SourceIrreducibleComponent.IsoOverAmbient (source C1) (source C2) := by
      subst hVal
      exact (D.listedRepresentativeIso (source C1)).trans
        (D.listedRepresentativeIso (source C2)).symm
    have hRange :
        Set.range (source C1).toAmbient.base = Set.range (source C2).toAmbient.base :=
      SourceIrreducibleComponent.IsoOverAmbient.range_eq hiso
    have hSet :
        C1.1 = C2.1 := by
      calc
        C1.1 = Set.range (source C1).toAmbient.base := by
          symm
          exact SourceIrreducibleComponent.range_ofTopologicalComponent
            X C1 (hClopen C1).right (hClopen C1).left (hIntegral C1)
        _ = Set.range (source C2).toAmbient.base := hRange
        _ = C2.1 := by
          exact SourceIrreducibleComponent.range_ofTopologicalComponent
            X C2 (hClopen C2).right (hClopen C2).left (hIntegral C2)
    exact Subtype.ext hSet
  · intro listed
    let C : { C : Set X.scheme // C ∈ irreducibleComponents X.scheme } :=
      ⟨Set.range listed.1.toAmbient.base, listed.1.range_mem_irreducibleComponents⟩
    refine ⟨C, ?_⟩
    apply Subtype.ext
    exact D.listedRepresentative_eq_of_iso listed.2
      (SourceIrreducibleComponent.isoOverAmbient_of_range_eq
        (source C) listed.1 (by
          calc
            Set.range (source C).toAmbient.base = C.1 := by
              exact SourceIrreducibleComponent.range_ofTopologicalComponent
                X C (hClopen C).right (hClopen C).left (hIntegral C)
            _ = Set.range listed.1.toAmbient.base := rfl))

/-- Bottom-up component owner theorem: once a smooth finite-type scheme is
known to be locally irreducible and each irreducible component open subscheme
is integral, the actual irreducible components assemble canonically into a
finite source-component decomposition. This is the natural entry point for
product-model component geometry. -/
noncomputable def finiteSourceIrreducibleComponentDecompositionOfLocallyIrreducible
    (X : Geometry.SmSchemeOver k)
    (hLoc : Geometry.Topology.LocallyIrreducibleSpace X.scheme)
    (hIntegral :
      ∀ C : { C : Set X.scheme // C ∈ irreducibleComponents X.scheme },
        IsIntegral
          (Scheme.Opens.toScheme
            (⟨C.1,
              Geometry.Topology.isOpen_irreducibleComponent_of_locallyIrreducible
                C.2 hLoc⟩ :
              X.scheme.Opens))) :
    FiniteIrreducibleComponentDecomposition X :=
  finiteSourceIrreducibleComponentDecompositionOfClopenComponents X
    (fun C =>
      Geometry.Topology.isClopen_irreducibleComponent_of_noetherian_locallyIrreducible
        C.2 hLoc)
    (by
      intro C
      exact hIntegral C)

/-- If every irreducible component of a topological space is open, then the
space is locally irreducible. This is the converse direction used to pass from
component-openness results back to local irreducibility. -/
theorem locallyIrreducibleSpace_of_irreducibleComponents_open
    {X : Type u} [TopologicalSpace X]
    (hOpen :
      ∀ C : { C : Set X // C ∈ irreducibleComponents X },
        IsOpen C.1) :
    Geometry.Topology.LocallyIrreducibleSpace X := by
  intro x
  refine ⟨irreducibleComponent x, ?_, mem_irreducibleComponent, ?_⟩
  · exact hOpen ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  · exact isIrreducible_irreducibleComponent

/-- For a smooth scheme over a field, every point admits an affine neighborhood
whose coordinate ring is standard smooth over the base field itself. Since the
base is `Spec k`, the affine open on the target can be rigidified to `⊤`. -/
theorem exists_affineNeighborhood_isStandardSmooth
    (X : Geometry.SmSchemeOver k) (x : X.scheme) :
    ∃ V : X.scheme.affineOpens, x ∈ V.1 ∧
      RingHom.IsStandardSmooth.{0, 0}
        (X.structMap.appLE ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩ V le_top) := by
  obtain ⟨U, V, hx, e, hSmooth⟩ := X.smooth.exists_isStandardSmooth x
  have hxU : X.structMap.base x ∈ U.1 := e hx
  have hU : U = ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩ := by
    ext y
    constructor
    · intro _
      trivial
    · intro _
      exact hxU
  refine ⟨V, hx, ?_⟩
  have hSmooth' :
      RingHom.IsStandardSmooth.{0, 0}
        (X.structMap.appLE ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩ V
          (hU ▸ rfl ▸ e)) :=
    ((X.structMap).appLE_congr e hU rfl
      (fun {R S} [CommRing R] [CommRing S] f =>
        RingHom.IsStandardSmooth.{0, 0} f)).mp hSmooth
  exact hSmooth'

/-- Specialized chart extraction for the actual product object `X ×_k Y`. -/
theorem overBaseProductObject_exists_affineNeighborhood_isStandardSmooth
    (X Y : Geometry.SmSchemeOver k)
    (x : (overBaseProductObject X Y).scheme) :
    ∃ V : (overBaseProductObject X Y).scheme.affineOpens, x ∈ V.1 ∧
      RingHom.IsStandardSmooth.{0, 0}
        ((overBaseProductObject X Y).structMap.appLE
          ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩ V le_top) :=
  exists_affineNeighborhood_isStandardSmooth (X := overBaseProductObject X Y) x

/-- A smooth `k`-scheme has affine smooth chart rings once standard-smooth chart
rings are known to be smooth over `k`. This is the direct owner theorem that
transports the existing standard-smooth affine cover into the smooth route. -/
theorem exists_affineNeighborhood_smooth_of_standardSmoothToSmooth
    (X : Geometry.SmSchemeOver k)
    (hStandardSmooth :
      ∀ {A : Type u} [CommRing A] [Algebra k A],
        RingHom.IsStandardSmooth.{0, 0} (algebraMap k A) → Algebra.Smooth k A)
    (x : X.scheme) :
    ∃ U : X.scheme.affineOpens,
      x ∈ U.1 ∧
      Algebra.Smooth k (Γ(X.scheme, U)) := by
  rcases exists_affineNeighborhood_isStandardSmooth (X := X) x with ⟨U, hxU, hU⟩
  exact ⟨U, hxU, hStandardSmooth hU⟩

/-- The product object `X ×_k Y` has affine smooth chart rings once
standard-smooth chart rings are known to be smooth over `k`. -/
theorem overBaseProductObject_exists_affineNeighborhood_smooth_of_standardSmoothToSmooth
    (X Y : Geometry.SmSchemeOver k)
    (hStandardSmooth :
      ∀ {A : Type u} [CommRing A] [Algebra k A],
        RingHom.IsStandardSmooth.{0, 0} (algebraMap k A) → Algebra.Smooth k A)
    (x : (overBaseProductObject X Y).scheme) :
    ∃ U : (overBaseProductObject X Y).scheme.affineOpens,
      x ∈ U.1 ∧
      Algebra.Smooth k (Γ((overBaseProductObject X Y).scheme, U)) :=
  exists_affineNeighborhood_smooth_of_standardSmoothToSmooth
    (X := overBaseProductObject X Y) hStandardSmooth x

/-- Every point of `X ×_k Y` admits an affine neighborhood whose coordinate
ring is essentially of finite type over `k`. This now follows canonically from
standard smoothness of the extracted chart. -/
theorem overBaseProductObject_exists_affineNeighborhood_essFiniteType
    (X Y : Geometry.SmSchemeOver k)
    (x : (overBaseProductObject X Y).scheme) :
    ∃ V : (overBaseProductObject X Y).scheme.affineOpens, x ∈ V.1 ∧
      Algebra.EssFiniteType k
        (Γ((overBaseProductObject X Y).scheme, V)) := by
  rcases overBaseProductObject_exists_affineNeighborhood_isStandardSmooth
      (X := X) (Y := Y) x with ⟨V, hxV, hV⟩
  refine ⟨V, hxV, ?_⟩
  letI : Algebra.IsStandardSmooth k (Γ((overBaseProductObject X Y).scheme, V)) := by
    rw [RingHom.IsStandardSmooth] at hV
    exact hV
  exact Boundary.standardSmooth_essFiniteType

/-- A scheme is reduced if every point admits an affine neighborhood whose
coordinate ring is reduced. This is the owner theorem that turns affine-local
reducedness statements into a global reducedness theorem on schemes. -/
theorem isReduced_of_exists_affineNeighborhood_reduced
    (X : Scheme.{u})
    (hReduced :
      ∀ x : X,
        ∃ U : X.affineOpens, x ∈ U.1 ∧ _root_.IsReduced Γ(X, U)) :
    IsReduced X := by
  apply AlgebraicGeometry.isReduced_of_isReduced_stalk
  intro x
  rcases hReduced x with ⟨U, hxU, hΓU⟩
  letI : _root_.IsReduced Γ(X, U) := hΓU
  letI : _root_.IsReduced Γ(U.1, ⊤) :=
    isReduced_of_injective (U.1.topIso.hom)
      U.1.topIso.commRingCatIsoToRingEquiv.injective
  letI : IsAffine U.1 := U.2.isAffine
  letI : IsReduced U.1 := AlgebraicGeometry.isReduced_of_isAffine_isReduced (X := U.1)
  letI : _root_.IsReduced (U.1.presheaf.stalk ⟨x, hxU⟩) :=
    AlgebraicGeometry.isReduced_stalk_of_isReduced (X := U.1) ⟨x, hxU⟩
  exact isReduced_of_injective (U.1.stalkIso ⟨x, hxU⟩).hom
    (U.1.stalkIso ⟨x, hxU⟩).commRingCatIsoToRingEquiv.injective

/-- A smooth `k`-scheme is reduced once standard-smooth affine chart rings over
`k` are known to be reduced. This isolates the remaining base geometry to the
pure ring-theoretic statement on standard-smooth algebras over a field. -/
theorem smSchemeOver_isReduced_of_standardSmoothAffineReduced
    (X : Geometry.SmSchemeOver k)
    (hStandardReduced :
      ∀ {A : Type u} [CommRing A] [Algebra k A],
        RingHom.IsStandardSmooth.{0, 0} (algebraMap k A) → _root_.IsReduced A) :
    IsReduced X.scheme := by
  apply isReduced_of_exists_affineNeighborhood_reduced
  intro x
  rcases exists_affineNeighborhood_isStandardSmooth (X := X) x with ⟨U, hxU, hU⟩
  refine ⟨U, hxU, ?_⟩
  exact hStandardReduced hU

/-- A smooth `k`-scheme is reduced once standard-smooth affine chart rings are
known to be smooth over `k`, provided smooth `k`-algebras are reduced. This
packages the smooth-route consumption of the standard-smooth affine cover. -/
theorem smSchemeOver_isReduced_of_standardSmoothAffineSmooth
    (X : Geometry.SmSchemeOver k)
    (hStandardSmooth :
      ∀ {A : Type u} [CommRing A] [Algebra k A],
        RingHom.IsStandardSmooth.{0, 0} (algebraMap k A) → Algebra.Smooth k A)
    (hSmoothReduced :
      ∀ {A : Type u} [CommRing A] [Algebra k A],
        Algebra.Smooth k A → _root_.IsReduced A) :
    IsReduced X.scheme := by
  refine smSchemeOver_isReduced_of_smoothAffine (X := X) ?_ hSmoothReduced
  intro x
  exact exists_affineNeighborhood_smooth_of_standardSmoothToSmooth
    (X := X) hStandardSmooth x

/-- A smooth `k`-scheme is reduced once standard-smooth affine chart rings over
`k` are known to be formally unramified. Finite presentation, hence essential
finite type, is automatic for standard-smooth algebras, so the field-level
reducedness theorem applies with no extra affine hypothesis. -/
theorem smSchemeOver_isReduced_of_standardSmoothAffineFormallyUnramified
    (X : Geometry.SmSchemeOver k)
    (hStandardUnramified :
      ∀ {A : Type u} [CommRing A] [Algebra k A],
        RingHom.IsStandardSmooth.{0, 0} (algebraMap k A) →
          Algebra.FormallyUnramified k A) :
    IsReduced X.scheme := by
  refine isReduced_of_exists_affineNeighborhood_formallyUnramified (k := k) (X := X.scheme) ?_
  intro x
  rcases exists_affineNeighborhood_isStandardSmooth (X := X) x with ⟨U, hxU, hU⟩
  refine ⟨U, hxU, ?_, ?_⟩
  · exact hStandardUnramified hU
  · letI : Algebra.IsStandardSmooth k (Γ(X.scheme, U)) := by
        rw [RingHom.IsStandardSmooth] at hU
        exact hU
    exact Boundary.standardSmooth_essFiniteType

/-- A smooth `k`-scheme is reduced once standard-smooth affine chart rings over
`k` are known to be formally étale. Essential finite type is automatic for
standard-smooth algebras, so the field-level reducedness theorem applies
without extra affine hypotheses. -/
theorem smSchemeOver_isReduced_of_standardSmoothAffineFormallyEtale
    (X : Geometry.SmSchemeOver k)
    (hStandardEtale :
      ∀ {A : Type u} [CommRing A] [Algebra k A],
        RingHom.IsStandardSmooth.{0, 0} (algebraMap k A) →
          Algebra.FormallyEtale k A) :
    IsReduced X.scheme := by
  refine isReduced_of_exists_affineNeighborhood_formallyEtale (k := k) (X := X.scheme) ?_
  intro x
  rcases exists_affineNeighborhood_isStandardSmooth (X := X) x with ⟨U, hxU, hU⟩
  refine ⟨U, hxU, ?_, ?_⟩
  · exact hStandardEtale hU
  · letI : Algebra.IsStandardSmooth k (Γ(X.scheme, U)) := by
        rw [RingHom.IsStandardSmooth] at hU
        exact hU
    exact Boundary.standardSmooth_essFiniteType

/-- A smooth `k`-scheme is reduced if each point admits a standard-smooth
relative-dimension-zero affine chart over `k`. This is the direct owner route
through the canonical theorem
`Boundary.Algebra.IsStandardSmoothOfRelativeDimension.formallyEtale`. -/
theorem smSchemeOver_isReduced_of_standardSmoothOfRelativeDimensionZeroAffine
    (X : Geometry.SmSchemeOver k)
    (h :
      ∀ x : X.scheme,
        ∃ U : X.scheme.affineOpens,
          x ∈ U.1 ∧
          Algebra.IsStandardSmoothOfRelativeDimension 0 k (Γ(X.scheme, U))) :
    IsReduced X.scheme := by
  refine isReduced_of_exists_affineNeighborhood_etale (k := k) (X := X.scheme) ?_
  intro x
  rcases h x with ⟨U, hxU, hU⟩
  refine ⟨U, hxU, ?_⟩
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0 k (Γ(X.scheme, U)) := hU
  exact Boundary.Algebra.IsStandardSmoothOfRelativeDimension.etale

/-- A smooth `k`-scheme has affine étale chart rings as soon as each point
admits a relative-dimension-zero standard-smooth affine chart. -/
theorem exists_affineNeighborhood_etale_of_standardSmoothOfRelativeDimensionZero
    (X : Geometry.SmSchemeOver k)
    (h :
      ∀ x : X.scheme,
        ∃ U : X.scheme.affineOpens,
          x ∈ U.1 ∧
          Algebra.IsStandardSmoothOfRelativeDimension 0 k (Γ(X.scheme, U)))
    (x : X.scheme) :
    ∃ U : X.scheme.affineOpens,
      x ∈ U.1 ∧
      Algebra.Etale k (Γ(X.scheme, U)) := by
  rcases h x with ⟨U, hxU, hU⟩
  refine ⟨U, hxU, ?_⟩
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0 k (Γ(X.scheme, U)) := hU
  exact Boundary.Algebra.IsStandardSmoothOfRelativeDimension.etale

/-- Every point of a smooth `k`-scheme admits an affine neighborhood whose
coordinate ring is standard smooth of relative dimension `0` over a finite
polynomial algebra over `k`. This is the direct geometric form of the owner
theorem
`Boundary.Algebra.IsStandardSmoothOfRelativeDimension.exists_polynomialBase_standardSmoothOfRelativeDimensionZero`
applied to the standard-smooth affine chart extracted from smoothness. -/
theorem exists_affineNeighborhood_standardSmoothOfRelativeDimensionZero_overPolynomial
    (X : Geometry.SmSchemeOver k)
    (x : X.scheme) :
    ∃ U : X.scheme.affineOpens,
      x ∈ U.1 ∧
      ∃ (τ : Type _) (_ : Finite τ) (φ : MvPolynomial τ k →+* Γ(X.scheme, U)),
        RingHom.IsStandardSmoothOfRelativeDimension 0 φ := by
  classical
  rcases exists_affineNeighborhood_isStandardSmooth (X := X) x with ⟨U, hxU, hU⟩
  letI : Algebra.IsStandardSmooth (k := k) (Γ(X.scheme, U)) := by
    rw [RingHom.IsStandardSmooth] at hU
    exact hU
  let P : Algebra.SubmersivePresentation k (Γ(X.scheme, U)) :=
    Classical.choice ‹Algebra.IsStandardSmooth k (Γ(X.scheme, U))›.out
  let n : ℕ := P.dimension
  letI : Algebra.IsStandardSmoothOfRelativeDimension n k (Γ(X.scheme, U)) := ⟨P, rfl⟩
  obtain ⟨τ, hτfin, _hτcard, φ, hφ⟩ :=
    Boundary.Algebra.IsStandardSmoothOfRelativeDimension.exists_polynomialBase_standardSmoothOfRelativeDimensionZero
      (R := k) (S := Γ(X.scheme, U)) (n := n)
  exact ⟨U, hxU, τ, hτfin, φ, hφ⟩

/-- Every point of a smooth `k`-scheme admits an affine neighborhood whose
coordinate ring is étale over a finite polynomial algebra over `k`. This is
the corollary of
`exists_affineNeighborhood_standardSmoothOfRelativeDimensionZero_overPolynomial`
obtained by applying the owner theorem
`Boundary.ringHom_standardSmoothOfRelativeDimensionZero_etale`. -/
theorem exists_affineNeighborhood_etale_overPolynomial
    (X : Geometry.SmSchemeOver k)
    (x : X.scheme) :
    ∃ U : X.scheme.affineOpens,
      x ∈ U.1 ∧
      ∃ (τ : Type _) (_ : Finite τ) (φ : MvPolynomial τ k →+* Γ(X.scheme, U)),
        Algebra.Etale φ.toAlgebra := by
  classical
  rcases exists_affineNeighborhood_standardSmoothOfRelativeDimensionZero_overPolynomial
      (X := X) x with ⟨U, hxU, τ, hτfin, φ, hφ⟩
  refine ⟨U, hxU, τ, hτfin, φ, ?_⟩
  exact Boundary.ringHom_standardSmoothOfRelativeDimensionZero_etale φ hφ

/-- An affine chart whose coordinate ring is standard smooth of relative
dimension `0` over a field has discrete underlying topological space. The
proof transports the discrete prime spectrum of the coordinate ring across the
canonical affine isomorphism `U ≅ Spec Γ(U)`. -/
theorem affineNeighborhood_discrete_of_standardSmoothOfRelativeDimensionZero
    {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))]
    (U : X.affineOpens)
    (hU : Algebra.IsStandardSmoothOfRelativeDimension 0 k (Γ(X, U))) :
    DiscreteTopology U := by
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0 k (Γ(X, U)) := hU
  letI : DiscreteTopology (PrimeSpectrum (Γ(X, U))) :=
    Boundary.standardSmoothOfRelativeDimensionZero_discretePrimeSpectrum (k := k)
  exact DiscreteTopology.of_continuous_injective
    (f := U.2.isoSpec.hom.base)
    U.2.isoSpec.hom.base.2
    (bijective_of_isIso U.2.isoSpec.hom.base).injective

/-- The affine scheme `Spec R` is locally irreducible when `R` is a domain. -/
theorem spec_locallyIrreducible_of_isDomain
    (R : CommRingCat.{u})
    [IsDomain R] :
    Geometry.Topology.LocallyIrreducibleSpace (Spec R) := by
  exact LocalIrreducibleProduct.locallyIrreducible_of_irreducibleSpace

/-- The prime spectrum of a multivariable polynomial ring over a field is
locally irreducible. -/
theorem spec_mvPolynomial_locallyIrreducible
    (τ : Type u) [Finite τ] :
    Geometry.Topology.LocallyIrreducibleSpace (Spec (CommRingCat.of (MvPolynomial τ k))) := by
  exact spec_locallyIrreducible_of_isDomain (CommRingCat.of (MvPolynomial τ k))

/-- A smooth `k`-scheme is locally irreducible if every point admits an affine
neighborhood whose coordinate ring is standard smooth of relative dimension
`0` over `k`. In fact, every such point has an open singleton neighborhood. -/
theorem smSchemeOver_locallyIrreducible_of_standardSmoothOfRelativeDimensionZeroAffine
    (X : Geometry.SmSchemeOver k)
    (h :
      ∀ x : X.scheme,
        ∃ U : X.scheme.affineOpens,
          x ∈ U.1 ∧
          Algebra.IsStandardSmoothOfRelativeDimension 0 k (Γ(X.scheme, U))) :
    Geometry.Topology.LocallyIrreducibleSpace X.scheme := by
  intro x
  rcases h x with ⟨U, hxU, hU⟩
  letI : DiscreteTopology U :=
    affineNeighborhood_discrete_of_standardSmoothOfRelativeDimensionZero
      (k := k) (X := X.scheme) U hU
  have hOpenSub : IsOpen ({⟨x, hxU⟩} : Set U) := isOpen_discrete _
  have hOpenX : IsOpen ({x} : Set X.scheme) := by
    convert U.1.2.isOpenEmbedding_subtypeVal.isOpenMap _ hOpenSub using 1
    ext y
    constructor
    · intro hy
      exact Subtype.ext hy
    · intro hy
      rw [hy]
      exact hxU
  refine ⟨{x}, hOpenX, ?_, isIrreducible_singleton x⟩
  exact Set.singleton_nonempty x

/-- A scheme over `Spec k` is reduced if every point admits an affine
neighborhood whose coordinate ring is formally étale over `k` and essentially
of finite type. This globalizes the field theorem
`Boundary.formallyEtale_isReduced_of_field`. -/
theorem isReduced_of_exists_affineNeighborhood_formallyEtale
    (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))]
    (h :
      ∀ x : X,
        ∃ U : X.affineOpens,
          x ∈ U.1 ∧
          Algebra.FormallyEtale k (Γ(X, U)) ∧
          Algebra.EssFiniteType k (Γ(X, U))) :
    IsReduced X := by
  refine isReduced_of_exists_affineNeighborhood_reduced (X := X) ?_
  intro x
  rcases h x with ⟨U, hxU, hEtale, hEss⟩
  refine ⟨U, hxU, ?_⟩
  letI : Algebra.FormallyEtale k (Γ(X, U)) := hEtale
  letI : Algebra.EssFiniteType k (Γ(X, U)) := hEss
  exact Boundary.formallyEtale_isReduced_of_field (k := k)

/-- A scheme over `Spec k` is reduced if every point admits an affine
neighborhood whose coordinate ring is formally unramified over `k` and
essentially of finite type. This globalizes the field theorem
`Boundary.formallyUnramified_isReduced_of_field`. -/
theorem isReduced_of_exists_affineNeighborhood_formallyUnramified
    (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))]
    (h :
      ∀ x : X,
        ∃ U : X.affineOpens,
          x ∈ U.1 ∧
          Algebra.FormallyUnramified k (Γ(X, U)) ∧
          Algebra.EssFiniteType k (Γ(X, U))) :
    IsReduced X := by
  refine isReduced_of_exists_affineNeighborhood_reduced (X := X) ?_
  intro x
  rcases h x with ⟨U, hxU, hUnram, hEss⟩
  refine ⟨U, hxU, ?_⟩
  letI : Algebra.FormallyUnramified k (Γ(X, U)) := hUnram
  letI : Algebra.EssFiniteType k (Γ(X, U)) := hEss
  exact Boundary.formallyUnramified_isReduced_of_field (k := k)

/-- A scheme over `Spec k` is reduced if every point admits an affine
neighborhood whose coordinate ring is étale over `k`. -/
theorem isReduced_of_exists_affineNeighborhood_etale
    (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))]
    (h :
      ∀ x : X,
        ∃ U : X.affineOpens,
          x ∈ U.1 ∧
          Algebra.Etale k (Γ(X, U))) :
    IsReduced X := by
  refine isReduced_of_exists_affineNeighborhood_reduced (X := X) ?_
  intro x
  rcases h x with ⟨U, hxU, hEtale⟩
  refine ⟨U, hxU, ?_⟩
  letI : Algebra.Etale k (Γ(X, U)) := hEtale
  exact Boundary.etale_isReduced_of_field (k := k)

/-- A smooth `k`-scheme is reduced if each point admits an affine neighborhood
whose coordinate ring is formally étale over `k` and essentially of finite
type. -/
theorem smSchemeOver_isReduced_of_formallyEtaleAffine
    (X : Geometry.SmSchemeOver k)
    (h :
      ∀ x : X.scheme,
        ∃ U : X.scheme.affineOpens,
          x ∈ U.1 ∧
          Algebra.FormallyEtale k (Γ(X.scheme, U)) ∧
          Algebra.EssFiniteType k (Γ(X.scheme, U))) :
    IsReduced X.scheme :=
  isReduced_of_exists_affineNeighborhood_formallyEtale (k := k) (X := X.scheme) h

/-- A smooth `k`-scheme is reduced if each point admits an affine neighborhood
whose coordinate ring is formally unramified over `k` and essentially of
finite type. -/
theorem smSchemeOver_isReduced_of_formallyUnramifiedAffine
    (X : Geometry.SmSchemeOver k)
    (h :
      ∀ x : X.scheme,
        ∃ U : X.scheme.affineOpens,
          x ∈ U.1 ∧
          Algebra.FormallyUnramified k (Γ(X.scheme, U)) ∧
          Algebra.EssFiniteType k (Γ(X.scheme, U))) :
    IsReduced X.scheme :=
  isReduced_of_exists_affineNeighborhood_formallyUnramified (k := k) (X := X.scheme) h

/-- A smooth `k`-scheme is reduced if each point admits an affine neighborhood
whose coordinate ring is étale over `k`. -/
theorem smSchemeOver_isReduced_of_etaleAffine
    (X : Geometry.SmSchemeOver k)
    (h :
      ∀ x : X.scheme,
        ∃ U : X.scheme.affineOpens,
          x ∈ U.1 ∧
          Algebra.Etale k (Γ(X.scheme, U))) :
    IsReduced X.scheme :=
  isReduced_of_exists_affineNeighborhood_etale (k := k) (X := X.scheme) h

/-- The base product object `X ×_k Y` is reduced if its affine chart rings are
formally étale over `k` and essentially of finite type. -/
theorem overBaseProductObject_isReduced_of_formallyEtaleAffine
    (X Y : Geometry.SmSchemeOver k)
    (h :
      ∀ x : (overBaseProductObject X Y).scheme,
        ∃ U : (overBaseProductObject X Y).scheme.affineOpens,
          x ∈ U.1 ∧
          Algebra.FormallyEtale k (Γ((overBaseProductObject X Y).scheme, U)) ∧
          Algebra.EssFiniteType k (Γ((overBaseProductObject X Y).scheme, U))) :
    IsReduced (overBaseProductObject X Y).scheme :=
  smSchemeOver_isReduced_of_formallyEtaleAffine
    (X := overBaseProductObject X Y) h

/-- A scheme over `Spec k` is reduced if every point admits an affine
neighborhood whose coordinate ring is smooth over `k`, provided smooth
`k`-algebras are known to be reduced. This is the smooth-owner analogue of the
formally étale/unramified globalizers. -/
theorem isReduced_of_exists_affineNeighborhood_smooth
    (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))]
    (h :
      ∀ x : X,
        ∃ U : X.affineOpens,
          x ∈ U.1 ∧
          Algebra.Smooth k (Γ(X, U)))
    (hSmoothReduced :
      ∀ {A : Type u} [CommRing A] [Algebra k A],
        Algebra.Smooth k A → _root_.IsReduced A) :
    IsReduced X := by
  refine isReduced_of_exists_affineNeighborhood_reduced (X := X) ?_
  intro x
  rcases h x with ⟨U, hxU, hΓU⟩
  refine ⟨U, hxU, ?_⟩
  exact hSmoothReduced hΓU

/-- A smooth `k`-scheme is reduced if each point admits an affine neighborhood
whose coordinate ring is smooth over `k`, provided smooth `k`-algebras are
known to be reduced. -/
theorem smSchemeOver_isReduced_of_smoothAffine
    (X : Geometry.SmSchemeOver k)
    (h :
      ∀ x : X.scheme,
        ∃ U : X.scheme.affineOpens,
          x ∈ U.1 ∧
          Algebra.Smooth k (Γ(X.scheme, U)))
    (hSmoothReduced :
      ∀ {A : Type u} [CommRing A] [Algebra k A],
        Algebra.Smooth k A → _root_.IsReduced A) :
    IsReduced X.scheme :=
  isReduced_of_exists_affineNeighborhood_smooth (k := k) (X := X.scheme) h hSmoothReduced

/-- The base product object `X ×_k Y` is reduced if its affine chart rings are
smooth over `k`, provided smooth `k`-algebras are known to be reduced. -/
theorem overBaseProductObject_isReduced_of_smoothAffine
    (X Y : Geometry.SmSchemeOver k)
    (h :
      ∀ x : (overBaseProductObject X Y).scheme,
        ∃ U : (overBaseProductObject X Y).scheme.affineOpens,
          x ∈ U.1 ∧
          Algebra.Smooth k (Γ((overBaseProductObject X Y).scheme, U)))
    (hSmoothReduced :
      ∀ {A : Type u} [CommRing A] [Algebra k A],
        Algebra.Smooth k A → _root_.IsReduced A) :
    IsReduced (overBaseProductObject X Y).scheme :=
  smSchemeOver_isReduced_of_smoothAffine
    (X := overBaseProductObject X Y) h hSmoothReduced

/-- The base product object `X ×_k Y` is reduced if its affine chart rings are
formally unramified over `k` and essentially of finite type. -/
theorem overBaseProductObject_isReduced_of_formallyUnramifiedAffine
    (X Y : Geometry.SmSchemeOver k)
    (h :
      ∀ x : (overBaseProductObject X Y).scheme,
        ∃ U : (overBaseProductObject X Y).scheme.affineOpens,
          x ∈ U.1 ∧
          Algebra.FormallyUnramified k
            (Γ((overBaseProductObject X Y).scheme, U)) ∧
          Algebra.EssFiniteType k
            (Γ((overBaseProductObject X Y).scheme, U))) :
    IsReduced (overBaseProductObject X Y).scheme :=
  smSchemeOver_isReduced_of_formallyUnramifiedAffine
    (X := overBaseProductObject X Y) h

/-- The actual product object `X ×_k Y` is reduced once standard-smooth affine
chart rings over `k` are known to be formally unramified. -/
theorem overBaseProductObject_isReduced_of_standardSmoothAffineFormallyUnramified
    (X Y : Geometry.SmSchemeOver k)
    (hStandardUnramified :
      ∀ {A : Type u} [CommRing A] [Algebra k A],
        RingHom.IsStandardSmooth.{0, 0} (algebraMap k A) →
          Algebra.FormallyUnramified k A) :
    IsReduced (overBaseProductObject X Y).scheme :=
  smSchemeOver_isReduced_of_standardSmoothAffineFormallyUnramified
    (X := overBaseProductObject X Y) hStandardUnramified

/-- The actual product object `X ×_k Y` is reduced once standard-smooth affine
chart rings are known to be smooth over `k`, provided smooth `k`-algebras are
reduced. -/
theorem overBaseProductObject_isReduced_of_standardSmoothAffineSmooth
    (X Y : Geometry.SmSchemeOver k)
    (hStandardSmooth :
      ∀ {A : Type u} [CommRing A] [Algebra k A],
        RingHom.IsStandardSmooth.{0, 0} (algebraMap k A) → Algebra.Smooth k A)
    (hSmoothReduced :
      ∀ {A : Type u} [CommRing A] [Algebra k A],
        Algebra.Smooth k A → _root_.IsReduced A) :
    IsReduced (overBaseProductObject X Y).scheme :=
  smSchemeOver_isReduced_of_standardSmoothAffineSmooth
    (X := overBaseProductObject X Y) hStandardSmooth hSmoothReduced

/-- The actual product object `X ×_k Y` is reduced once standard-smooth affine
chart rings over `k` are known to be formally étale. -/
theorem overBaseProductObject_isReduced_of_standardSmoothAffineFormallyEtale
    (X Y : Geometry.SmSchemeOver k)
    (hStandardEtale :
      ∀ {A : Type u} [CommRing A] [Algebra k A],
        RingHom.IsStandardSmooth.{0, 0} (algebraMap k A) →
          Algebra.FormallyEtale k A) :
    IsReduced (overBaseProductObject X Y).scheme :=
  smSchemeOver_isReduced_of_standardSmoothAffineFormallyEtale
    (X := overBaseProductObject X Y) hStandardEtale

/-- The base product object `X ×_k Y` is reduced if its affine chart rings are
étale over `k`. -/
theorem overBaseProductObject_isReduced_of_etaleAffine
    (X Y : Geometry.SmSchemeOver k)
    (h :
      ∀ x : (overBaseProductObject X Y).scheme,
        ∃ U : (overBaseProductObject X Y).scheme.affineOpens,
          x ∈ U.1 ∧
          Algebra.Etale k (Γ((overBaseProductObject X Y).scheme, U))) :
    IsReduced (overBaseProductObject X Y).scheme :=
  smSchemeOver_isReduced_of_etaleAffine
    (X := overBaseProductObject X Y) h

/-- On a reduced scheme, an open subscheme whose underlying topological space
is irreducible is integral. This is the scheme-theoretic bridge from local
irreducibility plus reducedness to integral component opens. -/
theorem isIntegral_openSubscheme_of_isIrreducible
    {X : Scheme.{u}} [IsReduced X]
    (U : X.Opens) (hIrred : IsIrreducible (U : Set X)) :
    IsIntegral U.toScheme := by
  letI : IsReduced U.toScheme := AlgebraicGeometry.isReduced_of_isOpenImmersion U.ι
  letI : IrreducibleSpace U := Subtype.irreducibleSpace hIrred
  letI : IrreducibleSpace U.toScheme := by
    exact (inferInstance : IrreducibleSpace U)
  exact AlgebraicGeometry.isIntegral_of_irreducibleSpace_of_isReduced U.toScheme

/-- On a reduced locally irreducible scheme, each irreducible component open
subscheme is integral. This is the canonical bottom theorem consumed by the
source-component decomposition owner. -/
theorem irreducibleComponentOpen_isIntegral_of_isReduced_locallyIrreducible
    (X : Scheme.{u}) [IsReduced X]
    (hLoc : Geometry.Topology.LocallyIrreducibleSpace X) :
    ∀ C : { C : Set X // C ∈ irreducibleComponents X },
      IsIntegral
        (Scheme.Opens.toScheme
          (⟨C.1,
            Geometry.Topology.isOpen_irreducibleComponent_of_locallyIrreducible
              C.2 hLoc⟩ :
            X.Opens)) := by
  intro C
  let U : X.Opens :=
    ⟨C.1,
      Geometry.Topology.isOpen_irreducibleComponent_of_locallyIrreducible
        C.2 hLoc⟩
  have hIrred : IsIrreducible (U : Set X) := by
    change IsIrreducible C.1
    exact C.2.1
  change IsIntegral U.toScheme
  exact isIntegral_openSubscheme_of_isIrreducible U hIrred

/-- On a reduced scheme, if each irreducible component is known to be open,
then the corresponding open component subschemes are integral. This is the
more primitive owner theorem; the locally irreducible version is obtained by
supplying component openness from local irreducibility. -/
theorem irreducibleComponentOpen_isIntegral_of_isReduced_componentsOpen
    (X : Scheme.{u}) [IsReduced X]
    (hOpen :
      ∀ C : { C : Set X // C ∈ irreducibleComponents X },
        IsOpen C.1) :
    ∀ C : { C : Set X // C ∈ irreducibleComponents X },
      IsIntegral
        (Scheme.Opens.toScheme
          (⟨C.1, hOpen C⟩ : X.Opens)) := by
  intro C
  have hIrred : IsIrreducible C.1 := C.2.1
  exact
    isIntegral_openSubscheme_of_isIrreducible
      (X := X) (U := (⟨C.1, hOpen C⟩ : X.Opens)) hIrred

/-- Reduced locally irreducible smooth schemes admit the canonical finite
source-component decomposition with no extra integrality input, because the
component opens are automatically integral. -/
noncomputable def finiteSourceIrreducibleComponentDecompositionOfReducedLocallyIrreducible
    (X : Geometry.SmSchemeOver k)
    [IsReduced X.scheme]
    (hLoc : Geometry.Topology.LocallyIrreducibleSpace X.scheme) :
    FiniteIrreducibleComponentDecomposition X :=
  finiteSourceIrreducibleComponentDecompositionOfLocallyIrreducible X hLoc
    (irreducibleComponentOpen_isIntegral_of_isReduced_locallyIrreducible
      X.scheme hLoc)

/-- Reduced smooth schemes with open irreducible components admit the
canonical finite source-component decomposition. This is the direct owner form
when component-openness is proved geometrically without passing through a
separate local-irreducibility theorem. -/
noncomputable def finiteSourceIrreducibleComponentDecompositionOfReducedComponentsOpen
    (X : Geometry.SmSchemeOver k)
    [IsReduced X.scheme]
    (hOpen :
      ∀ C : { C : Set X.scheme // C ∈ irreducibleComponents X.scheme },
        IsOpen C.1) :
    FiniteIrreducibleComponentDecomposition X :=
  finiteSourceIrreducibleComponentDecompositionOfClopenComponents X
    (fun C =>
      ⟨isClosed_of_mem_irreducibleComponents C.1 C.2, hOpen C⟩)
    (irreducibleComponentOpen_isIntegral_of_isReduced_componentsOpen
      X.scheme hOpen)

/-- Specialized owner theorem: if the irreducible components of `X ×_k Y` are
open, then its underlying topological space is locally irreducible. This is
just the generic topological theorem applied at the actual product object. -/
theorem overBaseProductObject_locallyIrreducible_of_componentsOpen
    (X Y : Geometry.SmSchemeOver k)
    (hOpen :
      ∀ C :
        { C : Set (overBaseProductObject X Y).scheme //
            C ∈ irreducibleComponents (overBaseProductObject X Y).scheme },
        IsOpen C.1) :
    Geometry.Topology.LocallyIrreducibleSpace (overBaseProductObject X Y).scheme :=
  locallyIrreducibleSpace_of_irreducibleComponents_open
    (X := (overBaseProductObject X Y).scheme) hOpen

/-- Specialized owner theorem: reduced product objects with open irreducible
components admit the canonical finite source-component decomposition. -/
noncomputable def overBaseProductObject_componentDecompositionOfReducedComponentsOpen
    (X Y : Geometry.SmSchemeOver k)
    [IsReduced (overBaseProductObject X Y).scheme]
    (hOpen :
      ∀ C :
        { C : Set (overBaseProductObject X Y).scheme //
            C ∈ irreducibleComponents (overBaseProductObject X Y).scheme },
        IsOpen C.1) :
    FiniteIrreducibleComponentDecomposition (overBaseProductObject X Y) :=
  finiteSourceIrreducibleComponentDecompositionOfReducedComponentsOpen
    (overBaseProductObject X Y) hOpen

/-- Specialized owner theorem: reduced locally irreducible product objects
admit the canonical finite source-component decomposition. -/
noncomputable def overBaseProductObject_componentDecompositionOfReducedLocallyIrreducible
    (X Y : Geometry.SmSchemeOver k)
    [IsReduced (overBaseProductObject X Y).scheme]
    (hLoc :
      Geometry.Topology.LocallyIrreducibleSpace (overBaseProductObject X Y).scheme) :
    FiniteIrreducibleComponentDecomposition (overBaseProductObject X Y) :=
  finiteSourceIrreducibleComponentDecompositionOfReducedLocallyIrreducible
    (overBaseProductObject X Y) hLoc

end -- noncomputable section

end Boundary

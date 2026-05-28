import Boundary.Basic
import Boundary.SmOver
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Topology.Irreducible

universe u

variable {k : Type u} [Field k] [PerfectField k]

open AlgebraicGeometry CategoryTheory Limits

namespace Boundary

noncomputable section

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

abbrev toAmbient {X : Geometry.SmSchemeOver k}
    (component : SourceIrreducibleComponent X) :
    component.carrier.scheme ⟶ X.scheme :=
  component.immersion

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

theorem toAmbient_overBase {X : Geometry.SmSchemeOver k}
    (component : SourceIrreducibleComponent X) :
    component.toAmbient ≫ X.structMap = component.carrier.structMap :=
  component.overBase

structure IsoOverAmbient {X : Geometry.SmSchemeOver k}
    (C D : SourceIrreducibleComponent X) where
  iso : C.carrier.scheme ≅ D.carrier.scheme
  hom_toAmbient : iso.hom ≫ D.toAmbient = C.toAmbient

namespace IsoOverAmbient

def refl {X : Geometry.SmSchemeOver k}
    (C : SourceIrreducibleComponent X) : IsoOverAmbient C C where
  iso := Iso.refl _
  hom_toAmbient := by simp

def symm {X : Geometry.SmSchemeOver k}
    {C D : SourceIrreducibleComponent X} (h : IsoOverAmbient C D) :
    IsoOverAmbient D C where
  iso := h.iso.symm
  hom_toAmbient := by
    calc
      h.iso.inv ≫ C.toAmbient = h.iso.inv ≫ (h.iso.hom ≫ D.toAmbient) := by
        rw [h.hom_toAmbient]
      _ = D.toAmbient := by simp [Category.assoc]

def trans {X : Geometry.SmSchemeOver k}
    {C D E : SourceIrreducibleComponent X}
    (hCD : IsoOverAmbient C D) (hDE : IsoOverAmbient D E) :
    IsoOverAmbient C E where
  iso := hCD.iso ≪≫ hDE.iso
  hom_toAmbient := by
    calc
      (hCD.iso ≪≫ hDE.iso).hom ≫ E.toAmbient = hCD.iso.hom ≫ (hDE.iso.hom ≫ E.toAmbient) := by
        simp [Category.assoc]
      _ = hCD.iso.hom ≫ D.toAmbient := by rw [hDE.hom_toAmbient]
      _ = C.toAmbient := by rw [hCD.hom_toAmbient]

theorem hom_structMap {X : Geometry.SmSchemeOver k}
    {C D : SourceIrreducibleComponent X} (h : IsoOverAmbient C D) :
    h.iso.hom ≫ D.carrier.structMap = C.carrier.structMap := by
  calc
    h.iso.hom ≫ D.carrier.structMap = h.iso.hom ≫ (D.toAmbient ≫ X.structMap) := by
      rw [D.toAmbient_overBase]
    _ = (h.iso.hom ≫ D.toAmbient) ≫ X.structMap := by simp [Category.assoc]
    _ = C.toAmbient ≫ X.structMap := by rw [h.hom_toAmbient]
    _ = C.carrier.structMap := C.toAmbient_overBase

noncomputable def overBaseProductIso {X : Geometry.SmSchemeOver k} {Y : Geometry.SmSchemeOver k}
    {C D : SourceIrreducibleComponent X} (h : IsoOverAmbient C D) :
    pullback C.carrier.structMap Y.structMap ≅ pullback D.carrier.structMap Y.structMap := by
  refine asIso <|
    pullback.map C.carrier.structMap Y.structMap D.carrier.structMap Y.structMap
      h.iso.hom (𝟙 Y.scheme) (𝟙 (Spec (CommRingCat.of k))) ?_ ?_
  · simpa using h.hom_structMap.symm
  · simp

@[simp] theorem overBaseProductIso_hom_fst {X : Geometry.SmSchemeOver k}
    {Y : Geometry.SmSchemeOver k} {C D : SourceIrreducibleComponent X}
    (h : IsoOverAmbient C D) :
    (h.overBaseProductIso (Y := Y)).hom ≫ pullback.fst D.carrier.structMap Y.structMap =
      pullback.fst C.carrier.structMap Y.structMap ≫ h.iso.hom := by
  simp [IsoOverAmbient.overBaseProductIso, Category.assoc]

@[simp] theorem overBaseProductIso_hom_snd {X : Geometry.SmSchemeOver k}
    {Y : Geometry.SmSchemeOver k} {C D : SourceIrreducibleComponent X}
    (h : IsoOverAmbient C D) :
    (h.overBaseProductIso (Y := Y)).hom ≫ pullback.snd D.carrier.structMap Y.structMap =
      pullback.snd C.carrier.structMap Y.structMap := by
  simp [IsoOverAmbient.overBaseProductIso, Category.assoc]

/-- Explicit compatibility between represented source components and the
induced fiber products with a target. -/
structure CompatibleOverBaseProductIso {X : Geometry.SmSchemeOver k}
    {Y : Geometry.SmSchemeOver k}
    (C D : SourceIrreducibleComponent X) where
  sourceIso : IsoOverAmbient C D
  iso : overBaseProduct C.carrier Y ≅ overBaseProduct D.carrier Y

namespace CompatibleOverBaseProductIso

/-- Reflexive compatibility of source components and their fiber products. -/
def refl {X : Geometry.SmSchemeOver k} {Y : Geometry.SmSchemeOver k}
    (C : SourceIrreducibleComponent X) : CompatibleOverBaseProductIso (Y := Y) C C where
  sourceIso := IsoOverAmbient.refl C
  iso := Iso.refl _

/-- Symmetry of compatibility of source components and their fiber products. -/
def symm {X : Geometry.SmSchemeOver k} {Y : Geometry.SmSchemeOver k}
    {C D : SourceIrreducibleComponent X}
    (h : CompatibleOverBaseProductIso (Y := Y) C D) :
    CompatibleOverBaseProductIso (Y := Y) D C where
  sourceIso := h.sourceIso.symm
  iso := h.iso.symm

/-- Transitivity of compatibility of source components and their fiber products. -/
def trans {X : Geometry.SmSchemeOver k} {Y : Geometry.SmSchemeOver k}
    {C D E : SourceIrreducibleComponent X}
    (hCD : CompatibleOverBaseProductIso (Y := Y) C D)
    (hDE : CompatibleOverBaseProductIso (Y := Y) D E) :
    CompatibleOverBaseProductIso (Y := Y) C E where
  sourceIso := hCD.sourceIso.trans hDE.sourceIso
  iso := hCD.iso ≪≫ hDE.iso

/-- The canonical fiber-product compatibility induced by a source-component
isomorphism over the ambient source. -/
def ofIsoOverAmbient {X : Geometry.SmSchemeOver k} {Y : Geometry.SmSchemeOver k}
    {C D : SourceIrreducibleComponent X} (h : IsoOverAmbient C D) :
    CompatibleOverBaseProductIso (Y := Y) C D where
  sourceIso := h
  iso := h.overBaseProductIso (Y := Y)

end CompatibleOverBaseProductIso

end IsoOverAmbient

end SourceIrreducibleComponent

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

end FiniteIrreducibleComponentDecomposition

/-- Smooth schemes of finite type over a field have finitely many topological
irreducible components. This is the raw finiteness input behind any future
construction of `FiniteIrreducibleComponentDecomposition`. -/
theorem finite_irreducibleComponents (X : Geometry.SmSchemeOver k) :
    (irreducibleComponents X.scheme).Finite :=
  AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian

end -- noncomputable section

end Boundary

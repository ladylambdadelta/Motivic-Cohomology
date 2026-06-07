import Mathlib.CategoryTheory.Category.Basic
import Boundary.Hodge.HodgeClasses

/-!
# Morphisms of pure rational Hodge structures

This file defines morphisms at the linear-algebra level: rational linear maps
whose complexifications preserve the Hodge decomposition pieces.
-/

namespace Boundary
namespace Hodge

open CategoryTheory

namespace PureHodgeStructure

/-- The scalar extension of a rational linear map to complexifications. -/
noncomputable def complexificationMap (H G : PureHodgeStructure)
    (f : H.rationalCarrier →ₗ[ℚ] G.rationalCarrier) :
    Complexification H.rationalCarrier →ₗ[ℂ] Complexification G.rationalCarrier :=
  TensorProduct.AlgebraTensorModule.lTensor ℂ ℂ f

@[simp]
theorem complexificationMap_tmul (H G : PureHodgeStructure)
    (f : H.rationalCarrier →ₗ[ℚ] G.rationalCarrier)
    (z : ℂ) (x : H.rationalCarrier) :
    H.complexificationMap G f (TensorProduct.mk ℚ ℂ H.rationalCarrier z x) =
      TensorProduct.mk ℚ ℂ G.rationalCarrier z (f x) :=
  TensorProduct.AlgebraTensorModule.lTensor_tmul f z x

@[simp]
theorem complexificationMap_complexifyVector (H G : PureHodgeStructure)
    (f : H.rationalCarrier →ₗ[ℚ] G.rationalCarrier) (x : H.rationalCarrier) :
    H.complexificationMap G f (H.complexifyVector x) =
      G.complexifyVector (f x) := by
  rfl

theorem complexificationMap_comp (H G K : PureHodgeStructure)
    (f : H.rationalCarrier →ₗ[ℚ] G.rationalCarrier)
    (g : G.rationalCarrier →ₗ[ℚ] K.rationalCarrier) :
    H.complexificationMap K (g.comp f) =
      (G.complexificationMap K g).comp (H.complexificationMap G f) := by
  ext z x
  rfl

@[simp]
theorem complexificationMap_id (H : PureHodgeStructure) :
    H.complexificationMap H LinearMap.id = LinearMap.id := by
  ext z x
  rfl

@[simp]
theorem complexificationMap_linearEquiv (H G : PureHodgeStructure)
    (e : H.rationalCarrier ≃ₗ[ℚ] G.rationalCarrier) :
    H.complexificationMap G e.toLinearMap =
      Complexification.mapLinearEquiv H.rationalCarrier G.rationalCarrier e := rfl

@[simp]
theorem complexificationMap_fst_product (H G : PureHodgeStructure) (hweight : H.weight = G.weight)
    (x : Complexification (H.rationalCarrier × G.rationalCarrier)) :
    (H.product G hweight).complexificationMap H
        (LinearMap.fst ℚ H.rationalCarrier G.rationalCarrier) x =
      (Complexification.productEquiv H.rationalCarrier G.rationalCarrier x).1 := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro z vw
    rcases vw with ⟨v, w⟩
    change TensorProduct.mk ℚ ℂ H.rationalCarrier z v =
      ((Complexification.productEquiv H.rationalCarrier G.rationalCarrier)
        (TensorProduct.mk ℚ ℂ (H.rationalCarrier × G.rationalCarrier) z (v, w))).1
    rw [Complexification.productEquiv_tmul_fst]
  · intro x y hx hy
    simp [LinearMap.map_add, hx, hy]

@[simp]
theorem complexificationMap_snd_product (H G : PureHodgeStructure) (hweight : H.weight = G.weight)
    (x : Complexification (H.rationalCarrier × G.rationalCarrier)) :
    (H.product G hweight).complexificationMap G
        (LinearMap.snd ℚ H.rationalCarrier G.rationalCarrier) x =
      (Complexification.productEquiv H.rationalCarrier G.rationalCarrier x).2 := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro z vw
    rcases vw with ⟨v, w⟩
    change TensorProduct.mk ℚ ℂ G.rationalCarrier z w =
      ((Complexification.productEquiv H.rationalCarrier G.rationalCarrier)
        (TensorProduct.mk ℚ ℂ (H.rationalCarrier × G.rationalCarrier) z (v, w))).2
    rw [Complexification.productEquiv_tmul_snd]
  · intro x y hx hy
    simp [LinearMap.map_add, hx, hy]

@[simp]
theorem productEquiv_complexificationMap_inl (H G : PureHodgeStructure) (hweight : H.weight = G.weight)
    (x : Complexification H.rationalCarrier) :
    Complexification.productEquiv H.rationalCarrier G.rationalCarrier
      (H.complexificationMap (H.product G hweight)
        (LinearMap.inl ℚ H.rationalCarrier G.rationalCarrier) x) = (x, 0) := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro z v
    change (Complexification.productEquiv H.rationalCarrier G.rationalCarrier)
        (TensorProduct.mk ℚ ℂ (H.rationalCarrier × G.rationalCarrier) z (v, 0)) =
      (TensorProduct.mk ℚ ℂ H.rationalCarrier z v, 0)
    rw [Complexification.productEquiv_tmul]
    simp
  · intro x y hx hy
    simp [LinearMap.map_add, hx, hy]

@[simp]
theorem productEquiv_complexificationMap_inr (H G : PureHodgeStructure) (hweight : H.weight = G.weight)
    (x : Complexification G.rationalCarrier) :
    Complexification.productEquiv H.rationalCarrier G.rationalCarrier
      (G.complexificationMap (H.product G hweight)
        (LinearMap.inr ℚ H.rationalCarrier G.rationalCarrier) x) = (0, x) := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro z v
    change (Complexification.productEquiv H.rationalCarrier G.rationalCarrier)
        (TensorProduct.mk ℚ ℂ (H.rationalCarrier × G.rationalCarrier) z (0, v)) =
      (0, TensorProduct.mk ℚ ℂ G.rationalCarrier z v)
    rw [Complexification.productEquiv_tmul]
    simp
  · intro x y hx hy
    simp [LinearMap.map_add, hx, hy]

/-- A morphism of pure rational Hodge structures is a rational linear map whose
complexification sends each Hodge piece into the corresponding Hodge piece. -/
structure Hom (H G : PureHodgeStructure) where
  linear : H.rationalCarrier →ₗ[ℚ] G.rationalCarrier
  map_hodgePiece :
    ∀ pq, (H.hodgePiece pq).map (H.complexificationMap G linear) ≤ G.hodgePiece pq

namespace Hom

@[ext]
theorem ext {H G : PureHodgeStructure} {f g : Hom H G}
    (h : f.linear = g.linear) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance (H G : PureHodgeStructure) : CoeFun (Hom H G)
    (fun _ => H.rationalCarrier → G.rationalCarrier) where
  coe f := f.linear

/-- The complexification of a morphism. -/
noncomputable def complexification {H G : PureHodgeStructure} (f : Hom H G) :
    Complexification H.rationalCarrier →ₗ[ℂ] Complexification G.rationalCarrier :=
  H.complexificationMap G f.linear

theorem maps_hodgePiece {H G : PureHodgeStructure} (f : Hom H G) (pq : ℤ × ℤ)
    {x : Complexification H.rationalCarrier} (hx : x ∈ H.hodgePiece pq) :
    f.complexification x ∈ G.hodgePiece pq := by
  exact f.map_hodgePiece pq ⟨x, hx, rfl⟩

theorem isHodgeClass_map {H G : PureHodgeStructure} (f : Hom H G)
    (p : ℤ) (hH : H.weight = 2 * p) (hG : G.weight = 2 * p)
    {x : H.rationalCarrier} (hx : H.IsHodgeClass p hH x) :
    G.IsHodgeClass p hG (f.linear x) := by
  change G.complexifyVector (f.linear x) ∈ G.hodgePiece (p, p)
  rw [← H.complexificationMap_complexifyVector G f.linear x]
  exact f.maps_hodgePiece (p, p) hx

theorem map_hodgeClasses_le {H G : PureHodgeStructure} (f : Hom H G)
    (p : ℤ) (hH : H.weight = 2 * p) (hG : G.weight = 2 * p) :
    (H.hodgeClasses p hH).map f.linear ≤ G.hodgeClasses p hG := by
  rintro _ ⟨x, hx, rfl⟩
  exact f.isHodgeClass_map p hH hG hx

/-- The identity morphism of a pure rational Hodge structure. -/
def id (H : PureHodgeStructure) : Hom H H where
  linear := LinearMap.id
  map_hodgePiece pq := by
    rintro _ ⟨x, hx, rfl⟩
    simpa using hx

@[simp]
theorem id_linear (H : PureHodgeStructure) :
    (id H).linear = LinearMap.id := rfl

@[simp]
theorem id_apply (H : PureHodgeStructure) (x : H.rationalCarrier) :
    id H x = x := rfl

/-- Composition of morphisms of pure rational Hodge structures. -/
def comp {H G K : PureHodgeStructure} (f : Hom H G) (g : Hom G K) : Hom H K where
  linear := g.linear.comp f.linear
  map_hodgePiece pq := by
    rintro _ ⟨x, hx, rfl⟩
    rw [complexificationMap_comp]
    exact g.maps_hodgePiece pq (f.maps_hodgePiece pq hx)

@[simp]
theorem comp_linear {H G K : PureHodgeStructure} (f : Hom H G) (g : Hom G K) :
    (comp f g).linear = g.linear.comp f.linear := rfl

@[simp]
theorem comp_apply {H G K : PureHodgeStructure} (f : Hom H G) (g : Hom G K)
    (x : H.rationalCarrier) :
    comp f g x = g.linear (f.linear x) := rfl

theorem map_hodgeClasses_comp {H G K : PureHodgeStructure} (f : Hom H G) (g : Hom G K)
    (p : ℤ) (hH : H.weight = 2 * p) (_hG : G.weight = 2 * p)
    (hK : K.weight = 2 * p) :
    ((H.hodgeClasses p hH).map f.linear).map g.linear ≤ K.hodgeClasses p hK := by
  rintro _ ⟨y, ⟨x, hx, rfl⟩, rfl⟩
  exact (comp f g).map_hodgeClasses_le p hH hK ⟨x, hx, rfl⟩

theorem map_hodgeClasses_id (H : PureHodgeStructure)
    (p : ℤ) (hH : H.weight = 2 * p) :
    (H.hodgeClasses p hH).map (id H).linear = H.hodgeClasses p hH := by
  ext x
  simp

/-- The zero morphism of pure rational Hodge structures of the same weight. -/
def zeroHom (H G : PureHodgeStructure) (_hweight : H.weight = G.weight) : Hom H G where
  linear := 0
  map_hodgePiece pq := by
    rintro _ ⟨x, hx, rfl⟩
    change ((H.complexificationMap G 0) x) ∈ G.hodgePiece pq
    simp [PureHodgeStructure.complexificationMap]

/-- The tautological morphism from a pulled-back Hodge structure to the original one. -/
def ofLinearEquivHom (H : PureHodgeStructure)
    {V : Type} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (e : V ≃ₗ[ℚ] H.rationalCarrier) :
    Hom (H.ofLinearEquiv e) H where
  linear := e.toLinearMap
  map_hodgePiece pq := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [PureHodgeStructure.ofLinearEquiv, PureHodgeStructure.complexificationMap,
      PureHodgeStructure.complexifyVector] using hx

@[simp]
theorem ofLinearEquivHom_apply (H : PureHodgeStructure)
    {V : Type} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (e : V ≃ₗ[ℚ] H.rationalCarrier) (x : V) :
    (ofLinearEquivHom H e).linear x = e x := rfl

/-- The tautological morphism from a Hodge structure to its pullback along a
rational linear equivalence. -/
def toOfLinearEquivHom (H : PureHodgeStructure)
    {V : Type} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (e : V ≃ₗ[ℚ] H.rationalCarrier) :
    Hom H (H.ofLinearEquiv e) where
  linear := e.symm.toLinearMap
  map_hodgePiece pq := by
    rintro _ ⟨x, hx, rfl⟩
    change (Complexification.mapLinearEquiv V H.rationalCarrier e)
        ((Complexification.mapLinearEquiv V H.rationalCarrier e).symm x) ∈ H.hodgePiece pq
    have h :=
      (Complexification.mapLinearEquiv V H.rationalCarrier e).apply_symm_apply x
    rw [h]
    exact hx

@[simp]
theorem toOfLinearEquivHom_apply (H : PureHodgeStructure)
    {V : Type} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (e : V ≃ₗ[ℚ] H.rationalCarrier) (x : H.rationalCarrier) :
    (toOfLinearEquivHom H e).linear x = e.symm x := rfl

@[simp]
theorem ofLinearEquivHom_toOfLinearEquivHom_apply (H : PureHodgeStructure)
    {V : Type} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (e : V ≃ₗ[ℚ] H.rationalCarrier) (x : H.rationalCarrier) :
    (ofLinearEquivHom H e).linear ((toOfLinearEquivHom H e).linear x) = x := by
  rw [toOfLinearEquivHom_apply, ofLinearEquivHom_apply]
  exact e.apply_symm_apply x

@[simp]
theorem toOfLinearEquivHom_ofLinearEquivHom_apply (H : PureHodgeStructure)
    {V : Type} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (e : V ≃ₗ[ℚ] H.rationalCarrier) (x : V) :
    (toOfLinearEquivHom H e).linear ((ofLinearEquivHom H e).linear x) = x := by
  rw [ofLinearEquivHom_apply, toOfLinearEquivHom_apply]
  exact e.symm_apply_apply x

/-- Projection from the product of same-weight pure Hodge structures to the left factor. -/
def fstHom (H G : PureHodgeStructure) (hweight : H.weight = G.weight) :
    Hom (H.product G hweight) H where
  linear := LinearMap.fst ℚ H.rationalCarrier G.rationalCarrier
  map_hodgePiece pq := by
    rintro _ ⟨x, hx, rfl⟩
    rw [complexificationMap_fst_product]
    exact hx.1

/-- Projection from the product of same-weight pure Hodge structures to the right factor. -/
def sndHom (H G : PureHodgeStructure) (hweight : H.weight = G.weight) :
    Hom (H.product G hweight) G where
  linear := LinearMap.snd ℚ H.rationalCarrier G.rationalCarrier
  map_hodgePiece pq := by
    rintro _ ⟨x, hx, rfl⟩
    rw [complexificationMap_snd_product]
    exact hx.2

@[simp]
theorem complexificationMap_prod (H G K : PureHodgeStructure)
    (f : H.rationalCarrier →ₗ[ℚ] G.rationalCarrier)
    (g : H.rationalCarrier →ₗ[ℚ] K.rationalCarrier)
    (hweight : G.weight = K.weight)
    (x : Complexification H.rationalCarrier) :
    Complexification.productEquiv G.rationalCarrier K.rationalCarrier
      (H.complexificationMap (G.product K hweight) (LinearMap.prod f g) x) =
        (H.complexificationMap G f x, H.complexificationMap K g x) := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro z v
    change Complexification.productEquiv G.rationalCarrier K.rationalCarrier
        (TensorProduct.mk ℚ ℂ (G.rationalCarrier × K.rationalCarrier) z (f v, g v)) =
      (TensorProduct.mk ℚ ℂ G.rationalCarrier z (f v),
        TensorProduct.mk ℚ ℂ K.rationalCarrier z (g v))
    rw [Complexification.productEquiv_tmul]
  · intro x y hx hy
    simp [LinearMap.map_add, hx, hy]

/-- Pair two pure Hodge morphisms with common source into a product target. -/
def pairHom {H G K : PureHodgeStructure}
    (f : Hom H G) (g : Hom H K) (hweight : G.weight = K.weight) :
    Hom H (G.product K hweight) where
  linear := LinearMap.prod f.linear g.linear
  map_hodgePiece pq := by
    rintro _ ⟨x, hx, rfl⟩
    change Complexification.productEquiv G.rationalCarrier K.rationalCarrier
      (H.complexificationMap (G.product K hweight) (LinearMap.prod f.linear g.linear) x) ∈
        submoduleProd ℂ (Complexification G.rationalCarrier) (G.hodgePiece pq) (K.hodgePiece pq)
    rw [complexificationMap_prod _ _ _ _ _ hweight]
    exact (mem_submoduleProd (K := ℂ) (V := Complexification G.rationalCarrier)
      (x := (H.complexificationMap G f.linear x, H.complexificationMap K g.linear x))).2
        ⟨f.maps_hodgePiece pq hx, g.maps_hodgePiece pq hx⟩

/-- Inclusion of the left factor into the product of same-weight pure Hodge structures. -/
def inlHom (H G : PureHodgeStructure) (hweight : H.weight = G.weight) :
    Hom H (H.product G hweight) where
  linear := LinearMap.inl ℚ H.rationalCarrier G.rationalCarrier
  map_hodgePiece pq := by
    rintro _ ⟨x, hx, rfl⟩
    change Complexification.productEquiv H.rationalCarrier G.rationalCarrier
      (H.complexificationMap (H.product G hweight)
        (LinearMap.inl ℚ H.rationalCarrier G.rationalCarrier) x) ∈
        submoduleProd ℂ (Complexification H.rationalCarrier) (H.hodgePiece pq) (G.hodgePiece pq)
    rw [productEquiv_complexificationMap_inl]
    exact (mem_submoduleProd (K := ℂ) (V := Complexification H.rationalCarrier)
      (x := (x, (0 : Complexification G.rationalCarrier)))).2 ⟨hx, zero_mem _⟩

/-- Inclusion of the right factor into the product of same-weight pure Hodge structures. -/
def inrHom (H G : PureHodgeStructure) (hweight : H.weight = G.weight) :
    Hom G (H.product G hweight) where
  linear := LinearMap.inr ℚ H.rationalCarrier G.rationalCarrier
  map_hodgePiece pq := by
    rintro _ ⟨x, hx, rfl⟩
    change Complexification.productEquiv H.rationalCarrier G.rationalCarrier
      (G.complexificationMap (H.product G hweight)
        (LinearMap.inr ℚ H.rationalCarrier G.rationalCarrier) x) ∈
        submoduleProd ℂ (Complexification H.rationalCarrier) (H.hodgePiece pq) (G.hodgePiece pq)
    rw [productEquiv_complexificationMap_inr]
    exact (mem_submoduleProd (K := ℂ) (V := Complexification H.rationalCarrier)
      (x := ((0 : Complexification H.rationalCarrier), x))).2 ⟨zero_mem _, hx⟩

@[simp] theorem fstHom_apply (H G : PureHodgeStructure) (hweight : H.weight = G.weight)
    (x : H.rationalCarrier × G.rationalCarrier) :
    fstHom H G hweight x = x.1 := rfl

@[simp] theorem sndHom_apply (H G : PureHodgeStructure) (hweight : H.weight = G.weight)
    (x : H.rationalCarrier × G.rationalCarrier) :
    sndHom H G hweight x = x.2 := rfl

@[simp] theorem inlHom_apply (H G : PureHodgeStructure) (hweight : H.weight = G.weight)
    (x : H.rationalCarrier) :
    inlHom H G hweight x = (x, 0) := rfl

@[simp] theorem inrHom_apply (H G : PureHodgeStructure) (hweight : H.weight = G.weight)
    (x : G.rationalCarrier) :
    inrHom H G hweight x = (0, x) := rfl

@[simp] theorem zeroHom_apply (H G : PureHodgeStructure) (hweight : H.weight = G.weight)
    (x : H.rationalCarrier) :
    zeroHom H G hweight x = 0 := rfl

@[simp] theorem pairHom_apply {H G K : PureHodgeStructure}
    (f : Hom H G) (g : Hom H K) (hweight : G.weight = K.weight)
    (x : H.rationalCarrier) :
    pairHom f g hweight x = (f.linear x, g.linear x) := rfl

end Hom

/-- Pure rational Hodge structures whose weight is equal to a fixed integer. -/
structure OfWeight (w : ℤ) where
  hodge : PureHodgeStructure
  weight_eq : hodge.weight = w

namespace OfWeight

instance (w : ℤ) : CoeSort (OfWeight w) (Type _) where
  coe H := H.hodge.rationalCarrier

instance (w : ℤ) (H : OfWeight w) : AddCommGroup H :=
  H.hodge.rationalAddCommGroup

instance (w : ℤ) (H : OfWeight w) : Module ℚ H :=
  H.hodge.rationalModule

instance (w : ℤ) : Category (OfWeight w) where
  Hom H G := Hom H.hodge G.hodge
  id H := Hom.id H.hodge
  comp f g := Hom.comp f g
  id_comp f := by
    apply Hom.ext
    rfl
  comp_id f := by
    apply Hom.ext
    rfl
  assoc f g h := by
    apply Hom.ext
    rfl

@[simp]
theorem id_hom_linear {w : ℤ} (H : OfWeight w) :
    (𝟙 H : H ⟶ H).linear = LinearMap.id := rfl

@[simp]
theorem comp_hom_linear {w : ℤ} {H G K : OfWeight w}
    (f : H ⟶ G) (g : G ⟶ K) :
    (f ≫ g).linear = g.linear.comp f.linear := rfl

/-- The categorical product object in fixed weight `w`. -/
noncomputable def prod {w : ℤ} (H G : OfWeight w) : OfWeight w where
  hodge := H.hodge.product G.hodge (by simp [H.weight_eq, G.weight_eq])
  weight_eq := by simp [PureHodgeStructure.product, H.weight_eq]

/-- First projection from the fixed-weight product. -/
def fst {w : ℤ} (H G : OfWeight w) : prod H G ⟶ H :=
  Hom.fstHom H.hodge G.hodge (by simp [H.weight_eq, G.weight_eq])

/-- Second projection from the fixed-weight product. -/
def snd {w : ℤ} (H G : OfWeight w) : prod H G ⟶ G :=
  Hom.sndHom H.hodge G.hodge (by simp [H.weight_eq, G.weight_eq])

/-- Pairing into the fixed-weight product. -/
def lift {w : ℤ} {X H G : OfWeight w} (f : X ⟶ H) (g : X ⟶ G) : X ⟶ prod H G :=
  Hom.pairHom f g (by simp [H.weight_eq, G.weight_eq])

/-- Inclusion of the left factor into the fixed-weight product. -/
def inl {w : ℤ} (H G : OfWeight w) : H ⟶ prod H G :=
  lift (𝟙 H) (Hom.zeroHom H.hodge G.hodge (by simp [H.weight_eq, G.weight_eq]))

/-- Inclusion of the right factor into the fixed-weight product. -/
def inr {w : ℤ} (H G : OfWeight w) : G ⟶ prod H G :=
  lift (Hom.zeroHom G.hodge H.hodge (by simp [H.weight_eq, G.weight_eq])) (𝟙 G)

@[simp]
theorem fst_lift {w : ℤ} {X H G : OfWeight w} (f : X ⟶ H) (g : X ⟶ G) :
    lift f g ≫ fst H G = f := by
  apply Hom.ext
  rfl

@[simp]
theorem snd_lift {w : ℤ} {X H G : OfWeight w} (f : X ⟶ H) (g : X ⟶ G) :
    lift f g ≫ snd H G = g := by
  apply Hom.ext
  rfl

@[simp]
theorem fst_inl {w : ℤ} (H G : OfWeight w) :
    inl H G ≫ fst H G = 𝟙 H := by
  simp [inl]

@[simp]
theorem snd_inl {w : ℤ} (H G : OfWeight w) :
    inl H G ≫ snd H G =
      Hom.zeroHom H.hodge G.hodge (by simp [H.weight_eq, G.weight_eq]) := by
  simp [inl]

@[simp]
theorem fst_inr {w : ℤ} (H G : OfWeight w) :
    inr H G ≫ fst H G =
      Hom.zeroHom G.hodge H.hodge (by simp [H.weight_eq, G.weight_eq]) := by
  simp [inr]

@[simp]
theorem snd_inr {w : ℤ} (H G : OfWeight w) :
    inr H G ≫ snd H G = 𝟙 G := by
  simp [inr]

theorem hom_ext {w : ℤ} {X H G : OfWeight w} (f g : X ⟶ prod H G)
    (hfst : f ≫ fst H G = g ≫ fst H G)
    (hsnd : f ≫ snd H G = g ≫ snd H G) : f = g := by
  apply Hom.ext
  ext x
  have h1 := congrArg (fun k : X ⟶ H => k.linear x) hfst
  have h2 := congrArg (fun k : X ⟶ G => k.linear x) hsnd
  exact Prod.ext h1 h2

theorem lift_eta {w : ℤ} {X H G : OfWeight w} (f : X ⟶ prod H G) :
    lift (f ≫ fst H G) (f ≫ snd H G) = f := by
  apply hom_ext
  · simp
  · simp

end OfWeight

end PureHodgeStructure

end Hodge
end Boundary

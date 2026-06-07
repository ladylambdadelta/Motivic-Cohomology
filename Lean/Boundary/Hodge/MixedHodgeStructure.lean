import Boundary.Hodge.Morphism

/-!
# Mixed Hodge structures

This file records the linear-algebra shape of a mixed Hodge structure: a
rational vector space with an increasing weight filtration, a decreasing Hodge
filtration on its complexification, and pure Hodge data on the actual
weight-graded quotients.

This follows Deligne's definition of mixed Hodge structures via pure Hodge
structures on `Gr_n^W`; cf. Deligne, "Théorie de Hodge II", §2, and
Peters-Steenbrink, *Mixed Hodge Structures*, Ch. 3.
-/

namespace Boundary
namespace Hodge

/-- A mixed Hodge structure at the rational linear-algebra level; cf.
Deligne, "Théorie de Hodge II", §2. -/
structure MixedHodgeStructure where
  rationalCarrier : Type
  rationalAddCommGroup : AddCommGroup rationalCarrier
  rationalModule : Module ℚ rationalCarrier
  rationalFinite : Module.Finite ℚ rationalCarrier
  weightFiltration : IncreasingFiltration ℚ rationalCarrier
  hodgeFiltration : DecreasingFiltration ℂ (Complexification rationalCarrier)
  gradedPieceHodgePiece :
    ∀ n : ℤ, ℤ × ℤ → Submodule ℂ (Complexification (weightFiltration.gradedPiece n))
  gradedPieceHodgePiece_free :
    ∀ n pq, Module.Free ℂ (gradedPieceHodgePiece n pq)
  gradedPieceHodgePiece_finite :
    ∀ n pq, Module.Finite ℂ (gradedPieceHodgePiece n pq)
  gradedPieceHodgeFiltration :
    ∀ n : ℤ, DecreasingFiltration ℂ (Complexification (weightFiltration.gradedPiece n))
  gradedPieceOppositeFiltration :
    ∀ n : ℤ, DecreasingFiltration ℂ (Complexification (weightFiltration.gradedPiece n))
  gradedPiece_piece_le_filtration :
    ∀ ⦃n p r s : ℤ⦄, p ≤ r →
      gradedPieceHodgePiece n (r, s) ≤ (gradedPieceHodgeFiltration n).step p
  gradedPiece_piece_le_oppositeFiltration :
    ∀ ⦃n q r s : ℤ⦄, q ≤ s →
      gradedPieceHodgePiece n (r, s) ≤ (gradedPieceOppositeFiltration n).step q
  gradedPiece_filtration_inf_eq :
    ∀ ⦃n p q : ℤ⦄, p + q = n →
      (gradedPieceHodgeFiltration n).step p ⊓ (gradedPieceOppositeFiltration n).step q =
        gradedPieceHodgePiece n (p, q)
  gradedPiece_weight_zero :
    ∀ ⦃n p q : ℤ⦄, p + q ≠ n → gradedPieceHodgePiece n (p, q) = ⊥

namespace MixedHodgeStructure

attribute [instance] rationalAddCommGroup rationalModule rationalFinite

/-- The pure Hodge structure carried by the actual weight-graded quotient
`grₙ^W(M) = Wₙ / Wₙ₋₁`. -/
noncomputable def gradedPiece (M : MixedHodgeStructure) (n : ℤ) : PureHodgeStructure where
  weight := n
  rationalCarrier := M.weightFiltration.gradedPiece n
  rationalAddCommGroup := inferInstance
  rationalModule := inferInstance
  rationalFinite := M.weightFiltration.finite_gradedPiece n
  hodgePiece := M.gradedPieceHodgePiece n
  hodgePiece_free := M.gradedPieceHodgePiece_free n
  hodgePiece_finite := M.gradedPieceHodgePiece_finite n
  hodgeFiltration := M.gradedPieceHodgeFiltration n
  oppositeFiltration := M.gradedPieceOppositeFiltration n
  piece_le_filtration := by
    intro p r s hpr
    exact M.gradedPiece_piece_le_filtration hpr
  piece_le_oppositeFiltration := by
    intro q r s hqs
    exact M.gradedPiece_piece_le_oppositeFiltration hqs
  filtration_inf_eq := by
    intro p q hpq
    exact M.gradedPiece_filtration_inf_eq hpq
  weight_zero := by
    intro p q hpq
    exact M.gradedPiece_weight_zero hpq

/-- The scalar extension of a rational linear map between mixed Hodge
structures. -/
noncomputable def complexificationMap (M N : MixedHodgeStructure)
    (f : M.rationalCarrier →ₗ[ℚ] N.rationalCarrier) :
    Complexification M.rationalCarrier →ₗ[ℂ] Complexification N.rationalCarrier :=
  TensorProduct.AlgebraTensorModule.lTensor ℂ ℂ f

@[simp]
theorem complexificationMap_tmul (M N : MixedHodgeStructure)
    (f : M.rationalCarrier →ₗ[ℚ] N.rationalCarrier)
    (z : ℂ) (x : M.rationalCarrier) :
    M.complexificationMap N f (TensorProduct.mk ℚ ℂ M.rationalCarrier z x) =
      TensorProduct.mk ℚ ℂ N.rationalCarrier z (f x) :=
  TensorProduct.AlgebraTensorModule.lTensor_tmul f z x

theorem complexificationMap_comp (M N P : MixedHodgeStructure)
    (f : M.rationalCarrier →ₗ[ℚ] N.rationalCarrier)
    (g : N.rationalCarrier →ₗ[ℚ] P.rationalCarrier) :
    M.complexificationMap P (g.comp f) =
      (N.complexificationMap P g).comp (M.complexificationMap N f) := by
  ext z
  simp [complexificationMap]

@[simp]
theorem complexificationMap_id (M : MixedHodgeStructure) :
    M.complexificationMap M LinearMap.id = LinearMap.id := by
  ext z
  simp [complexificationMap]

/-- A morphism of mixed Hodge structures preserves the rational carrier, the
weight filtration, the complex Hodge filtration, and the supplied pure graded
pieces. -/
structure Hom (M N : MixedHodgeStructure) where
  linear : M.rationalCarrier →ₗ[ℚ] N.rationalCarrier
  map_weightFiltration :
    ∀ n, (M.weightFiltration.step n).map linear ≤ N.weightFiltration.step n
  map_hodgeFiltration :
    ∀ p, (M.hodgeFiltration.step p).map (M.complexificationMap N linear) ≤
      N.hodgeFiltration.step p
  map_gradedPiece : ∀ n, PureHodgeStructure.Hom (M.gradedPiece n) (N.gradedPiece n)

namespace Hom

instance (M N : MixedHodgeStructure) : CoeFun (Hom M N)
    (fun _ => M.rationalCarrier → N.rationalCarrier) where
  coe f := f.linear

@[ext]
theorem ext {M N : MixedHodgeStructure} {f g : Hom M N}
    (h : f.linear = g.linear)
    (hgraded : ∀ n, f.map_gradedPiece n = g.map_gradedPiece n) : f = g := by
  cases f
  cases g
  cases h
  simp at hgraded
  cases funext hgraded
  rfl

theorem maps_weightFiltration {M N : MixedHodgeStructure} (f : Hom M N) (n : ℤ)
    {x : M.rationalCarrier} (hx : x ∈ M.weightFiltration.step n) :
    f.linear x ∈ N.weightFiltration.step n := by
  exact f.map_weightFiltration n ⟨x, hx, rfl⟩

theorem maps_hodgeFiltration {M N : MixedHodgeStructure} (f : Hom M N) (p : ℤ)
    {x : Complexification M.rationalCarrier} (hx : x ∈ M.hodgeFiltration.step p) :
    M.complexificationMap N f.linear x ∈ N.hodgeFiltration.step p := by
  exact f.map_hodgeFiltration p ⟨x, hx, rfl⟩

def id (M : MixedHodgeStructure) : Hom M M where
  linear := LinearMap.id
  map_weightFiltration n := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  map_hodgeFiltration p := by
    rintro _ ⟨x, hx, rfl⟩
    rw [complexificationMap_id]
    exact hx
  map_gradedPiece n := PureHodgeStructure.Hom.id (M.gradedPiece n)

def comp {M N P : MixedHodgeStructure} (f : Hom M N) (g : Hom N P) : Hom M P where
  linear := g.linear.comp f.linear
  map_weightFiltration n := by
    rintro _ ⟨x, hx, rfl⟩
    exact g.maps_weightFiltration n (f.maps_weightFiltration n hx)
  map_hodgeFiltration p := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' := f.maps_hodgeFiltration p hx
    rw [complexificationMap_comp]
    exact g.maps_hodgeFiltration p hx'
  map_gradedPiece n := PureHodgeStructure.Hom.comp (f.map_gradedPiece n) (g.map_gradedPiece n)

@[simp]
theorem id_apply (M : MixedHodgeStructure) (x : M.rationalCarrier) :
    id M x = x := rfl

@[simp]
theorem comp_apply {M N P : MixedHodgeStructure} (f : Hom M N) (g : Hom N P)
    (x : M.rationalCarrier) :
    comp f g x = g.linear (f.linear x) := rfl

/-- The zero morphism of mixed Hodge structures. -/
noncomputable def zeroHom (M N : MixedHodgeStructure) : Hom M N where
  linear := 0
  map_weightFiltration n := by
    rintro _ ⟨x, hx, rfl⟩
    exact zero_mem _
  map_hodgeFiltration p := by
    rintro _ ⟨x, hx, rfl⟩
    simp [complexificationMap]
  map_gradedPiece n := PureHodgeStructure.Hom.zeroHom (M.gradedPiece n) (N.gradedPiece n) rfl

@[simp]
theorem zeroHom_apply (M N : MixedHodgeStructure) (x : M.rationalCarrier) :
    (zeroHom M N).linear x = 0 := rfl

end Hom

theorem weightFiltration_monotone (M : MixedHodgeStructure)
    ⦃m n : ℤ⦄ (hmn : m ≤ n) :
    M.weightFiltration.step m ≤ M.weightFiltration.step n :=
  M.weightFiltration.monotone hmn

theorem hodgeFiltration_antitone (M : MixedHodgeStructure)
    ⦃p q : ℤ⦄ (hpq : p ≤ q) :
    M.hodgeFiltration.step q ≤ M.hodgeFiltration.step p :=
  M.hodgeFiltration.antitone hpq

theorem gradedPiece_is_pure_of_weight (M : MixedHodgeStructure) (n : ℤ) :
    (M.gradedPiece n).weight = n :=
  rfl

@[simp]
theorem gradedPiece_hodgeNumber_eq_zero_of_ne (M : MixedHodgeStructure)
    {n p q : ℤ} (hpq : p + q ≠ n) :
    (M.gradedPiece n).hodgeNumber p q = 0 := by
  have hpq' : p + q ≠ (M.gradedPiece n).weight := by
    rw [M.gradedPiece_is_pure_of_weight n]
    exact hpq
  exact
    PureHodgeStructure.hodgeNumber_eq_zero_of_weight_ne
      (M.gradedPiece n) hpq'

/-- The pure structure on the `n`th graded piece of a product mixed Hodge
structure, transported along the canonical product equivalence for associated
graded pieces. -/
noncomputable def productGradedPiece (M N : MixedHodgeStructure) (n : ℤ) :
    PureHodgeStructure :=
  PureHodgeStructure.ofLinearEquiv
    (V := (M.weightFiltration.product N.weightFiltration).gradedPiece n)
    (PureHodgeStructure.product (M.gradedPiece n) (N.gradedPiece n) rfl)
    (M.weightFiltration.gradedPieceProductEquiv N.weightFiltration n)

/-- Componentwise product of mixed Hodge structures. -/
noncomputable def product (M N : MixedHodgeStructure) : MixedHodgeStructure where
  rationalCarrier := M.rationalCarrier × N.rationalCarrier
  rationalAddCommGroup := inferInstance
  rationalModule := inferInstance
  rationalFinite := by
    letI := M.rationalFinite
    letI := N.rationalFinite
    infer_instance
  weightFiltration := M.weightFiltration.product N.weightFiltration
  hodgeFiltration :=
    { step := fun p =>
        submoduleProd ℂ (Complexification M.rationalCarrier)
          (M.hodgeFiltration.step p) (N.hodgeFiltration.step p) |>.comap
            (Complexification.productEquiv M.rationalCarrier N.rationalCarrier).toLinearMap
      antitone' := by
        intro p q hpq x hx
        exact ⟨M.hodgeFiltration.antitone hpq hx.1, N.hodgeFiltration.antitone hpq hx.2⟩ }
  gradedPieceHodgePiece := fun n pq => (productGradedPiece M N n).hodgePiece pq
  gradedPieceHodgePiece_free := by
    intro n pq
    exact (productGradedPiece M N n).hodgePiece_free pq
  gradedPieceHodgePiece_finite := by
    intro n pq
    exact (productGradedPiece M N n).hodgePiece_finite pq
  gradedPieceHodgeFiltration := fun n => (productGradedPiece M N n).hodgeFiltration
  gradedPieceOppositeFiltration := fun n => (productGradedPiece M N n).oppositeFiltration
  gradedPiece_piece_le_filtration := by
    intro n p r s hpr
    exact (productGradedPiece M N n).piece_le_filtration hpr
  gradedPiece_piece_le_oppositeFiltration := by
    intro n q r s hqs
    exact (productGradedPiece M N n).piece_le_oppositeFiltration hqs
  gradedPiece_filtration_inf_eq := by
    intro n p q hpq
    exact (productGradedPiece M N n).filtration_inf_eq hpq
  gradedPiece_weight_zero := by
    intro n p q hpq
    exact (productGradedPiece M N n).weight_zero hpq

@[simp]
theorem complexificationMap_fst_product (M N : MixedHodgeStructure)
    (x : Complexification (M.rationalCarrier × N.rationalCarrier)) :
    (M.product N).complexificationMap M
        (LinearMap.fst ℚ M.rationalCarrier N.rationalCarrier) x =
      (Complexification.productEquiv M.rationalCarrier N.rationalCarrier x).1 := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro z vw
    rcases vw with ⟨v, w⟩
    change TensorProduct.mk ℚ ℂ M.rationalCarrier z v =
      ((Complexification.productEquiv M.rationalCarrier N.rationalCarrier)
        (TensorProduct.mk ℚ ℂ (M.rationalCarrier × N.rationalCarrier) z (v, w))).1
    rw [Complexification.productEquiv_tmul_fst]
  · intro x y hx hy
    simp [LinearMap.map_add, hx, hy]

@[simp]
theorem complexificationMap_snd_product (M N : MixedHodgeStructure)
    (x : Complexification (M.rationalCarrier × N.rationalCarrier)) :
    (M.product N).complexificationMap N
        (LinearMap.snd ℚ M.rationalCarrier N.rationalCarrier) x =
      (Complexification.productEquiv M.rationalCarrier N.rationalCarrier x).2 := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro z vw
    rcases vw with ⟨v, w⟩
    change TensorProduct.mk ℚ ℂ N.rationalCarrier z w =
      ((Complexification.productEquiv M.rationalCarrier N.rationalCarrier)
        (TensorProduct.mk ℚ ℂ (M.rationalCarrier × N.rationalCarrier) z (v, w))).2
    rw [Complexification.productEquiv_tmul_snd]
  · intro x y hx hy
    simp [LinearMap.map_add, hx, hy]

@[simp]
theorem complexificationMap_prod {M N P : MixedHodgeStructure}
    (f : M.rationalCarrier →ₗ[ℚ] N.rationalCarrier)
    (g : M.rationalCarrier →ₗ[ℚ] P.rationalCarrier)
    (x : Complexification M.rationalCarrier) :
    Complexification.productEquiv N.rationalCarrier P.rationalCarrier
      (M.complexificationMap (N.product P) (LinearMap.prod f g) x) =
        (M.complexificationMap N f x, M.complexificationMap P g x) := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro z v
    change Complexification.productEquiv N.rationalCarrier P.rationalCarrier
        (TensorProduct.mk ℚ ℂ (N.rationalCarrier × P.rationalCarrier) z (f v, g v)) =
      (TensorProduct.mk ℚ ℂ N.rationalCarrier z (f v),
        TensorProduct.mk ℚ ℂ P.rationalCarrier z (g v))
    rw [Complexification.productEquiv_tmul]
  · intro x y hx hy
    simp [LinearMap.map_add, hx, hy]

/-- Projection from a product mixed Hodge structure to the left factor. -/
noncomputable def fstHom (M N : MixedHodgeStructure) : Hom (M.product N) M where
  linear := LinearMap.fst ℚ M.rationalCarrier N.rationalCarrier
  map_weightFiltration n := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx.1
  map_hodgeFiltration p := by
    rintro _ ⟨x, hx, rfl⟩
    rw [complexificationMap_fst_product]
    exact hx.1
  map_gradedPiece n :=
    PureHodgeStructure.Hom.comp
      (PureHodgeStructure.Hom.ofLinearEquivHom
        (PureHodgeStructure.product (M.gradedPiece n) (N.gradedPiece n) rfl)
        (M.weightFiltration.gradedPieceProductEquiv N.weightFiltration n))
      (PureHodgeStructure.Hom.fstHom (M.gradedPiece n) (N.gradedPiece n) rfl)

/-- Projection from a product mixed Hodge structure to the right factor. -/
noncomputable def sndHom (M N : MixedHodgeStructure) : Hom (M.product N) N where
  linear := LinearMap.snd ℚ M.rationalCarrier N.rationalCarrier
  map_weightFiltration n := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  map_hodgeFiltration p := by
    rintro _ ⟨x, hx, rfl⟩
    rw [complexificationMap_snd_product]
    exact hx.2
  map_gradedPiece n :=
    PureHodgeStructure.Hom.comp
      (PureHodgeStructure.Hom.ofLinearEquivHom
        (PureHodgeStructure.product (M.gradedPiece n) (N.gradedPiece n) rfl)
        (M.weightFiltration.gradedPieceProductEquiv N.weightFiltration n))
      (PureHodgeStructure.Hom.sndHom (M.gradedPiece n) (N.gradedPiece n) rfl)

/-- Pair two mixed Hodge morphisms with common source into a product target. -/
noncomputable def pairHom {M N P : MixedHodgeStructure}
    (f : Hom M N) (g : Hom M P) : Hom M (N.product P) where
  linear := LinearMap.prod f.linear g.linear
  map_weightFiltration n := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨f.maps_weightFiltration n hx, g.maps_weightFiltration n hx⟩
  map_hodgeFiltration p := by
    rintro _ ⟨x, hx, rfl⟩
    change Complexification.productEquiv N.rationalCarrier P.rationalCarrier
      (M.complexificationMap (N.product P) (LinearMap.prod f.linear g.linear) x) ∈
        submoduleProd ℂ (Complexification N.rationalCarrier)
          (N.hodgeFiltration.step p) (P.hodgeFiltration.step p)
    rw [complexificationMap_prod]
    exact (mem_submoduleProd (K := ℂ) (V := Complexification N.rationalCarrier)
      (x := (M.complexificationMap N f.linear x, M.complexificationMap P g.linear x))).2
        ⟨f.maps_hodgeFiltration p hx, g.maps_hodgeFiltration p hx⟩
  map_gradedPiece n :=
    PureHodgeStructure.Hom.comp
      (PureHodgeStructure.Hom.pairHom (f.map_gradedPiece n) (g.map_gradedPiece n) rfl)
      (PureHodgeStructure.Hom.toOfLinearEquivHom
        (PureHodgeStructure.product (N.gradedPiece n) (P.gradedPiece n) rfl)
        (N.weightFiltration.gradedPieceProductEquiv P.weightFiltration n))

/-- Left inclusion into a mixed product. -/
noncomputable def inlHom (M N : MixedHodgeStructure) : Hom M (M.product N) :=
  pairHom (Hom.id M) (Hom.zeroHom M N)

/-- Right inclusion into a mixed product. -/
noncomputable def inrHom (M N : MixedHodgeStructure) : Hom N (M.product N) :=
  pairHom (Hom.zeroHom N M) (Hom.id N)

@[simp]
theorem fstHom_apply (M N : MixedHodgeStructure) (x : M.rationalCarrier × N.rationalCarrier) :
    (fstHom M N).linear x = x.1 := by
  rfl

@[simp]
theorem sndHom_apply (M N : MixedHodgeStructure) (x : M.rationalCarrier × N.rationalCarrier) :
    (sndHom M N).linear x = x.2 := by
  rfl

@[simp]
theorem pairHom_apply {M N P : MixedHodgeStructure}
    (f : Hom M N) (g : Hom M P) (x : M.rationalCarrier) :
    (pairHom f g).linear x = (f.linear x, g.linear x) := rfl

@[simp]
theorem inlHom_apply (M N : MixedHodgeStructure) (x : M.rationalCarrier) :
    (inlHom M N).linear x = (x, 0) := by
  simp [inlHom, pairHom_apply]

@[simp]
theorem inrHom_apply (M N : MixedHodgeStructure) (x : N.rationalCarrier) :
    (inrHom M N).linear x = (0, x) := by
  simp [inrHom, pairHom_apply]

@[simp]
theorem fst_comp_inl (M N : MixedHodgeStructure) :
    Hom.comp (inlHom M N) (fstHom M N) = Hom.id M := by
  apply Hom.ext
  · rfl
  · intro n
    apply PureHodgeStructure.Hom.ext
    ext x
    let e := M.weightFiltration.gradedPieceProductEquiv N.weightFiltration n
    change (e (e.symm (x, 0))).1 = x
    exact congrArg Prod.fst (Equiv.apply_symm_apply e (x, 0))

@[simp]
theorem snd_comp_inl (M N : MixedHodgeStructure) :
    Hom.comp (inlHom M N) (sndHom M N) = Hom.zeroHom M N := by
  apply Hom.ext
  · rfl
  · intro n
    apply PureHodgeStructure.Hom.ext
    ext x
    let e := M.weightFiltration.gradedPieceProductEquiv N.weightFiltration n
    change (e (e.symm (x, 0))).2 = 0
    exact congrArg Prod.snd (Equiv.apply_symm_apply e (x, 0))

@[simp]
theorem fst_comp_inr (M N : MixedHodgeStructure) :
    Hom.comp (inrHom M N) (fstHom M N) = Hom.zeroHom N M := by
  apply Hom.ext
  · rfl
  · intro n
    apply PureHodgeStructure.Hom.ext
    ext x
    let e := M.weightFiltration.gradedPieceProductEquiv N.weightFiltration n
    change (e (e.symm (0, x))).1 = 0
    exact congrArg Prod.fst (Equiv.apply_symm_apply e (0, x))

@[simp]
theorem snd_comp_inr (M N : MixedHodgeStructure) :
    Hom.comp (inrHom M N) (sndHom M N) = Hom.id N := by
  apply Hom.ext
  · rfl
  · intro n
    apply PureHodgeStructure.Hom.ext
    ext x
    let e := M.weightFiltration.gradedPieceProductEquiv N.weightFiltration n
    change (e (e.symm (0, x))).2 = x
    exact congrArg Prod.snd (Equiv.apply_symm_apply e (0, x))

theorem pairHom_eta {X A B : MixedHodgeStructure} (f : Hom X (A.product B)) :
    pairHom (Hom.comp f (fstHom A B)) (Hom.comp f (sndHom A B)) = f := by
  apply Hom.ext
  · ext x
    simp [pairHom_apply, Hom.comp_apply, fstHom_apply, sndHom_apply]
  · intro n
    apply PureHodgeStructure.Hom.ext
    ext x
    let e := A.weightFiltration.gradedPieceProductEquiv B.weightFiltration n
    change e.symm (e ((f.map_gradedPiece n).linear x)) = (f.map_gradedPiece n).linear x
    exact Equiv.symm_apply_apply e ((f.map_gradedPiece n).linear x)

theorem Hom.ext_product {X A B : MixedHodgeStructure}
    (f g : Hom X (A.product B))
    (h₁ : Hom.comp f (fstHom A B) = Hom.comp g (fstHom A B))
    (h₂ : Hom.comp f (sndHom A B) = Hom.comp g (sndHom A B)) :
    f = g := by
  apply Hom.ext
  · ext x
    have hfst := congrArg (fun h : Hom X A => h.linear x) h₁
    have hsnd := congrArg (fun h : Hom X B => h.linear x) h₂
    rw [Hom.comp_apply, fstHom_apply, sndHom_apply] at hfst hsnd
    exact Prod.ext hfst hsnd
  · intro n
    apply PureHodgeStructure.Hom.ext
    ext x
    have hfst := congrArg (fun h : PureHodgeStructure.Hom (X.gradedPiece n) (A.gradedPiece n) => h.linear x) (congrArg (fun h => h.map_gradedPiece n) h₁)
    have hsnd := congrArg (fun h : PureHodgeStructure.Hom (X.gradedPiece n) (B.gradedPiece n) => h.linear x) (congrArg (fun h => h.map_gradedPiece n) h₂)
    let e := A.weightFiltration.gradedPieceProductEquiv B.weightFiltration n
    have hfst' : (e ((f.map_gradedPiece n).linear x)).1 = (e ((g.map_gradedPiece n).linear x)).1 := by
      rw [Hom.comp, fstHom, sndHom, pairHom, Hom.id, Hom.zeroHom, e] at hfst
      exact hfst
    have hsnd' : (e ((f.map_gradedPiece n).linear x)).2 = (e ((g.map_gradedPiece n).linear x)).2 := by
      rw [Hom.comp, fstHom, sndHom, pairHom, Hom.id, Hom.zeroHom, e] at hsnd
      exact hsnd
    exact e.injective (Prod.ext hfst' hsnd')

end MixedHodgeStructure

end Hodge
end Boundary

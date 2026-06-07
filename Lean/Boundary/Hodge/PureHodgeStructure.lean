import Boundary.Hodge.FilteredVectorSpace
import Boundary.Hodge.GradedVectorSpace
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Module.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Module
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Pure Hodge structures

A pure rational Hodge structure is bundled as a finite-dimensional rational
vector space together with genuine `(p,q)` subspaces in its complexification
`ℂ ⊗[ℚ] V` and a decreasing Hodge filtration related to those pieces.

This is intentionally the linear-algebra layer only: it does not assert that
the structure has arisen from de Rham, Betti, or analytic cohomology.

The conventions are those of rational pure Hodge structures; cf. Deligne,
"Théorie de Hodge I", §2, and Voisin, *Hodge Theory and Complex Algebraic
Geometry I*, Ch. 7.
-/

namespace Boundary
namespace Hodge

/-- The scalar extension `V_ℂ = ℂ ⊗[ℚ] V_ℚ` of a rational vector space. -/
abbrev Complexification (V : Type) [AddCommGroup V] [Module ℚ V] : Type :=
  TensorProduct ℚ ℂ V

namespace Complexification

variable (V W : Type) [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

/-- Scalar extension of a rational linear equivalence. -/
noncomputable def mapLinearEquiv (e : V ≃ₗ[ℚ] W) :
    Complexification V ≃ₗ[ℂ] Complexification W where
  toFun := TensorProduct.AlgebraTensorModule.lTensor ℂ ℂ e.toLinearMap
  invFun := TensorProduct.AlgebraTensorModule.lTensor ℂ ℂ e.symm.toLinearMap
  left_inv := by
    intro x
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · change
        (TensorProduct.AlgebraTensorModule.lTensor ℂ ℂ e.symm.toLinearMap)
            ((TensorProduct.AlgebraTensorModule.lTensor ℂ ℂ e.toLinearMap) 0) = 0
      rw [map_zero, map_zero]
    · intro z v
      change
        (TensorProduct.AlgebraTensorModule.lTensor ℂ ℂ e.symm.toLinearMap)
            ((TensorProduct.AlgebraTensorModule.lTensor ℂ ℂ e.toLinearMap)
              (TensorProduct.mk ℚ ℂ V z v)) =
          TensorProduct.mk ℚ ℂ V z v
      calc
        (TensorProduct.AlgebraTensorModule.lTensor ℂ ℂ e.symm.toLinearMap)
            ((TensorProduct.AlgebraTensorModule.lTensor ℂ ℂ e.toLinearMap)
              (TensorProduct.mk ℚ ℂ V z v))
            =
          (TensorProduct.AlgebraTensorModule.lTensor ℂ ℂ e.symm.toLinearMap)
            (TensorProduct.mk ℚ ℂ W z (e v)) := by
              rfl
        _ = TensorProduct.mk ℚ ℂ V z (e.symm (e v)) := by
              rfl
        _ = TensorProduct.mk ℚ ℂ V z v := by
              rw [e.symm_apply_apply]
    · intro x y hx hy
      change
        (TensorProduct.AlgebraTensorModule.lTensor ℂ ℂ e.symm.toLinearMap)
            ((TensorProduct.AlgebraTensorModule.lTensor ℂ ℂ e.toLinearMap) (x + y)) =
          x + y
      rw [map_add, map_add]
      exact congrArg₂ HAdd.hAdd hx hy
  right_inv := by
    intro x
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · change
        (TensorProduct.AlgebraTensorModule.lTensor ℂ ℂ e.toLinearMap)
            ((TensorProduct.AlgebraTensorModule.lTensor ℂ ℂ e.symm.toLinearMap) 0) = 0
      rw [map_zero, map_zero]
    · intro z w
      change
        (TensorProduct.AlgebraTensorModule.lTensor ℂ ℂ e.toLinearMap)
            ((TensorProduct.AlgebraTensorModule.lTensor ℂ ℂ e.symm.toLinearMap)
              (TensorProduct.mk ℚ ℂ W z w)) =
          TensorProduct.mk ℚ ℂ W z w
      calc
        (TensorProduct.AlgebraTensorModule.lTensor ℂ ℂ e.toLinearMap)
            ((TensorProduct.AlgebraTensorModule.lTensor ℂ ℂ e.symm.toLinearMap)
              (TensorProduct.mk ℚ ℂ W z w))
            =
          (TensorProduct.AlgebraTensorModule.lTensor ℂ ℂ e.toLinearMap)
            (TensorProduct.mk ℚ ℂ V z (e.symm w)) := by
              rfl
        _ = TensorProduct.mk ℚ ℂ W z (e (e.symm w)) := by
              rfl
        _ = TensorProduct.mk ℚ ℂ W z w := by
              rw [e.apply_symm_apply]
    · intro x y hx hy
      change
        (TensorProduct.AlgebraTensorModule.lTensor ℂ ℂ e.toLinearMap)
            ((TensorProduct.AlgebraTensorModule.lTensor ℂ ℂ e.symm.toLinearMap) (x + y)) =
          x + y
      rw [map_add, map_add]
      exact congrArg₂ HAdd.hAdd hx hy
  map_add' := by
    intro x y
    exact (TensorProduct.AlgebraTensorModule.lTensor ℂ ℂ e.toLinearMap).map_add x y
  map_smul' := by
    intro c x
    exact (TensorProduct.AlgebraTensorModule.lTensor ℂ ℂ e.toLinearMap).map_smul c x

@[simp]
theorem mapLinearEquiv_tmul (e : V ≃ₗ[ℚ] W) (z : ℂ) (v : V) :
    mapLinearEquiv V W e (TensorProduct.mk ℚ ℂ V z v) =
      TensorProduct.mk ℚ ℂ W z (e v) :=
  TensorProduct.AlgebraTensorModule.lTensor_tmul e.toLinearMap z v

/-- Scalar extension from `ℚ` to `ℂ` commutes with binary products. -/
noncomputable def productEquiv :
    Complexification (V × W) ≃ₗ[ℂ] Complexification V × Complexification W where
  toFun := TensorProduct.prodRight ℚ ℂ V W
  invFun := (TensorProduct.prodRight ℚ ℂ V W).symm
  map_add' := (TensorProduct.prodRight ℚ ℂ V W).map_add
  map_smul' := by
    intro c x
    change (TensorProduct.prodRight ℚ ℂ V W) (c • x) =
      c • (TensorProduct.prodRight ℚ ℂ V W) x
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · rw [smul_zero, map_zero, smul_zero]
    · intro z vw
      rcases vw with ⟨v, w⟩
      rw [TensorProduct.smul_tmul']
      rw [TensorProduct.prodRight_tmul]
      rw [TensorProduct.prodRight_tmul]
      rw [Prod.smul_mk, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
    · intro x y hx hy
      rw [smul_add, (TensorProduct.prodRight ℚ ℂ V W).map_add, hx, hy,
        (TensorProduct.prodRight ℚ ℂ V W).map_add, smul_add]
  left_inv := (TensorProduct.prodRight ℚ ℂ V W).left_inv
  right_inv := (TensorProduct.prodRight ℚ ℂ V W).right_inv

@[simp]
theorem productEquiv_tmul (z : ℂ) (v : V) (w : W) :
    productEquiv V W (TensorProduct.mk ℚ ℂ (V × W) z (v, w)) =
      (TensorProduct.mk ℚ ℂ V z v, TensorProduct.mk ℚ ℂ W z w) := by
  change (TensorProduct.prodRight ℚ ℂ V W)
      (TensorProduct.mk ℚ ℂ (V × W) z (v, w)) =
    (TensorProduct.mk ℚ ℂ V z v, TensorProduct.mk ℚ ℂ W z w)
  exact TensorProduct.prodRight_tmul ℚ ℂ V W z v w

@[simp]
theorem productEquiv_tmul_fst (z : ℂ) (v : V) (w : W) :
    (productEquiv V W (TensorProduct.mk ℚ ℂ (V × W) z (v, w))).1 =
      TensorProduct.mk ℚ ℂ V z v := by
  rw [productEquiv_tmul]

@[simp]
theorem productEquiv_tmul_snd (z : ℂ) (v : V) (w : W) :
    (productEquiv V W (TensorProduct.mk ℚ ℂ (V × W) z (v, w))).2 =
      TensorProduct.mk ℚ ℂ W z w := by
  rw [productEquiv_tmul]

@[simp]
theorem productEquiv_symm_mk_tmul (z : ℂ) (v : V) (w : W) :
    (productEquiv V W).symm
      (TensorProduct.mk ℚ ℂ V z v, TensorProduct.mk ℚ ℂ W z w) =
      TensorProduct.mk ℚ ℂ (V × W) z (v, w) := by
  exact (LinearEquiv.symm_apply_eq (productEquiv V W)).2
    (productEquiv_tmul V W z v w).symm

end Complexification

namespace Submodule

variable {K : Type} [Field K]
variable {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- Pulling a submodule back along a linear equivalence gives an equivalent subtype module. -/
noncomputable def comapLinearEquiv (e : V ≃ₗ[K] W) (S : Submodule K W) :
    S.comap e.toLinearMap ≃ₗ[K] S where
  toFun := fun x => ⟨e x.1, x.2⟩
  invFun := fun x => ⟨e.symm x.1, by
    change e (e.symm x.1) ∈ S
    rw [e.apply_symm_apply]
    exact x.2⟩
  map_add' := by
    intro x y
    ext
    exact map_add e x.1 y.1
  map_smul' := by
    intro c x
    ext
    exact map_smul e c x.1
  left_inv := by
    intro x
    ext
    exact e.symm_apply_apply x.1
  right_inv := by
    intro x
    ext
    exact e.apply_symm_apply x.1

theorem free_comap_linearEquiv (e : V ≃ₗ[K] W) (S : Submodule K W)
    [Module.Free K S] :
    Module.Free K (S.comap e.toLinearMap) := by
  exact Module.Free.of_equiv (comapLinearEquiv e S).symm

theorem finite_comap_linearEquiv (e : V ≃ₗ[K] W) (S : Submodule K W)
    [Module.Finite K S] :
    Module.Finite K (S.comap e.toLinearMap) := by
  exact Module.Finite.equiv (comapLinearEquiv e S).symm

end Submodule

/-- A pure rational Hodge structure at the linear-algebra level. -/
structure PureHodgeStructure where
  weight : ℤ
  rationalCarrier : Type
  rationalAddCommGroup : AddCommGroup rationalCarrier
  rationalModule : Module ℚ rationalCarrier
  rationalFinite : Module.Finite ℚ rationalCarrier
  hodgePiece : ℤ × ℤ → Submodule ℂ (Complexification rationalCarrier)
  hodgePiece_free : ∀ pq, Module.Free ℂ (hodgePiece pq)
  hodgePiece_finite : ∀ pq, Module.Finite ℂ (hodgePiece pq)
  hodgeFiltration : DecreasingFiltration ℂ (Complexification rationalCarrier)
  oppositeFiltration : DecreasingFiltration ℂ (Complexification rationalCarrier)
  piece_le_filtration :
    ∀ ⦃p r s : ℤ⦄, p ≤ r → hodgePiece (r, s) ≤ hodgeFiltration.step p
  piece_le_oppositeFiltration :
    ∀ ⦃q r s : ℤ⦄, q ≤ s → hodgePiece (r, s) ≤ oppositeFiltration.step q
  filtration_inf_eq :
    ∀ ⦃p q : ℤ⦄, p + q = weight →
      hodgeFiltration.step p ⊓ oppositeFiltration.step q = hodgePiece (p, q)
  weight_zero :
    ∀ ⦃p q : ℤ⦄, p + q ≠ weight → hodgePiece (p, q) = ⊥

namespace PureHodgeStructure

attribute [instance] rationalAddCommGroup rationalModule rationalFinite
attribute [instance] hodgePiece_free hodgePiece_finite

/-- The Hodge number `h^{p,q}` of a pure Hodge structure. -/
noncomputable def hodgeNumber (H : PureHodgeStructure) (p q : ℤ) : ℕ :=
  Module.finrank ℂ (H.hodgePiece (p, q))

/-- The bigraded rank profile of a pure Hodge structure. -/
noncomputable def rankProfile (H : PureHodgeStructure) : BigradedRankProfile :=
  fun pq => H.hodgeNumber pq.1 pq.2

theorem hodgePiece_le_filtration (H : PureHodgeStructure)
    ⦃p r s : ℤ⦄ (hpr : p ≤ r) :
    H.hodgePiece (r, s) ≤ H.hodgeFiltration.step p :=
  H.piece_le_filtration hpr

theorem hodgeFiltration_antitone (H : PureHodgeStructure)
    ⦃p q : ℤ⦄ (hpq : p ≤ q) :
    H.hodgeFiltration.step q ≤ H.hodgeFiltration.step p :=
  H.hodgeFiltration.antitone hpq

theorem oppositeFiltration_antitone (H : PureHodgeStructure)
    ⦃p q : ℤ⦄ (hpq : p ≤ q) :
    H.oppositeFiltration.step q ≤ H.oppositeFiltration.step p :=
  H.oppositeFiltration.antitone hpq

theorem hodgePiece_le_oppositeFiltration (H : PureHodgeStructure)
    ⦃q r s : ℤ⦄ (hqs : q ≤ s) :
    H.hodgePiece (r, s) ≤ H.oppositeFiltration.step q :=
  H.piece_le_oppositeFiltration hqs

theorem hodgeFiltration_inf_eq_hodgePiece (H : PureHodgeStructure)
    ⦃p q : ℤ⦄ (hpq : p + q = H.weight) :
    H.hodgeFiltration.step p ⊓ H.oppositeFiltration.step q = H.hodgePiece (p, q) :=
  H.filtration_inf_eq hpq

/-- Transport a pure rational Hodge structure across a rational linear
equivalence by pulling back its complex Hodge data. -/
noncomputable def ofLinearEquiv (H : PureHodgeStructure)
    {V : Type} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (e : V ≃ₗ[ℚ] H.rationalCarrier) : PureHodgeStructure where
  weight := H.weight
  rationalCarrier := V
  rationalAddCommGroup := inferInstance
  rationalModule := inferInstance
  rationalFinite := inferInstance
  hodgePiece := fun pq =>
    (H.hodgePiece pq).comap (Complexification.mapLinearEquiv V H.rationalCarrier e).toLinearMap
  hodgePiece_free := by
    intro pq
    exact Submodule.free_comap_linearEquiv
      (Complexification.mapLinearEquiv V H.rationalCarrier e) (H.hodgePiece pq)
  hodgePiece_finite := by
    intro pq
    exact Submodule.finite_comap_linearEquiv
      (Complexification.mapLinearEquiv V H.rationalCarrier e) (H.hodgePiece pq)
  hodgeFiltration :=
    { step := fun p =>
        (H.hodgeFiltration.step p).comap
          (Complexification.mapLinearEquiv V H.rationalCarrier e).toLinearMap
      antitone' := by
        intro p q hpq
        exact Submodule.comap_mono (H.hodgeFiltration.antitone hpq) }
  oppositeFiltration :=
    { step := fun p =>
        (H.oppositeFiltration.step p).comap
          (Complexification.mapLinearEquiv V H.rationalCarrier e).toLinearMap
      antitone' := by
        intro p q hpq
        exact Submodule.comap_mono (H.oppositeFiltration.antitone hpq) }
  piece_le_filtration := by
    intro p r s hpr x hx
    exact H.piece_le_filtration hpr hx
  piece_le_oppositeFiltration := by
    intro q r s hqs x hx
    exact H.piece_le_oppositeFiltration hqs hx
  filtration_inf_eq := by
    intro p q hpq
    ext x
    change
      Complexification.mapLinearEquiv V H.rationalCarrier e x ∈
          H.hodgeFiltration.step p ⊓ H.oppositeFiltration.step q ↔
        Complexification.mapLinearEquiv V H.rationalCarrier e x ∈ H.hodgePiece (p, q)
    rw [H.filtration_inf_eq hpq]
  weight_zero := by
    intro p q hpq
    ext x
    change
      Complexification.mapLinearEquiv V H.rationalCarrier e x ∈ H.hodgePiece (p, q) ↔
        x ∈ (⊥ : Submodule ℂ (Complexification V))
    rw [H.weight_zero hpq]
    constructor
    · intro hx
      rw [Submodule.mem_bot] at hx
      exact (LinearEquiv.map_eq_zero_iff
        (Complexification.mapLinearEquiv V H.rationalCarrier e)).1 hx
    · intro hx
      rw [Submodule.mem_bot] at hx
      rw [hx, map_zero]
      exact Submodule.zero_mem ⊥

theorem hodgePiece_eq_bot_of_weight_ne (H : PureHodgeStructure)
    ⦃p q : ℤ⦄ (hpq : p + q ≠ H.weight) :
    H.hodgePiece (p, q) = ⊥ :=
  H.weight_zero hpq

@[simp]
theorem hodgeNumber_eq_zero_of_weight_ne (H : PureHodgeStructure)
    ⦃p q : ℤ⦄ (hpq : p + q ≠ H.weight) :
    H.hodgeNumber p q = 0 := by
  rw [hodgeNumber, H.hodgePiece_eq_bot_of_weight_ne hpq]
  exact finrank_bot ℂ (Complexification H.rationalCarrier)

/-- Product of the Hodge pieces of two pure structures, transported through
complexification of the rational product. -/
noncomputable def productHodgePiece (H G : PureHodgeStructure) (pq : ℤ × ℤ) :
    Submodule ℂ (Complexification (H.rationalCarrier × G.rationalCarrier)) :=
  (submoduleProd ℂ (Complexification H.rationalCarrier) (H.hodgePiece pq) (G.hodgePiece pq)).comap
    (Complexification.productEquiv H.rationalCarrier G.rationalCarrier).toLinearMap

/-- Product of the Hodge filtrations of two pure structures, transported through
complexification of the rational product. -/
noncomputable def productHodgeFiltration (H G : PureHodgeStructure) :
    DecreasingFiltration ℂ (Complexification (H.rationalCarrier × G.rationalCarrier)) where
  step p :=
    (submoduleProd ℂ (Complexification H.rationalCarrier)
      (H.hodgeFiltration.step p) (G.hodgeFiltration.step p)).comap
        (Complexification.productEquiv H.rationalCarrier G.rationalCarrier).toLinearMap
  antitone' := by
    intro p q hpq x hx
    exact ⟨H.hodgeFiltration.antitone hpq hx.1, G.hodgeFiltration.antitone hpq hx.2⟩

/-- Product of the opposite filtrations of two pure structures, transported
through complexification of the rational product. -/
noncomputable def productOppositeFiltration (H G : PureHodgeStructure) :
    DecreasingFiltration ℂ (Complexification (H.rationalCarrier × G.rationalCarrier)) where
  step p :=
    (submoduleProd ℂ (Complexification H.rationalCarrier)
      (H.oppositeFiltration.step p) (G.oppositeFiltration.step p)).comap
        (Complexification.productEquiv H.rationalCarrier G.rationalCarrier).toLinearMap
  antitone' := by
    intro p q hpq x hx
    exact ⟨H.oppositeFiltration.antitone hpq hx.1, G.oppositeFiltration.antitone hpq hx.2⟩

/-- The direct product of two pure rational Hodge structures of the same weight. -/
noncomputable def product (H G : PureHodgeStructure) (hweight : H.weight = G.weight) :
    PureHodgeStructure where
  weight := H.weight
  rationalCarrier := H.rationalCarrier × G.rationalCarrier
  rationalAddCommGroup := inferInstance
  rationalModule := inferInstance
  rationalFinite := inferInstance
  hodgePiece := productHodgePiece H G
  hodgePiece_free := by
    intro pq
    dsimp [productHodgePiece]
    haveI : Module.Free ℂ
        (submoduleProd ℂ (Complexification H.rationalCarrier) (H.hodgePiece pq) (G.hodgePiece pq)) :=
      free_submoduleProd ℂ (Complexification H.rationalCarrier) (H.hodgePiece pq) (G.hodgePiece pq)
    exact Submodule.free_comap_linearEquiv
      (Complexification.productEquiv H.rationalCarrier G.rationalCarrier)
      (submoduleProd ℂ (Complexification H.rationalCarrier) (H.hodgePiece pq) (G.hodgePiece pq))
  hodgePiece_finite := by
    intro pq
    dsimp [productHodgePiece]
    haveI : Module.Finite ℂ
        (submoduleProd ℂ (Complexification H.rationalCarrier) (H.hodgePiece pq) (G.hodgePiece pq)) :=
      finite_submoduleProd ℂ (Complexification H.rationalCarrier) (H.hodgePiece pq) (G.hodgePiece pq)
    exact Submodule.finite_comap_linearEquiv
      (Complexification.productEquiv H.rationalCarrier G.rationalCarrier)
      (submoduleProd ℂ (Complexification H.rationalCarrier) (H.hodgePiece pq) (G.hodgePiece pq))
  hodgeFiltration := productHodgeFiltration H G
  oppositeFiltration := productOppositeFiltration H G
  piece_le_filtration := by
    intro p r s hpr x hx
    exact ⟨H.piece_le_filtration hpr hx.1, G.piece_le_filtration hpr hx.2⟩
  piece_le_oppositeFiltration := by
    intro q r s hqs x hx
    exact ⟨H.piece_le_oppositeFiltration hqs hx.1, G.piece_le_oppositeFiltration hqs hx.2⟩
  filtration_inf_eq := by
    intro p q hpq
    ext x
    change
      (((Complexification.productEquiv H.rationalCarrier G.rationalCarrier x).1 ∈
          H.hodgeFiltration.step p ∧
        (Complexification.productEquiv H.rationalCarrier G.rationalCarrier x).2 ∈
          G.hodgeFiltration.step p) ∧
       ((Complexification.productEquiv H.rationalCarrier G.rationalCarrier x).1 ∈
          H.oppositeFiltration.step q ∧
        (Complexification.productEquiv H.rationalCarrier G.rationalCarrier x).2 ∈
          G.oppositeFiltration.step q)) ↔
       ((Complexification.productEquiv H.rationalCarrier G.rationalCarrier x).1 ∈
          H.hodgePiece (p, q) ∧
        (Complexification.productEquiv H.rationalCarrier G.rationalCarrier x).2 ∈
          G.hodgePiece (p, q))
    constructor
    · intro hx
      have hx₁ : (Complexification.productEquiv H.rationalCarrier G.rationalCarrier x).1 ∈
          H.hodgeFiltration.step p ⊓ H.oppositeFiltration.step q := ⟨hx.1.1, hx.2.1⟩
      have hx₂ : (Complexification.productEquiv H.rationalCarrier G.rationalCarrier x).2 ∈
          G.hodgeFiltration.step p ⊓ G.oppositeFiltration.step q := ⟨hx.1.2, hx.2.2⟩
      rw [H.filtration_inf_eq hpq] at hx₁
      have hpqG : p + q = G.weight := hpq.trans hweight
      rw [G.filtration_inf_eq hpqG] at hx₂
      exact ⟨hx₁, hx₂⟩
    · intro hx
      have hx₁ : (Complexification.productEquiv H.rationalCarrier G.rationalCarrier x).1 ∈
          H.hodgeFiltration.step p ⊓ H.oppositeFiltration.step q := by
        rw [H.filtration_inf_eq hpq]
        exact hx.1
      have hx₂ : (Complexification.productEquiv H.rationalCarrier G.rationalCarrier x).2 ∈
          G.hodgeFiltration.step p ⊓ G.oppositeFiltration.step q := by
        have hpqG : p + q = G.weight := hpq.trans hweight
        rw [G.filtration_inf_eq hpqG]
        exact hx.2
      exact ⟨⟨hx₁.1, hx₂.1⟩, hx₁.2, hx₂.2⟩
  weight_zero := by
    intro p q hpq
    apply le_antisymm
    · intro x hx
      have hH : H.hodgePiece (p, q) = ⊥ := H.weight_zero hpq
      have hG : G.hodgePiece (p, q) = ⊥ := G.weight_zero (by
        intro hpqG
        exact hpq (hpqG.trans hweight.symm))
      change (Complexification.productEquiv H.rationalCarrier G.rationalCarrier x) ∈
        submoduleProd ℂ (Complexification H.rationalCarrier) (H.hodgePiece (p, q))
          (G.hodgePiece (p, q)) at hx
      rw [hH, hG] at hx
      have hx_zero :
          Complexification.productEquiv H.rationalCarrier G.rationalCarrier x = 0 := by
        ext
        · exact hx.1
        · exact hx.2
      exact (LinearEquiv.map_eq_zero_iff
        (Complexification.productEquiv H.rationalCarrier G.rationalCarrier)).1 hx_zero
    · exact bot_le

@[simp]
theorem hodgeNumber_product (H G : PureHodgeStructure) (hweight : H.weight = G.weight)
    (p q : ℤ) :
    (H.product G hweight).hodgeNumber p q = H.hodgeNumber p q + G.hodgeNumber p q := by
  rw [hodgeNumber, product]
  dsimp [productHodgePiece]
  rw [LinearEquiv.finrank_eq (Submodule.comapLinearEquiv
    (Complexification.productEquiv H.rationalCarrier G.rationalCarrier)
    (submoduleProd ℂ (Complexification H.rationalCarrier)
      (H.hodgePiece (p, q)) (G.hodgePiece (p, q))))]
  exact finrank_submoduleProd ℂ (Complexification H.rationalCarrier)
    (H.hodgePiece (p, q)) (G.hodgePiece (p, q))

@[simp]
theorem rankProfile_product (H G : PureHodgeStructure) (hweight : H.weight = G.weight) :
    (H.product G hweight).rankProfile =
      BigradedRankProfile.add H.rankProfile G.rankProfile := by
  funext pq
  rcases pq with ⟨p, q⟩
  rw [rankProfile, BigradedRankProfile.add_apply]
  exact hodgeNumber_product H G hweight p q

theorem rankProfile_ofLinearEquiv (H : PureHodgeStructure)
    {V : Type} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (e : V ≃ₗ[ℚ] H.rationalCarrier) :
    (H.ofLinearEquiv e).rankProfile = H.rankProfile := by
  funext pq
  rcases pq with ⟨p, q⟩
  rw [rankProfile, rankProfile]
  rw [hodgeNumber, hodgeNumber]
  exact LinearEquiv.finrank_eq
    (Submodule.comapLinearEquiv
      (Complexification.mapLinearEquiv V H.rationalCarrier e) (H.hodgePiece (p, q)))

end PureHodgeStructure

end Hodge
end Boundary

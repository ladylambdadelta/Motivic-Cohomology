import Boundary.Hodge.PureHodgeStructure

/-!
# Rational Hodge classes

Rational Hodge classes for a pure rational Hodge structure are rational
vectors whose scalar extension to the complexification lies in the `(p,p)`
Hodge piece.
-/

namespace Boundary
namespace Hodge

namespace PureHodgeStructure

/-- The canonical scalar-extension map `V_ℚ → V_ℚ ⊗[ℚ] ℂ`. -/
noncomputable def complexifyMap (H : PureHodgeStructure) :
    H.rationalCarrier →ₗ[ℚ] Complexification H.rationalCarrier where
  toFun x := TensorProduct.mk ℚ ℂ H.rationalCarrier 1 x
  map_add' := by
    intro x y
    exact TensorProduct.tmul_add 1 x y
  map_smul' := by
    intro q x
    simp [TensorProduct.tmul_smul]

/-- The complexification of a rational vector. -/
noncomputable def complexifyVector (H : PureHodgeStructure) (x : H.rationalCarrier) :
    Complexification H.rationalCarrier :=
  H.complexifyMap x

@[simp]
theorem complexifyVector_zero (H : PureHodgeStructure) :
    H.complexifyVector 0 = 0 :=
  H.complexifyMap.map_zero

@[simp]
theorem complexifyVector_add (H : PureHodgeStructure)
    (x y : H.rationalCarrier) :
    H.complexifyVector (x + y) = H.complexifyVector x + H.complexifyVector y :=
  H.complexifyMap.map_add x y

@[simp]
theorem complexifyVector_smul (H : PureHodgeStructure)
    (q : ℚ) (x : H.rationalCarrier) :
    H.complexifyVector (q • x) = algebraMap ℚ ℂ q • H.complexifyVector x :=
  H.complexifyMap.map_smul q x

/-- A rational Hodge class of codimension `p` in a pure structure of weight
`2*p` is a rational vector whose complexification lies in `H^{p,p}`. -/
def IsHodgeClass (H : PureHodgeStructure) (p : ℤ)
    (_hweight : H.weight = 2 * p) (x : H.rationalCarrier) : Prop :=
  H.complexifyVector x ∈ H.hodgePiece (p, p)

/-- Filtration-side formulation of a rational Hodge class: after scalar
extension, the vector lies in both opposed weight-`p` filtration steps. -/
def IsHodgeClassFiltration (H : PureHodgeStructure) (p : ℤ)
    (_hweight : H.weight = 2 * p) (x : H.rationalCarrier) : Prop :=
  H.complexifyVector x ∈ H.hodgeFiltration.step p ∧
    H.complexifyVector x ∈ H.oppositeFiltration.step p

theorem isHodgeClass_iff_filtration (H : PureHodgeStructure) (p : ℤ)
    (hweight : H.weight = 2 * p) (x : H.rationalCarrier) :
    H.IsHodgeClass p hweight x ↔ H.IsHodgeClassFiltration p hweight x := by
  constructor
  · intro hx
    exact ⟨H.piece_le_filtration le_rfl hx, H.piece_le_oppositeFiltration le_rfl hx⟩
  · intro hx
    rw [IsHodgeClass, IsHodgeClassFiltration] at *
    have hEq := H.hodgeFiltration_inf_eq_hodgePiece
      (p := p) (q := p) (by
        rw [hweight]
        rw [two_mul])
    rw [← hEq]
    exact hx

@[simp]
theorem isHodgeClass_zero (H : PureHodgeStructure) (p : ℤ)
    (hweight : H.weight = 2 * p) :
    H.IsHodgeClass p hweight 0 := by
  rw [IsHodgeClass]
  rw [H.complexifyVector_zero]
  exact zero_mem (H.hodgePiece (p, p))

theorem isHodgeClass_add (H : PureHodgeStructure) (p : ℤ)
    (hweight : H.weight = 2 * p) {x y : H.rationalCarrier}
    (hx : H.IsHodgeClass p hweight x) (hy : H.IsHodgeClass p hweight y) :
    H.IsHodgeClass p hweight (x + y) := by
  rw [IsHodgeClass]
  rw [H.complexifyVector_add]
  exact H.hodgePiece (p, p) |>.add_mem hx hy

theorem isHodgeClass_smul (H : PureHodgeStructure) (p : ℤ)
    (hweight : H.weight = 2 * p) (q : ℚ) {x : H.rationalCarrier}
    (hx : H.IsHodgeClass p hweight x) :
    H.IsHodgeClass p hweight (q • x) := by
  rw [IsHodgeClass]
  rw [H.complexifyVector_smul]
  exact H.hodgePiece (p, p) |>.smul_mem (algebraMap ℚ ℂ q) hx

/-- The rational subspace of Hodge classes in bidegree `(p,p)`. -/
noncomputable def hodgeClasses (H : PureHodgeStructure) (p : ℤ)
    (hweight : H.weight = 2 * p) : Submodule ℚ H.rationalCarrier where
  carrier := {x | H.IsHodgeClass p hweight x}
  zero_mem' := H.isHodgeClass_zero p hweight
  add_mem' := by
    intro x y hx hy
    exact H.isHodgeClass_add p hweight hx hy
  smul_mem' := by
    intro q x hx
    exact H.isHodgeClass_smul p hweight q hx

@[simp]
theorem mem_hodgeClasses (H : PureHodgeStructure) (p : ℤ)
    (hweight : H.weight = 2 * p) (x : H.rationalCarrier) :
    x ∈ H.hodgeClasses p hweight ↔ H.IsHodgeClass p hweight x :=
  Iff.rfl

@[simp]
theorem product_complexifyVector (H G : PureHodgeStructure)
    (hweight : H.weight = G.weight)
    (x : H.rationalCarrier) (y : G.rationalCarrier) :
    Complexification.productEquiv H.rationalCarrier G.rationalCarrier
        ((H.product G hweight).complexifyVector (x, y)) =
      (H.complexifyVector x, G.complexifyVector y) := by
  exact Complexification.productEquiv_tmul H.rationalCarrier G.rationalCarrier 1 x y

theorem product_isHodgeClass_left (H G : PureHodgeStructure) (p : ℤ)
    (hH : H.weight = 2 * p) (hG : G.weight = 2 * p)
    {x : H.rationalCarrier} (hx : H.IsHodgeClass p hH x) :
    (H.product G (hH.trans hG.symm)).IsHodgeClass p hH (x, 0) := by
  change Complexification.productEquiv H.rationalCarrier G.rationalCarrier
      ((H.product G (hH.trans hG.symm)).complexifyVector (x, 0)) ∈
    submoduleProd ℂ (Complexification H.rationalCarrier)
      (H.hodgePiece (p, p)) (G.hodgePiece (p, p))
  rw [product_complexifyVector]
  exact ⟨hx, by simp [IsHodgeClass]⟩

theorem product_isHodgeClass_right (H G : PureHodgeStructure) (p : ℤ)
    (hH : H.weight = 2 * p) (hG : G.weight = 2 * p)
    {y : G.rationalCarrier} (hy : G.IsHodgeClass p hG y) :
    (H.product G (hH.trans hG.symm)).IsHodgeClass p hH (0, y) := by
  change Complexification.productEquiv H.rationalCarrier G.rationalCarrier
      ((H.product G (hH.trans hG.symm)).complexifyVector (0, y)) ∈
    submoduleProd ℂ (Complexification H.rationalCarrier)
      (H.hodgePiece (p, p)) (G.hodgePiece (p, p))
  rw [product_complexifyVector]
  exact ⟨by simp [IsHodgeClass], hy⟩

theorem hodgeClasses_product_left_map (H G : PureHodgeStructure) (p : ℤ)
    (hH : H.weight = 2 * p) (hG : G.weight = 2 * p) :
    (H.hodgeClasses p hH).map
        (LinearMap.inl ℚ H.rationalCarrier G.rationalCarrier) ≤
      (H.product G (hH.trans hG.symm)).hodgeClasses p hH := by
  rintro _ ⟨x, hx, rfl⟩
  exact H.product_isHodgeClass_left G p hH hG hx

theorem hodgeClasses_product_right_map (H G : PureHodgeStructure) (p : ℤ)
    (hH : H.weight = 2 * p) (hG : G.weight = 2 * p) :
    (G.hodgeClasses p hG).map
        (LinearMap.inr ℚ H.rationalCarrier G.rationalCarrier) ≤
      (H.product G (hH.trans hG.symm)).hodgeClasses p hH := by
  rintro _ ⟨y, hy, rfl⟩
  exact H.product_isHodgeClass_right G p hH hG hy

theorem hodgeClasses_product_contains_sup (H G : PureHodgeStructure) (p : ℤ)
    (hH : H.weight = 2 * p) (hG : G.weight = 2 * p) :
    (H.hodgeClasses p hH).map
          (LinearMap.inl ℚ H.rationalCarrier G.rationalCarrier) ⊔
        (G.hodgeClasses p hG).map
          (LinearMap.inr ℚ H.rationalCarrier G.rationalCarrier) ≤
      (H.product G (hH.trans hG.symm)).hodgeClasses p hH := by
  exact sup_le (H.hodgeClasses_product_left_map G p hH hG)
    (H.hodgeClasses_product_right_map G p hH hG)

theorem hodgeClasses_product_prod_le (H G : PureHodgeStructure) (p : ℤ)
    (hH : H.weight = 2 * p) (hG : G.weight = 2 * p) :
    submoduleProd ℚ H.rationalCarrier (H.hodgeClasses p hH) (G.hodgeClasses p hG) ≤
      (H.product G (hH.trans hG.symm)).hodgeClasses p hH := by
  intro x hx
  change Complexification.productEquiv H.rationalCarrier G.rationalCarrier
      ((H.product G (hH.trans hG.symm)).complexifyVector x) ∈
    submoduleProd ℂ (Complexification H.rationalCarrier)
      (H.hodgePiece (p, p)) (G.hodgePiece (p, p))
  rcases x with ⟨x, y⟩
  rw [product_complexifyVector]
  exact ⟨hx.1, hx.2⟩

/-- Hodge classes transport across a rational linear equivalence by applying the equivalence. -/
theorem hodgeClasses_ofLinearEquiv_iff (H : PureHodgeStructure)
    {V : Type} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (e : V ≃ₗ[ℚ] H.rationalCarrier) (p : ℤ) (hweight : H.weight = 2 * p)
    (x : V) :
    x ∈ (H.ofLinearEquiv e).hodgeClasses p hweight ↔ e x ∈ H.hodgeClasses p hweight := by
  change
    ((Complexification.mapLinearEquiv V H.rationalCarrier e)
      ((H.ofLinearEquiv e).complexifyMap x) ∈ H.hodgePiece (p, p)) ↔
      (H.complexifyMap (e x) ∈ H.hodgePiece (p, p))
  have hvec :
      (Complexification.mapLinearEquiv V H.rationalCarrier e)
        ((H.ofLinearEquiv e).complexifyMap x) =
        H.complexifyMap (e x) := by
    dsimp [PureHodgeStructure.ofLinearEquiv, PureHodgeStructure.complexifyMap,
      PureHodgeStructure.complexifyVector]
    exact Complexification.mapLinearEquiv_tmul (V := V) (W := H.rationalCarrier) e (1 : ℂ) x
  constructor
  · intro hx
    rw [hvec] at hx
    exact hx
  · intro hx
    rw [hvec]
    exact hx

/-- Hodge classes are preserved by transporting a pure Hodge structure across a
rational linear equivalence. -/
noncomputable def hodgeClassesOfLinearEquiv (H : PureHodgeStructure)
    {V : Type} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (e : V ≃ₗ[ℚ] H.rationalCarrier) (p : ℤ) (hweight : H.weight = 2 * p) :
    (H.ofLinearEquiv e).hodgeClasses p hweight ≃ₗ[ℚ] H.hodgeClasses p hweight where
  toFun x := ⟨e x.1, by
    exact (hodgeClasses_ofLinearEquiv_iff H e p hweight x.1).1 x.2⟩
  invFun x := ⟨e.symm x.1, by
    exact (hodgeClasses_ofLinearEquiv_iff H e p hweight (e.symm x.1)).2
      (by
        rw [e.apply_symm_apply]
        exact x.2)⟩
  map_add' := by
    intro x y
    ext
    simp
  map_smul' := by
    intro q x
    ext
    simp
  left_inv := by
    intro x
    ext
    simp
  right_inv := by
    intro x
    ext
    simp

@[simp]
theorem hodgeClassesOfLinearEquiv_apply (H : PureHodgeStructure)
    {V : Type} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (e : V ≃ₗ[ℚ] H.rationalCarrier) (p : ℤ) (hweight : H.weight = 2 * p)
    (x : (H.ofLinearEquiv e).hodgeClasses p hweight) :
    H.hodgeClassesOfLinearEquiv e p hweight x = ⟨e x.1, by
      exact (hodgeClasses_ofLinearEquiv_iff H e p hweight x.1).1 x.2⟩ :=
  rfl

end PureHodgeStructure

end Hodge
end Boundary

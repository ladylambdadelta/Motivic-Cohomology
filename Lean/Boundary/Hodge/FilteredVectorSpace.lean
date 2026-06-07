import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Module.Prod
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Filtered vector spaces

Small linear-algebra API for increasing and decreasing filtrations by
subspaces.  The definitions are field-generic, but the Hodge files below use
them over `ℚ` and `ℂ`.
-/

universe u v

namespace Boundary
namespace Hodge

variable (K : Type u) [Field K]
variable (V : Type v) [AddCommGroup V] [Module K V]
variable {W : Type v} [AddCommGroup W] [Module K W]

/-- Product of two submodules, as a submodule of the product module. -/
def submoduleProd (S : Submodule K V) (T : Submodule K W) :
    Submodule K (V × W) where
  carrier := {x | x.1 ∈ S ∧ x.2 ∈ T}
  zero_mem' := ⟨S.zero_mem, T.zero_mem⟩
  add_mem' := by
    intro x y hx hy
    exact ⟨S.add_mem hx.1 hy.1, T.add_mem hx.2 hy.2⟩
  smul_mem' := by
    intro c x hx
    exact ⟨S.smul_mem c hx.1, T.smul_mem c hx.2⟩

@[simp]
theorem mem_submoduleProd {S : Submodule K V} {T : Submodule K W}
    {x : V × W} :
    x ∈ submoduleProd K V S T ↔ x.1 ∈ S ∧ x.2 ∈ T :=
  Iff.rfl

/-- The product submodule is linearly equivalent to the product of the two
subtype modules. -/
def submoduleProdLinearEquiv (S : Submodule K V) (T : Submodule K W) :
    submoduleProd K V S T ≃ₗ[K] S × T where
  toFun := fun x => (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun := fun x => ⟨(x.1.1, x.2.1), ⟨x.1.2, x.2.2⟩⟩
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro c x
    rfl
  left_inv := by
    intro x
    rfl
  right_inv := by
    intro x
    rfl

@[simp]
theorem submoduleProdLinearEquiv_apply (S : Submodule K V) (T : Submodule K W)
    (x : submoduleProd K V S T) :
    submoduleProdLinearEquiv K V S T x =
      (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩) :=
  rfl

theorem free_submoduleProd (S : Submodule K V) (T : Submodule K W)
    [Module.Free K S] [Module.Free K T] :
    Module.Free K (submoduleProd K V S T) := by
  letI : Module.Free K (S × T) := inferInstance
  exact Module.Free.of_equiv (submoduleProdLinearEquiv K V S T).symm

theorem finite_submoduleProd (S : Submodule K V) (T : Submodule K W)
    [Module.Finite K S] [Module.Finite K T] :
    Module.Finite K (submoduleProd K V S T) := by
  letI : Module.Finite K (S × T) := inferInstance
  exact Module.Finite.equiv (submoduleProdLinearEquiv K V S T).symm

theorem finrank_submoduleProd (S : Submodule K V) (T : Submodule K W)
    [Module.Free K S] [Module.Free K T] [Module.Finite K S] [Module.Finite K T] :
    Module.finrank K (submoduleProd K V S T) =
      Module.finrank K S + Module.finrank K T := by
  rw [LinearEquiv.finrank_eq (submoduleProdLinearEquiv K V S T)]
  exact Module.finrank_prod

/-- Quotienting a product by the product submodule is the product of the
individual quotients. -/
noncomputable def quotientSubmoduleProdEquiv (S : Submodule K V) (T : Submodule K W) :
    ((V × W) ⧸ submoduleProd K V S T) ≃ₗ[K] (V ⧸ S) × (W ⧸ T) where
  map_add' := by
    intro x y
    refine Quotient.inductionOn₂' x y ?_
    intro x y
    rfl
  map_smul' := by
    intro c x
    refine Quotient.inductionOn' x ?_
    intro x
    rfl
  toFun :=
    (submoduleProd K V S T).liftQ
      ((LinearMap.prod (S.mkQ.comp (LinearMap.fst K V W))
        (T.mkQ.comp (LinearMap.snd K V W)))) (by
          rintro ⟨x, y⟩ hxy
          ext <;> simp [hxy.1, hxy.2])
  invFun :=
    LinearMap.coprod
      (S.liftQ ((submoduleProd K V S T).mkQ.comp (LinearMap.inl K V W)) (by
        intro x hx
        rw [LinearMap.mem_ker]
        change (submoduleProd K V S T).mkQ (x, 0) = 0
        simp [hx]))
      (T.liftQ ((submoduleProd K V S T).mkQ.comp (LinearMap.inr K V W)) (by
        intro y hy
        rw [LinearMap.mem_ker]
        change (submoduleProd K V S T).mkQ (0, y) = 0
        simp [hy]))
  left_inv := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro x
    change
      LinearMap.coprod
        (S.liftQ ((submoduleProd K V S T).mkQ.comp (LinearMap.inl K V W)) _)
        (T.liftQ ((submoduleProd K V S T).mkQ.comp (LinearMap.inr K V W)) _)
        ((LinearMap.prod (S.mkQ.comp (LinearMap.fst K V W))
          (T.mkQ.comp (LinearMap.snd K V W))) x) =
      (submoduleProd K V S T).mkQ x
    rcases x with ⟨x, y⟩
    change Submodule.Quotient.mk ((x, (0 : W)) + ((0 : V), y)) =
      Submodule.Quotient.mk (x, y)
    simp
  right_inv := by
    intro z
    rcases z with ⟨x, y⟩
    refine Quotient.inductionOn₂' x y ?_
    intro x y
    change (S.mkQ x, (0 : W ⧸ T)) + ((0 : V ⧸ S), T.mkQ y) = (S.mkQ x, T.mkQ y)
    simp

@[simp]
theorem quotientSubmoduleProdEquiv_mk (S : Submodule K V) (T : Submodule K W)
    (x : V × W) :
    quotientSubmoduleProdEquiv K V S T ((submoduleProd K V S T).mkQ x) =
      (S.mkQ x.1, T.mkQ x.2) := by
  rfl

/-- A decreasing filtration `Fᵖ V`, indexed by integers. -/
structure DecreasingFiltration where
  step : ℤ → Submodule K V
  antitone' : ∀ ⦃p q : ℤ⦄, p ≤ q → step q ≤ step p

/-- An increasing filtration `Wₙ V`, indexed by integers. -/
structure IncreasingFiltration where
  step : ℤ → Submodule K V
  monotone' : ∀ ⦃p q : ℤ⦄, p ≤ q → step p ≤ step q

namespace DecreasingFiltration

variable {K V}

theorem antitone (F : DecreasingFiltration K V) ⦃p q : ℤ⦄
    (hpq : p ≤ q) : F.step q ≤ F.step p :=
  F.antitone' hpq

@[simp]
theorem step_le_step_iff (F : DecreasingFiltration K V) ⦃p q : ℤ⦄
    (hpq : p ≤ q) : F.step q ≤ F.step p :=
  F.antitone hpq

/-- The constant full decreasing filtration. -/
def full : DecreasingFiltration K V where
  step := fun _ => ⊤
  antitone' := by
    intro p q hpq
    exact le_top

/-- The constant zero decreasing filtration. -/
def zero : DecreasingFiltration K V where
  step := fun _ => ⊥
  antitone' := by
    intro p q hpq
    exact bot_le

@[simp]
theorem full_step (p : ℤ) : (full (K := K) (V := V)).step p = ⊤ :=
  rfl

@[simp]
theorem zero_step (p : ℤ) : (zero (K := K) (V := V)).step p = ⊥ :=
  rfl

end DecreasingFiltration

namespace IncreasingFiltration

variable {K V}

theorem monotone (W : IncreasingFiltration K V) ⦃p q : ℤ⦄
    (hpq : p ≤ q) : W.step p ≤ W.step q :=
  W.monotone' hpq

@[simp]
theorem step_le_step_iff (W : IncreasingFiltration K V) ⦃p q : ℤ⦄
    (hpq : p ≤ q) : W.step p ≤ W.step q :=
  W.monotone hpq

/-- The constant full increasing filtration. -/
def full : IncreasingFiltration K V where
  step := fun _ => ⊤
  monotone' := by
    intro p q hpq
    exact le_top

/-- The constant zero increasing filtration. -/
def zero : IncreasingFiltration K V where
  step := fun _ => ⊥
  monotone' := by
    intro p q hpq
    exact bot_le

@[simp]
theorem full_step (p : ℤ) : (full (K := K) (V := V)).step p = ⊤ :=
  rfl

@[simp]
theorem zero_step (p : ℤ) : (zero (K := K) (V := V)).step p = ⊥ :=
  rfl

/-- Componentwise product of increasing filtrations. -/
def product
    (W₁ : IncreasingFiltration K V) (W₂ : IncreasingFiltration K W) :
    IncreasingFiltration K (V × W) where
  step n := submoduleProd K V (W₁.step n) (W₂.step n)
  monotone' := by
    intro p q hpq x hx
    exact ⟨W₁.monotone hpq hx.1, W₂.monotone hpq hx.2⟩

/-- The previous filtration step, viewed as a submodule of `W.step n`. -/
def previousStepSubmodule (W : IncreasingFiltration K V) (n : ℤ) :
    Submodule K (W.step n) :=
  (W.step (n - 1)).comap (W.step n).subtype

@[simp]
theorem mem_previousStepSubmodule (W : IncreasingFiltration K V) (n : ℤ)
    (x : W.step n) :
    x ∈ W.previousStepSubmodule n ↔ x.1 ∈ W.step (n - 1) :=
  Iff.rfl

theorem previousStepSubmodule_product_map
    (W₁ : IncreasingFiltration K V) (W₂ : IncreasingFiltration K W) (n : ℤ) :
    (IncreasingFiltration.previousStepSubmodule (W₁.product W₂) n).map
        (submoduleProdLinearEquiv K V (W₁.step n) (W₂.step n)).toLinearMap =
      submoduleProd (K := K) (V := W₁.step n) (W := W₂.step n)
        (W₁.previousStepSubmodule n) (W₂.previousStepSubmodule n) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases y with ⟨⟨y₁, y₂⟩, hy'⟩
    rw [IncreasingFiltration.previousStepSubmodule, mem_submoduleProd] at hy
    exact hy
  · rintro hx
    refine ⟨⟨(x.1.1, x.2.1), ?_⟩, hx, ?_⟩
    · exact ⟨x.1.2, x.2.2⟩
    · ext <;> rfl

/-- The associated graded piece `grₙ^W(V) = Wₙ / Wₙ₋₁`. -/
abbrev gradedPiece (W : IncreasingFiltration K V) (n : ℤ) :=
  W.step n ⧸ W.previousStepSubmodule n

/-- The quotient map `Wₙ → grₙ^W(V)`. -/
def gradedPieceMkQ (W : IncreasingFiltration K V) (n : ℤ) :
    W.step n →ₗ[K] W.gradedPiece n :=
  (W.previousStepSubmodule n).mkQ

@[simp]
theorem gradedPieceMkQ_apply (W : IncreasingFiltration K V) (n : ℤ)
    (x : W.step n) :
    W.gradedPieceMkQ n x = (W.previousStepSubmodule n).mkQ x :=
  rfl

/-- A linear map preserving an increasing filtration induces maps on the
associated graded pieces. -/
def gradedPieceMapStep {V₂ : Type*} [AddCommGroup V₂] [Module K V₂]
    (W₁ : IncreasingFiltration K V) (W₂ : IncreasingFiltration K V₂)
    (f : V →ₗ[K] V₂)
    (hf : ∀ n, (W₁.step n).map f ≤ W₂.step n) (n : ℤ) :
    W₁.step n →ₗ[K] W₂.step n :=
  { toFun := fun x => ⟨f x.1, hf n ⟨x.1, x.2, rfl⟩⟩
    map_add' := by
      intro x y
      ext
      simp
    map_smul' := by
      intro c x
      ext
      simp }

theorem previousStepSubmodule_le_comap_gradedPieceMapStep {V₂ : Type*}
    [AddCommGroup V₂] [Module K V₂]
    (W₁ : IncreasingFiltration K V) (W₂ : IncreasingFiltration K V₂)
    (f : V →ₗ[K] V₂)
    (hf : ∀ n, (W₁.step n).map f ≤ W₂.step n) (n : ℤ) :
    W₁.previousStepSubmodule n ≤
      (W₂.previousStepSubmodule n).comap (W₁.gradedPieceMapStep W₂ f hf n) := by
  intro x hx
  change f x.1 ∈ W₂.step (n - 1)
  exact hf (n - 1) ⟨x.1, hx, rfl⟩

def gradedPieceMap {V₂ : Type*} [AddCommGroup V₂] [Module K V₂]
    (W₁ : IncreasingFiltration K V) (W₂ : IncreasingFiltration K V₂)
    (f : V →ₗ[K] V₂)
    (hf : ∀ n, (W₁.step n).map f ≤ W₂.step n) (n : ℤ) :
    W₁.gradedPiece n →ₗ[K] W₂.gradedPiece n := by
  exact
    (W₁.previousStepSubmodule n).mapQ (W₂.previousStepSubmodule n)
      (W₁.gradedPieceMapStep W₂ f hf n)
      (W₁.previousStepSubmodule_le_comap_gradedPieceMapStep W₂ f hf n)

@[simp]
theorem gradedPieceMap_mkQ {V₂ : Type*} [AddCommGroup V₂] [Module K V₂]
    (W₁ : IncreasingFiltration K V) (W₂ : IncreasingFiltration K V₂)
    (f : V →ₗ[K] V₂)
    (hf : ∀ n, (W₁.step n).map f ≤ W₂.step n) (n : ℤ) (x : W₁.step n) :
    W₁.gradedPieceMap W₂ f hf n ((W₁.previousStepSubmodule n).mkQ x) =
      (W₂.previousStepSubmodule n).mkQ ⟨f x.1, hf n ⟨x.1, x.2, rfl⟩⟩ :=
  show
    (W₁.previousStepSubmodule n).mapQ (W₂.previousStepSubmodule n)
      (W₁.gradedPieceMapStep W₂ f hf n)
      (W₁.previousStepSubmodule_le_comap_gradedPieceMapStep W₂ f hf n)
      ((W₁.previousStepSubmodule n).mkQ x) =
        (W₂.previousStepSubmodule n).mkQ ⟨f x.1, hf n ⟨x.1, x.2, rfl⟩⟩
  from
    Submodule.mapQ_apply
      (p := W₁.previousStepSubmodule n) (q := W₂.previousStepSubmodule n)
      (f := W₁.gradedPieceMapStep W₂ f hf n)
      (h := W₁.previousStepSubmodule_le_comap_gradedPieceMapStep W₂ f hf n) x

@[simp]
theorem gradedPieceMap_id (W : IncreasingFiltration K V) (n : ℤ) :
    W.gradedPieceMap W LinearMap.id (fun _ => by
      intro x hx
      rw [Submodule.map_id] at hx
      exact hx) n = LinearMap.id := by
  apply Submodule.linearMap_qext
  ext y
  rfl

theorem gradedPieceMap_comp {V₂ V₃ : Type*}
    [AddCommGroup V₂] [Module K V₂] [AddCommGroup V₃] [Module K V₃]
    (W₁ : IncreasingFiltration K V) (W₂ : IncreasingFiltration K V₂)
    (W₃ : IncreasingFiltration K V₃)
    (f : V →ₗ[K] V₂) (g : V₂ →ₗ[K] V₃)
    (hf : ∀ n, (W₁.step n).map f ≤ W₂.step n)
    (hg : ∀ n, (W₂.step n).map g ≤ W₃.step n)
    (n : ℤ) :
    W₁.gradedPieceMap W₃ (g.comp f)
    (by
          intro m x hx
          rcases hx with ⟨y, hy, rfl⟩
          exact hg m ⟨f y, hf m (show f y ∈ (W₁.step m).map f from Submodule.mem_map_of_mem hy), rfl⟩) n =
      (W₂.gradedPieceMap W₃ g hg n).comp (W₁.gradedPieceMap W₂ f hf n) := by
  apply Submodule.linearMap_qext
  ext y
  rfl

theorem finite_gradedPiece (W : IncreasingFiltration K V) (n : ℤ)
    [Module.Finite K V] :
    Module.Finite K (W.gradedPiece n) := by
  infer_instance

theorem finrank_gradedPiece (W : IncreasingFiltration K V) (n : ℤ)
    [Module.Finite K V] :
    Module.finrank K (W.gradedPiece n) =
      Module.finrank K (W.step n) -
        Module.finrank K (W.previousStepSubmodule n) := by
  rw [IncreasingFiltration.gradedPiece]
  exact Submodule.finrank_quotient (W.previousStepSubmodule n)

/-- The associated graded piece of a product filtration is the product of the
associated graded pieces. -/
noncomputable def gradedPieceProductEquiv
    (W₁ : IncreasingFiltration K V) (W₂ : IncreasingFiltration K W) (n : ℤ) :
    (W₁.product W₂).gradedPiece n ≃ₗ[K] W₁.gradedPiece n × W₂.gradedPiece n :=
  (Submodule.Quotient.equiv
      (IncreasingFiltration.previousStepSubmodule (W₁.product W₂) n)
      (submoduleProd (K := K) (V := W₁.step n) (W := W₂.step n)
        (W₁.previousStepSubmodule n) (W₂.previousStepSubmodule n))
      (submoduleProdLinearEquiv K V (W₁.step n) (W₂.step n))
      (W₁.previousStepSubmodule_product_map W₂ n)).trans
    (quotientSubmoduleProdEquiv (K := K) (V := W₁.step n) (W := W₂.step n)
      (W₁.previousStepSubmodule n) (W₂.previousStepSubmodule n))

end IncreasingFiltration

end Hodge
end Boundary

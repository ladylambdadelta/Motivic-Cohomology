import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Module.Prod
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

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

end IncreasingFiltration

end Hodge
end Boundary

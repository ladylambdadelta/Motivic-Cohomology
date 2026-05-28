import Mathlib.CategoryTheory.Category.Basic

/-!
# Formal Proof Scaffold

This file records the purely formal part of the simplified proof strategy:

tomography + holography => period faithfulness.

The harder step

strong generation => holography

is intentionally deferred until the triangulated and tensor-ideal infrastructure
for the simplified proof is introduced.
-/

universe u v w x

open CategoryTheory

namespace Boundary

/-- A chosen family of boundary probes inside a category. -/
structure ProbeFamily (C : Type u) [Category.{v} C] where
  Probe : Type w
  iota : Probe → C

variable {C : Type u} [Category.{v} C]

/-- The holographic record of an object against the chosen probe family. -/
def HolographicRecord (P : ProbeFamily C) (M : C) :=
  ∀ b : P.Probe, (P.iota b ⟶ M)

/-- Holography means that probe-precomposition detects equality of morphisms. -/
def Holography (P : ProbeFamily C) : Prop :=
  ∀ ⦃X Y : C⦄ (f g : X ⟶ Y),
    (∀ (b : P.Probe) (α : P.iota b ⟶ X), α ≫ f = α ≫ g) →
      f = g

/-- Tomography means equality of period records determines equality on every
    boundary probe input. -/
def Tomography
    (P : ProbeFamily C)
    (R : ∀ {X Y : C}, (X ⟶ Y) → Type x) : Prop :=
  ∀ ⦃X Y : C⦄ (f g : X ⟶ Y),
    R f = R g →
      ∀ (b : P.Probe) (α : P.iota b ⟶ X), α ≫ f = α ≫ g

/-- Period faithfulness is the final target statement. -/
def PeriodFaithfulness
    (R : ∀ {X Y : C}, (X ⟶ Y) → Type x) : Prop :=
  ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), R f = R g → f = g

/-- Formal theorem: tomography plus holography implies period faithfulness. -/
theorem tomography_implies_periodFaithfulness
    (P : ProbeFamily C)
    (R : ∀ {X Y : C}, (X ⟶ Y) → Type x)
    (hHolo : Holography P)
    (hTomo : Tomography P R) :
    PeriodFaithfulness R := by
  intro X Y f g hfg
  apply hHolo f g
  exact hTomo f g hfg

end Boundary

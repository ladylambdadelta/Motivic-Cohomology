import Geometry.Cycles.Basic
import Mathlib.Topology.Irreducible

/-!
# Integral Closed Component Families

This file isolates the honest cycle-level interface for decomposing an
arbitrary scheme into finitely many integral closed subschemes.

At this stage the file does **not** claim that Mathlib already constructs these
objects from irreducible components of a noetherian scheme. Instead it records
the exact data that such a construction must provide.
-/

universe u

open AlgebraicGeometry

noncomputable section

/-- A finite family of integral closed subschemes of a scheme. This is the
unweighted source-side family layer before any image multiplicities are
attached. -/
structure FiniteIntegralClosedFamily (X : Scheme.{u}) where
  index : Type u
  fintypeIndex : Fintype index
  decidableEqIndex : DecidableEq index
  component : index → IntClosedSubscheme X

namespace FiniteIntegralClosedFamily

variable {X : Scheme.{u}}

instance (family : FiniteIntegralClosedFamily X) : Fintype family.index :=
  family.fintypeIndex

instance (family : FiniteIntegralClosedFamily X) : DecidableEq family.index :=
  family.decidableEqIndex

end FiniteIntegralClosedFamily

/-- One irreducible component of a scheme, packaged as an integral closed
subscheme together with its topological provenance. -/
structure IrreducibleComponentAsIntClosedSubscheme (X : Scheme.{u}) where
  carrier : IntClosedSubscheme X
  isIrreducibleComponent :
    Set.range carrier.inclusion.base ∈ irreducibleComponents X

namespace IrreducibleComponentAsIntClosedSubscheme

variable {X : Scheme.{u}}

@[simp] theorem carrier_range_mem_irreducibleComponents
    (component : IrreducibleComponentAsIntClosedSubscheme X) :
    Set.range component.carrier.inclusion.base ∈ irreducibleComponents X :=
  component.isIrreducibleComponent

end IrreducibleComponentAsIntClosedSubscheme

/-- A finite decomposition of a scheme by integral closed subschemes whose
underlying topological images are actual irreducible components and whose union
covers the ambient scheme. This is the honest low-level input needed before any
composition-specific image or multiplicity data is attached. -/
structure FiniteIntegralClosedComponentDecomposition (X : Scheme.{u}) where
  index : Type u
  fintypeIndex : Fintype index
  decidableEqIndex : DecidableEq index
  component : index → IrreducibleComponentAsIntClosedSubscheme X
  covers :
    ∀ x : X.carrier,
      ∃ i : index, x ∈ Set.range ((component i).carrier.inclusion.base)
  irredundant : Function.Injective component

namespace FiniteIntegralClosedComponentDecomposition

variable {X : Scheme.{u}}

instance (decomposition : FiniteIntegralClosedComponentDecomposition X) :
    Fintype decomposition.index := decomposition.fintypeIndex

instance (decomposition : FiniteIntegralClosedComponentDecomposition X) :
    DecidableEq decomposition.index := decomposition.decidableEqIndex

/-- Forget the irreducible-component provenance and remember only the finite
family of integral closed subschemes. -/
def toFiniteIntegralClosedFamily
    (decomposition : FiniteIntegralClosedComponentDecomposition X) :
    FiniteIntegralClosedFamily X where
  index := decomposition.index
  fintypeIndex := decomposition.fintypeIndex
  decidableEqIndex := decomposition.decidableEqIndex
  component := fun i => (decomposition.component i).carrier

@[simp] theorem toFiniteIntegralClosedFamily_component
    (decomposition : FiniteIntegralClosedComponentDecomposition X)
    (i : decomposition.index) :
    decomposition.toFiniteIntegralClosedFamily.component i =
      (decomposition.component i).carrier := rfl

@[simp] theorem component_range_mem_irreducibleComponents
    (decomposition : FiniteIntegralClosedComponentDecomposition X)
    (i : decomposition.index) :
    Set.range ((decomposition.toFiniteIntegralClosedFamily.component i).inclusion.base) ∈
      irreducibleComponents X :=
  (decomposition.component i).isIrreducibleComponent

theorem exists_component_of_covers
    (decomposition : FiniteIntegralClosedComponentDecomposition X)
    (x : X.carrier) :
    ∃ i : decomposition.index,
      x ∈ Set.range ((decomposition.component i).carrier.inclusion.base) :=
  decomposition.covers x

end FiniteIntegralClosedComponentDecomposition

end

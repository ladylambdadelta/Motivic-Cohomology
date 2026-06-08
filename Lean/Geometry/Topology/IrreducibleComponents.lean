import Mathlib.Topology.Irreducible
import Mathlib.Topology.NoetherianSpace

/-!
# Local irreducibility and irreducible components

This file records the low-level topological lemma used by the component-geometry
pipeline:

* If every point has an open irreducible neighborhood, then irreducible
  components are open.
-/

open Set TopologicalSpace

universe u

namespace Geometry
namespace Topology

variable (X : Type u) [TopologicalSpace X]

/-- A topological space is locally irreducible if every point admits an open
irreducible neighborhood. -/
def LocallyIrreducibleSpace : Prop :=
  ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsIrreducible U

variable {X}

/-- In a locally irreducible space, each irreducible component is open. -/
theorem isOpen_irreducibleComponent_of_locallyIrreducible
    {C : Set X} (hC : C ∈ irreducibleComponents X)
    (hLoc : LocallyIrreducibleSpace X) : IsOpen C := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rcases hLoc x with ⟨U, hUOpen, hxU, hUIrr⟩
  have hMeet : (C ∩ U).Nonempty := ⟨x, hx, hxU⟩
  have hC_subset_closureU : C ⊆ closure U := by
    refine (subset_closure_inter_of_isPreirreducible_of_isOpen hC.1.2 hUOpen hMeet).trans ?_
    exact closure_mono inter_subset_right
  have hClosure_subset_C : closure U ⊆ C :=
    hC.2 hUIrr.closure hC_subset_closureU
  have hU_subset_C : U ⊆ C := by
    exact subset_closure.trans hClosure_subset_C
  exact Filter.mem_of_superset (hUOpen.mem_nhds hxU) hU_subset_C

/-- Noetherian locally irreducible spaces have clopen irreducible components. -/
theorem isClopen_irreducibleComponent_of_noetherian_locallyIrreducible
    [NoetherianSpace X] {C : Set X} (hC : C ∈ irreducibleComponents X)
    (hLoc : LocallyIrreducibleSpace X) : IsClopen C := by
  refine ⟨?_, isOpen_irreducibleComponent_of_locallyIrreducible hC hLoc⟩
  exact isClosed_of_mem_irreducibleComponents _ hC

end Topology
end Geometry

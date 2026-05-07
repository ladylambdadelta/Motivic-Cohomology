import TraceCalc.LayerB.RealObjects.SinkPeel
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin

/-!
# Real-objects formalization: existence of a sink in a finite DAG

**Real-objects path, cycle 7 (2026-04-23).**

This file proves:

* `DepGraph.sink_exists`: every nonempty `DepGraph n` has at least one
  sink. Manuscript reference: the remark following
  `thm:canonical-reconstruction-algorithm`
  (`our_paper_draft.tex` L1184): *"Because `Dep` is a finite DAG, it
  has at least one sink."* This is the missing bridge between
  `lem:sink-peel-preserves-completedness` (cycle 6) and the recursive
  reconstruction algorithm (cycle-pending).

The proof is the standard "no sink ⇒ infinite walk ⇒ pigeonhole gives
a cycle ⇒ contradicts acyclicity" argument, using
`Finite.exists_ne_map_eq_of_card_lt`.

The "canonical sink = `Key`-greatest sink" half of L1184 is left as a
separate downstream construction (it is purely a finite max over a
nonempty subset under the canonical key's total order, once existence
of a sink is in hand).
-/

namespace TraceCalc
namespace LayerB
namespace RealObjects

open RewriteCalculusSetup
open RewriteCalculusSetup.DepGraph

namespace RewriteCalculusSetup
namespace DepGraph

/-- **Existence of a sink in a finite acyclic dependence DAG**
(`our_paper_draft.tex` L1184: *"Because `Dep` is a finite DAG, it has
at least one sink."*).

For any `DepGraph n` with `0 < n`, there exists `s : Fin n` such that
`G.IsSink s`, i.e., `∀ j, G.edge s j = false`.

Proof: by contradiction. If no vertex were a sink, then every vertex
would have an outgoing edge. Classical choice yields a successor
function `f : Fin n → Fin n`. Iterating from any starting vertex
produces an infinite walk `walk : ℕ → Fin n`. By pigeonhole on
`walk` restricted to `Fin (n + 1)`, two distinct steps coincide,
yielding a directed cycle that contradicts `G.acyclic`. -/
theorem sink_exists {n : Nat} (G : DepGraph n) (hpos : 0 < n) :
    ∃ s : Fin n, G.IsSink s := by
  classical
  by_contra hno
  push_neg at hno
  -- `hno : ∀ s, ∃ j, G.edge s j ≠ false`
  have hsucc : ∀ s : Fin n, ∃ j : Fin n, G.edge s j = true := by
    intro s
    obtain ⟨j, hj⟩ : ∃ j, ¬ G.edge s j = false := by
      have := hno s
      simpa [DepGraph.IsSink, IsSink] using this
    refine ⟨j, ?_⟩
    cases hb : G.edge s j with
    | false => exact (hj hb).elim
    | true => rfl
  -- Successor function via classical choice.
  let f : Fin n → Fin n := fun s => (hsucc s).choose
  have hf : ∀ s, G.edge s (f s) = true := fun s => (hsucc s).choose_spec
  -- The walk: walk 0 = ⟨0, hpos⟩, walk (k+1) = f (walk k).
  let walk : Nat → Fin n := fun k => Nat.rec ⟨0, hpos⟩ (fun _ prev => f prev) k
  have walk_succ : ∀ k, walk (k + 1) = f (walk k) := fun _ => rfl
  -- Reach is preserved along consecutive walk segments.
  have hReach_seg : ∀ a d : Nat, 0 < d → G.Reach (walk a) (walk (a + d)) := by
    intro a d hd
    induction d with
    | zero => omega
    | succ m ih =>
      by_cases hm : m = 0
      · subst hm
        -- walk (a + 1) = f (walk a)
        have := hf (walk a)
        -- goal: G.Reach (walk a) (walk (a + 1))
        show Relation.TransGen _ (walk a) (walk (a + 1))
        rw [walk_succ]
        exact Relation.TransGen.single this
      · have hm' : 0 < m := Nat.pos_of_ne_zero hm
        have hRm : G.Reach (walk a) (walk (a + m)) := ih hm'
        have hstep : G.edge (walk (a + m)) (walk (a + m + 1)) = true := by
          rw [walk_succ]; exact hf _
        show Relation.TransGen _ (walk a) (walk (a + m + 1))
        exact Relation.TransGen.tail hRm hstep
  -- Pigeonhole on `Fin (n+1) → Fin n`.
  let g : Fin (n + 1) → Fin n := fun k => walk k.val
  have hcard : Fintype.card (Fin n) < Fintype.card (Fin (n + 1)) := by
    simp
  obtain ⟨a, b, hab, hgab⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt g hcard
  -- WLOG a.val < b.val.
  have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · -- a.val < b.val
    have hd : 0 < b.val - a.val := Nat.sub_pos_of_lt hlt
    have heq : a.val + (b.val - a.val) = b.val := by omega
    have hReach : G.Reach (walk a.val) (walk b.val) := by
      have := hReach_seg a.val (b.val - a.val) hd
      rwa [heq] at this
    -- walk a.val = walk b.val (= g a = g b).
    have hwalk_eq : walk a.val = walk b.val := hgab
    rw [← hwalk_eq] at hReach
    exact G.acyclic _ hReach
  · -- b.val < a.val: symmetric.
    have hd : 0 < a.val - b.val := Nat.sub_pos_of_lt hgt
    have heq : b.val + (a.val - b.val) = a.val := by omega
    have hReach : G.Reach (walk b.val) (walk a.val) := by
      have := hReach_seg b.val (a.val - b.val) hd
      rwa [heq] at this
    have hwalk_eq : walk b.val = walk a.val := hgab.symm
    rw [← hwalk_eq] at hReach
    exact G.acyclic _ hReach

end DepGraph
end RewriteCalculusSetup

end RealObjects
end LayerB
end TraceCalc

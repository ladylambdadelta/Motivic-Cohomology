import TraceCalc.LayerB.Boundary
import Mathlib.Data.Fintype.Card

/-!
# Reconstruction shadow model (Layer B, sandbox)

**STATUS (reclassified 2026-04-23, per the new strict standard):**
**SHADOW MODEL / SANDBOX. THIS FILE DOES NOT FORMALIZE THE MANUSCRIPT THEOREM.**

Everything in this file lives in namespace `TraceCalc.LayerB.ShadowModel`.
The definitions below are a normalized finite-combinatorial sandbox in which
structural lemmas about sink-peel reconstruction can be checked, **not** a
formalization of `thm:canonical-reconstruction-algorithm` (`our_paper_draft.tex`
L1149).

Concretely the sandbox commits the following deviations from the manuscript:

* `Trace := List Nat` is **not** the manuscript's certified trace object; it
  forgets packet payload, ports, attachments, gluing, and admissibility.
* `canonicalSink` is *definitionally* `some n` on `(n+1)`-records, not
  *theorem-level* discovered from the record.
* `reconstruct r = List.range n` (proved as `reconstruct_eq_range`), so all
  trace-correctness theorems reduce to statements about a *pre-normalized*
  serialization; `reconstruct` is not the manuscript's `T`.
* `CompletedRecord.c1` is strictly weaker than the manuscript's C1: it has
  no refined outputs, no source-boundary matching, no port typing.
* `TraceIsValidReconstruction.of_concat` concatenates lists under a binary
  no-cross-`requires` hypothesis; it is **not** `thm:tensor-factor-independence`
  (which requires actual trace tensoring, full WCC decomposition, and gluing
  semantics).

The file is retained because the lemmas about this combinatorial substrate
are correct on their own terms and may be useful as guideposts when the
real-objects path is built. Per `TEX_TO_LEAN_MAP.md` §"Anti-impersonation
rule (strict standard)", the corresponding manuscript map rows have been
demoted to record "no formalization yet".

## Original (pre-reclassification) introduction

The file was originally introduced as a vertical slice of

  Theorem (Canonical reconstruction algorithm), `thm:canonical-reconstruction-algorithm`,
  manuscript line ~1149.

## Representation choices (and what they cost)

Per `docs/design_reconstruction_record.md`, none of the seven design questions
are formally locked. To make progress, this file commits to the *simplest
faithful finite-combinatorial slice* of the algorithm and records the tradeoff
honestly here. Any future widening must come back and revisit each choice.

The committed slice:

* **Packets are indexed by `Fin n`, in `Key` order** (design Q1 + Q5(c)).
  This makes `Key` definitionally the identity, so `prop:key-total-injective`
  holds trivially in this slice.
* **`SupportDAG n`** is a `Bool`-valued adjacency `Fin n → Fin n → Bool` with the
  upper-triangular invariant `edge i j = true → i < j`. Acyclicity is *automatic*
  from upper-triangularity, and the largest index is *automatically* a sink.
  This is design Q2 (option (b)) combined with Q5(c). The cost: the file does
  not yet model arbitrary linear extensions of `Key`; it presupposes that the
  manuscript's `Key`-induced ordering has already been used to relabel packets.
* **`Trace` is `List Nat`** — a closed reconstructed trace is the sequence of
  packet indices in the order they are attached during the algorithm. Packet
  payload, attachment witnesses, and gluing semantics are entirely abstracted
  away (they are *not* in this slice).
  This is the most aggressive simplification in the file. It is faithful to
  the *combinatorial* content of the algorithm — the order in which packets
  are reattached — but it carries none of the rewrite-system payload of
  Definition `def:completed-reconstruction-record` (L1100).
* **`reconstruct` returns `Trace`, not `Option Trace`.** With upper-triangular
  `dep`, every record reconstructs (the largest index is always a sink, sink-peel
  always shrinks `n` by one, the recursion is total). The user-facing spec asked
  for `Option Trace`; we honor that with `reconstruct? : ReconstructionRecord n →
  Option Trace`, defined as `some (reconstruct r)`, so the theorem statements
  about partial reconstruction are still expressible in their `Option`-shaped form.

## What is *not* in this slice (concrete obligations remaining)

`thm:canonical-reconstruction-algorithm` proves that the algorithm produces a
*certified trace* `R` realizing `∂*` modulo a controlled equivalence, and that
the result is independent of choices (`thm:tensor-factor-independence`, L1278).
This file does **not** address:

1. The packet payload (rewrite scheme, refined interfaces, support data, replay
   certificate, L1109). Packets here are bare indices.
2. The attachment witness `Attach` and the typed gluing operation `Glue` (L1112,
   L1175). `reattach` here is `List.append [p]`.
3. The completion conditions C1–C4 (L1126). The current `ReconstructionRecord`
   type does not carry C1, C2, C4 as `Prop` fields; only C3 (acyclicity) is
   present and is enforced at the type level via upper-triangularity.
4. The **tensor-factorization branch** of the algorithm (L1149, case (1)):
   weakly-connected-component decomposition and parallel composition. The
   present file recurses *only* via canonical sink peel; for a record whose
   `dep` has multiple weakly-connected components, the resulting trace
   serializes them in `Key` order, which is correct for the *underlying linear
   reconstruction* but does not witness the tensor structure.
5. `lem:sink-peel-preserves-completedness` (L1235): trivially true for our
   record because we carry no completion `Prop`s. A faithful version requires
   item 3 first.
6. `lem:sink-deletion-inverse` (L1260): the round-trip `peel ∘ glue = id` is
   *not* stated here because `glue` is not modeled; in our slice the analogous
   statement is `predecessor (after appending p) = original`, but it is
   off-by-one in the type and not required for the recursion theorem below.
7. Tensor-factor independence (`thm:tensor-factor-independence`, L1278). Out of
   scope until item 4.

The recursion theorem (`reconstruct_canonical_sink_step` below) is the
**proof-shaped core** of the reconstruction algorithm: it states that the
`reconstruct` function commutes with one step of canonical-sink peel-and-glue,
which is the load-bearing structural identity of the manuscript's recursion.
-/

universe u

namespace TraceCalc
namespace LayerB
namespace ShadowModel

/-! ### Support DAG -/

/-- A finite directed acyclic dependency graph on packet indices `Fin n`,
encoded as an adjacency `Bool`-matrix with the **upper-triangular invariant**
`edge i j = true → i < j`.

In the manuscript's vocabulary this is `Dep` (`def:completed-reconstruction-record`,
L1100, component (5)), restricted to records whose packets have already been
relabeled into `Key`-induced order so that `Key = id` (design Q5(c)). Acyclicity
is automatic. The convention is `edge i j = true ↔ "j depends on i"`, so a
**sink** is a vertex with no outgoing edges (nothing depends on it). -/
structure SupportDAG (n : Nat) where
  edge  : Fin n → Fin n → Bool
  upper : ∀ (i j : Fin n), edge i j = true → i.val < j.val

namespace SupportDAG

variable {n : Nat}

/-- A vertex `i` is a **sink** if nothing depends on it: no outgoing edges. -/
def IsSink (D : SupportDAG n) (i : Fin n) : Prop :=
  ∀ j : Fin n, D.edge i j = false

/-- The largest index `Fin.last n` of `SupportDAG (n+1)` is automatically a sink:
upper-triangularity forbids `edge (Fin.last n) j = true` because no `j.val` can
exceed `n`. This is the slice-specific reason the canonical sink always exists
when `n ≥ 1`. -/
theorem isSink_last (D : SupportDAG (n+1)) : D.IsSink (Fin.last n) := by
  intro j
  by_contra h
  have h' : D.edge (Fin.last n) j = true := by
    cases hb : D.edge (Fin.last n) j
    · exact absurd hb h
    · rfl
  have hlt : (Fin.last n).val < j.val := D.upper _ _ h'
  have : j.val < n + 1 := j.isLt
  simp [Fin.last] at hlt
  omega

/-- Restriction of a `SupportDAG (n+1)` to its first `n` vertices, by deleting
the last vertex. Upper-triangularity is preserved because `Fin.castSucc` is
order-preserving on `.val`. This is the **predecessor-DAG** of canonical sink
peel applied to the canonical sink `Fin.last n`. -/
def predecessor (D : SupportDAG (n+1)) : SupportDAG n where
  edge i j := D.edge i.castSucc j.castSucc
  upper i j h := by
    have := D.upper i.castSucc j.castSucc h
    simpa [Fin.castSucc, Fin.castAdd, Fin.castLE] using this

end SupportDAG

/-! ### Reconstruction record -/

/-- The combinatorial slice of `def:completed-reconstruction-record` (L1100):
just the size and the dependency DAG. Packet payload, ports, attachment, and
the C1/C2/C4 completion `Prop`s are intentionally absent — see the file
docstring for the explicit list of what this elides. -/
structure ReconstructionRecord (n : Nat) where
  dep : SupportDAG n

namespace ReconstructionRecord

variable {n : Nat}

/-- Predecessor record obtained by canonical sink peel applied to the canonical
sink `Fin.last n` of an `(n+1)`-record. -/
def predecessor (r : ReconstructionRecord (n+1)) : ReconstructionRecord n :=
  ⟨r.dep.predecessor⟩

end ReconstructionRecord

/-! ### Trace and reattachment -/

/-- A reconstructed closed trace, in this slice: the sequence of packet indices
in the order they were reattached by the algorithm. Lossy w.r.t. the
manuscript's certified trace; see file docstring item 2. -/
abbrev Trace : Type := List Nat

/-- Reattach a peeled packet `p` to a previously reconstructed predecessor trace.
In this slice this is just appending the packet's index. The manuscript's
`Glue(R, s; Attach(s))` (L1175) carries typed boundary information that is not
present in our `Trace`; see file docstring item 2. -/
def reattach {n : Nat} (_r : ReconstructionRecord n) (p : Nat) (tr : Trace) : Trace :=
  tr ++ [p]

/-! ### Canonical sink and reconstruction -/

/-- Canonical sink of a record (manuscript: the `Key`-greatest sink, L1149).
In this slice, where `Key` is the identity on `Fin n`, the canonical sink is
`Fin.last (n-1)` when `n ≥ 1` and `none` when the record is empty.
Returns the underlying `Nat` index for compatibility with `Trace = List Nat`. -/
def canonicalSink : {n : Nat} → ReconstructionRecord n → Option Nat
  | 0,     _ => none
  | n+1,   _ => some n

/-- The canonical reconstruction algorithm (sink-peel slice). Recurses by
canonical-sink peel only; the tensor-factorization branch is omitted (file
docstring item 4). The recursion is structural on `n`, hence automatically
well-founded. -/
def reconstruct : {n : Nat} → ReconstructionRecord n → Trace
  | 0,     _ => []
  | n+1,   r => reattach r.predecessor n (reconstruct r.predecessor)

/-- The user-spec `Option`-valued wrapper. In this slice reconstruction is
*total*; the wrapper exists so theorems about reconstruction success are
expressible in their `Option`-shaped form. -/
def reconstruct? {n : Nat} (r : ReconstructionRecord n) : Option Trace :=
  some (reconstruct r)

/-! ### Theorems

Each theorem is tagged with its **scope** in the docstring. Per the
`TEX_TO_LEAN_MAP.md` anti-impersonation rule, none of these is the full
`thm:canonical-reconstruction-algorithm`; they are named slices.
-/

/-- **Scope: emptiness predicate on `canonicalSink`.**
`canonicalSink r = none` iff the record has size zero. Holds in this slice;
in the full algorithm the analogue is "no canonical sink ⇒ no packets to peel". -/
theorem canonicalSink_none_iff_empty :
    ∀ {n : Nat} (r : ReconstructionRecord n),
      canonicalSink r = none ↔ n = 0
  | 0,     _ => by simp [canonicalSink]
  | _+1,   _ => by simp [canonicalSink]

/-- **Scope: index-level strict descent for canonical sink peel.**
The size of the predecessor record is strictly less than the size of the
original. This is the termination measure justifying the `reconstruct`
recursion. In the manuscript this corresponds to the strict descent step in
the proof of `prop:reconstruction-termination` (L1267). -/
theorem predecessorRecord_strictly_smaller
    {n : Nat} (_r : ReconstructionRecord (n+1)) :
    (n : Nat) < n + 1 := Nat.lt_succ_self n

/-- **Scope: empty case of `reconstruct`.** -/
@[simp] theorem reconstruct_empty (r : ReconstructionRecord 0) :
    reconstruct r = [] := rfl

/-- **Scope: singleton case of `reconstruct`.**
The base case of the manuscript's recursion (L1149, case (2)). -/
@[simp] theorem reconstruct_singleton (r : ReconstructionRecord 1) :
    reconstruct r = [0] := rfl

/-- **Scope: empty case for the `Option`-wrapped reconstruction.** -/
theorem reconstruct?_empty (r : ReconstructionRecord 0) :
    reconstruct? r = some [] := rfl

/-- **Scope: the canonical-sink recursion identity — proof-shaped core of
`thm:canonical-reconstruction-algorithm`.**

If `canonicalSink r = some p`, then the full reconstruction equals the
predecessor's reconstruction with `p` reattached. This is the load-bearing
structural identity of the manuscript's recursion (L1149, case (3)):

  *"recurse on the predecessor subrecord and reattach via `Glue`"*

The slice qualification: `reattach` here is `List.append [p]`, so the witnessed
identity is the *combinatorial* shadow of the manuscript's gluing equation,
not its certified-trace form. See file docstring items 2 and 6. -/
theorem reconstruct_canonical_sink_step
    {n : Nat} (r : ReconstructionRecord (n+1)) (p : Nat)
    (hp : canonicalSink r = some p) :
    reconstruct r = reattach r.predecessor p (reconstruct r.predecessor) := by
  -- `canonicalSink` on an `(n+1)`-record returns `some n`, so `p = n`.
  have hp' : p = n := by
    simp [canonicalSink] at hp
    exact hp.symm
  subst hp'
  rfl

/-- **Scope: the `Option`-wrapped form of `reconstruct_canonical_sink_step`.**
If `canonicalSink r = some p` and recursive reconstruction of the predecessor
succeeds with `tr`, then `reconstruct? r = some (reattach _ p tr)`. -/
theorem reconstruct?_canonical_sink_step
    {n : Nat} (r : ReconstructionRecord (n+1)) (p : Nat) (tr : Trace)
    (hp : canonicalSink r = some p)
    (htr : reconstruct? r.predecessor = some tr) :
    reconstruct? r = some (reattach r.predecessor p tr) := by
  have hp' : p = n := by simp [canonicalSink] at hp; exact hp.symm
  have htr' : tr = reconstruct r.predecessor := by
    simpa [reconstruct?] using htr.symm
  subst hp'; subst htr'
  rfl

/-! ### Completedness — first honest predicate

Per the user instruction of 2026-04-23 (Option A), we add a real, non-vacuous
C1-shaped completion `Prop` to the slice and prove that canonical-sink peel
preserves it.

**Manuscript correspondence:** condition C1 of `def:completed-reconstruction-record`
(L1126): "every refined input of a packet is matched by a refined output of a
prior packet or the source boundary". The corresponding preservation lemma is
`lem:sink-peel-preserves-completedness`, clause C1$'$ (L1235):
"Since `s` is a sink, no other packet had an edge from `s`; therefore the
inputs of any remaining packet are fulfilled by other packets, which all
remain."

**Slice scope** (per the anti-impersonation rule): we model a packet's
"refined inputs" as a list of producer-packet indices in `Fin n`. A record is
*C1-completed* iff every declared input is realized by an actual dependency
edge. We do **not** model refined-output multiplicity, source-boundary
matching, or port-level typing. This is genuinely weaker than the manuscript's
C1, but it is non-trivial: it requires the predecessor construction to *prove*
that no remaining packet listed the deleted sink as one of its inputs. -/

/-- A reconstruction record together with declared input-requirements per
packet, satisfying the slice's C1-shaped completedness predicate. -/
structure CompletedRecord (n : Nat) extends ReconstructionRecord n where
  /-- For each consumer index `j`, the list of producer indices required by `j`. -/
  requires : Fin n → List (Fin n)
  /-- C1 (slice): every declared input is realized by a real dependency edge. -/
  c1 : ∀ (j i : Fin n), i ∈ requires j → dep.edge i j = true

namespace CompletedRecord

variable {n : Nat}

/-- **Scope: structural consequence of C1 against the canonical sink.**
In any C1-completed record on `n+1` packets, the canonical sink `Fin.last n`
appears as a declared input of no packet. This is the non-vacuous content of
slice-C1: if `Fin.last n` were required by some `j`, then by C1 there would
be an outgoing edge from `Fin.last n`, contradicting `SupportDAG.isSink_last`.

This is the load-bearing fact behind `lem:sink-peel-preserves-completedness`
clause C1$'$ in the slice. -/
theorem canonicalSink_not_required
    (r : CompletedRecord (n+1)) (j : Fin (n+1)) :
    Fin.last n ∉ r.requires j := by
  intro h
  have hedge : r.dep.edge (Fin.last n) j = true := r.c1 j (Fin.last n) h
  have hsink : r.dep.edge (Fin.last n) j = false := r.dep.isSink_last j
  rw [hsink] at hedge
  exact Bool.false_ne_true hedge

/-- Predecessor of a C1-completed record: drops the canonical sink `Fin.last n`
and restricts the requires-relation to `Fin n` indices. The lift is well-typed
because, by C1 plus upper-triangularity, every declared input `i` to a
remaining packet `j.castSucc` satisfies `i.val < j.val < n`. -/
def predecessor (r : CompletedRecord (n+1)) : CompletedRecord n where
  toReconstructionRecord := r.toReconstructionRecord.predecessor
  requires j := (r.requires j.castSucc).pmap
    (fun (i : Fin (n+1)) (h : i ∈ r.requires j.castSucc) =>
      ⟨i.val, by
        have hedge := r.c1 j.castSucc i h
        have hlt := r.dep.upper i j.castSucc hedge
        have hjlt : j.val < n := j.isLt
        have hjcast : (j.castSucc : Fin (n+1)).val = j.val := rfl
        rw [hjcast] at hlt
        exact lt_trans hlt hjlt⟩)
    (fun _ h => h)
  c1 j i hi := by
    rw [List.mem_pmap] at hi
    obtain ⟨i', hi'mem, hi'eq⟩ := hi
    have hval : i'.val = i.val := by
      have := congrArg Fin.val hi'eq
      simpa using this
    have hedge : r.dep.edge i' j.castSucc = true := r.c1 j.castSucc i' hi'mem
    show r.dep.edge i.castSucc j.castSucc = true
    have hcast : i.castSucc = i' := by
      apply Fin.ext
      show i.val = i'.val
      exact hval.symm
    rw [hcast]
    exact hedge

/-- **Scope: requirements of the predecessor are exactly the inherited ones.**
This is the cleanest formal statement of "sink peel preserves slice-C1":
membership in the predecessor's requires-relation is the lift of membership
in the original's requires-relation across `Fin.castSucc`.

Together with `canonicalSink_not_required`, this packages the combinatorial
slice of `lem:sink-peel-preserves-completedness` (L1235). -/
theorem mem_requires_predecessor
    (r : CompletedRecord (n+1)) (j i : Fin n) :
    i ∈ r.predecessor.requires j ↔ i.castSucc ∈ r.requires j.castSucc := by
  constructor
  · intro hi
    show i.castSucc ∈ r.requires j.castSucc
    -- Unfold predecessor's requires
    change i ∈ (r.requires j.castSucc).pmap _ _ at hi
    rw [List.mem_pmap] at hi
    obtain ⟨i', hi'mem, hi'eq⟩ := hi
    have hval : i'.val = i.val := by
      have := congrArg Fin.val hi'eq; simpa using this
    have hcast : i.castSucc = i' := by
      apply Fin.ext; show i.val = i'.val; exact hval.symm
    rw [hcast]; exact hi'mem
  · intro hi
    change i ∈ (r.requires j.castSucc).pmap _ _
    rw [List.mem_pmap]
    refine ⟨i.castSucc, hi, ?_⟩
    apply Fin.ext
    rfl

/-- **Scope: sink-peel preserves slice-C1 completedness, statement form.**
Direct restatement of the manuscript's `lem:sink-peel-preserves-completedness`
(L1235), restricted to the C1 clause and to the slice's input-list model:
the predecessor of a C1-completed record is again C1-completed. In Lean this
is true *by construction* of `CompletedRecord.predecessor`, so the statement
is the type-correctness of the construction itself; we record it as a
public theorem so its scope is documented. -/
theorem sinkPeel_preserves_C1 (r : CompletedRecord (n+1)) :
    ∀ (j i : Fin n),
      i ∈ r.predecessor.requires j → r.predecessor.dep.edge i j = true :=
  r.predecessor.c1

end CompletedRecord

/-! ### Canonical threshold cuts on completed records

The normalization bridge needed upstream in Campaign 12B is, at bottom, a cut
on the finite packet index set of a completed reconstruction record. In this
shadow-model layer the canonical cut is simply the threshold split on packet
indices, and admissibility reduces to upper-triangularity of the dependency
DAG. -/

/-- Lower packet set determined by a threshold on a completed record. -/
def canonicalLowerSet {n : Nat} (_r : CompletedRecord n) (threshold : Nat) :
    Finset (Fin n) :=
  Finset.univ.filter fun i => i.val < threshold

/-- Upper packet set determined by a threshold on a completed record. -/
def canonicalUpperSet {n : Nat} (_r : CompletedRecord n) (threshold : Nat) :
    Finset (Fin n) :=
  Finset.univ.filter fun i => threshold ≤ i.val

theorem mem_canonicalLowerSet_iff {n : Nat} (r : CompletedRecord n)
    (threshold : Nat) (i : Fin n) :
    i ∈ canonicalLowerSet r threshold ↔ i.val < threshold := by
  simp [canonicalLowerSet]

theorem mem_canonicalUpperSet_iff {n : Nat} (r : CompletedRecord n)
    (threshold : Nat) (i : Fin n) :
    i ∈ canonicalUpperSet r threshold ↔ threshold ≤ i.val := by
  simp [canonicalUpperSet]

/-- Canonical threshold cut on the packet set of a completed record.

This is the exact low-level bridge needed upstream: a threshold cut on the
finite reconstruction record together with the proof that the lower part is
closed under declared dependencies and that the complementary upper part is a
genuine partition of the packet set. -/
structure CanonicalThresholdCut {n : Nat}
    (r : CompletedRecord n) (threshold : Nat) where
  threshold_le : threshold ≤ n
  lowerSet : Finset (Fin n)
  upperSet : Finset (Fin n)
  lower_mem_iff : ∀ i : Fin n, i ∈ lowerSet ↔ i.val < threshold
  upper_mem_iff : ∀ i : Fin n, i ∈ upperSet ↔ threshold ≤ i.val
  lower_dependency_closed :
    ∀ {j i : Fin n}, j ∈ lowerSet → i ∈ r.requires j → i ∈ lowerSet
  partition : lowerSet ∪ upperSet = Finset.univ
  disjoint : Disjoint lowerSet upperSet

namespace CanonicalThresholdCut

def ofLe {n : Nat} (r : CompletedRecord n) (threshold : Nat)
    (hThreshold : threshold ≤ n) : CanonicalThresholdCut r threshold where
  threshold_le := hThreshold
  lowerSet := canonicalLowerSet r threshold
  upperSet := canonicalUpperSet r threshold
  lower_mem_iff := mem_canonicalLowerSet_iff r threshold
  upper_mem_iff := mem_canonicalUpperSet_iff r threshold
  lower_dependency_closed := by
    intro j i hj hi
    rw [mem_canonicalLowerSet_iff] at hj ⊢
    exact lt_trans (r.dep.upper i j (r.c1 j i hi)) hj
  partition := by
    ext i
    simp [canonicalLowerSet, canonicalUpperSet]
    exact Nat.lt_or_ge i.val threshold
  disjoint := by
    refine Finset.disjoint_left.mpr ?_
    intro i hiL hiU
    rw [mem_canonicalLowerSet_iff] at hiL
    rw [mem_canonicalUpperSet_iff] at hiU
    exact (Nat.not_lt.mpr hiU) hiL

variable {n threshold : Nat}
variable {r : CompletedRecord n}

/-- Inclusion of the canonical lower threshold block into the ambient record. -/
def lowerEmbedding (cut : CanonicalThresholdCut r threshold) :
    Fin threshold → Fin n :=
  fun i => i.castLE cut.threshold_le

/-- Inclusion of the canonical upper threshold block into the ambient record. -/
def upperEmbedding (cut : CanonicalThresholdCut r threshold) :
    Fin (n - threshold) → Fin n :=
  fun i =>
    ⟨threshold + i.val, by
      have hi := i.isLt
      omega⟩

/-- Projection of an ambient packet index to the upper complementary block,
when the index lies weakly above the threshold. -/
def upperProjection (cut : CanonicalThresholdCut r threshold) (i : Fin n) :
    Option (Fin (n - threshold)) :=
  if h : threshold ≤ i.val then
    some ⟨i.val - threshold, by
      have hi := i.isLt
      omega⟩
  else
    none

theorem upperProjection_upperEmbedding
    (cut : CanonicalThresholdCut r threshold) (i : Fin (n - threshold)) :
    cut.upperProjection (cut.upperEmbedding i) = some i := by
  unfold upperProjection upperEmbedding
  simp

theorem upperProjection_lowerEmbedding
    (cut : CanonicalThresholdCut r threshold) (i : Fin threshold) :
    cut.upperProjection (cut.lowerEmbedding i) = none := by
  unfold upperProjection lowerEmbedding
  simp [show ¬threshold ≤ i.val by exact Nat.not_le_of_lt i.isLt]

/-- The lower threshold block as a genuine completed subrecord, reindexed to
`Fin threshold`. -/
def lowerRecord (cut : CanonicalThresholdCut r threshold) :
    CompletedRecord threshold where
  toReconstructionRecord := {
    dep := {
      edge := fun i j => r.dep.edge (cut.lowerEmbedding i) (cut.lowerEmbedding j)
      upper := by
        intro i j h
        have hij := r.dep.upper (cut.lowerEmbedding i) (cut.lowerEmbedding j) h
        simpa [lowerEmbedding, Fin.castLE] using hij
    }
  }
  requires j :=
    (r.requires (cut.lowerEmbedding j)).pmap
      (fun i h =>
        ⟨i.val, by
          have hedge : r.dep.edge i (cut.lowerEmbedding j) = true :=
            r.c1 (cut.lowerEmbedding j) i h
          have hlt : i.val < (cut.lowerEmbedding j).val :=
            r.dep.upper i (cut.lowerEmbedding j) hedge
          have hjlt : (cut.lowerEmbedding j).val < threshold := by
            simpa [lowerEmbedding, Fin.castLE] using j.isLt
          exact lt_trans hlt hjlt⟩)
      (fun _ h => h)
  c1 j i hi := by
    change i ∈ (r.requires (cut.lowerEmbedding j)).pmap _ _ at hi
    rw [List.mem_pmap] at hi
    obtain ⟨i', hi'mem, hi'eq⟩ := hi
    have hval : i'.val = i.val := by
      have := congrArg Fin.val hi'eq
      simpa using this
    have hedge : r.dep.edge i' (cut.lowerEmbedding j) = true :=
      r.c1 (cut.lowerEmbedding j) i' hi'mem
    have hcast : cut.lowerEmbedding i = i' := by
      apply Fin.ext
      simpa [lowerEmbedding, Fin.castLE] using hval.symm
    simpa [hcast] using hedge

/-- The upper complementary block as a genuine reindexed completed record,
retaining only internal upper-block dependencies. -/
def upperRecord (cut : CanonicalThresholdCut r threshold) :
    CompletedRecord (n - threshold) where
  toReconstructionRecord := {
    dep := {
      edge := fun i j => r.dep.edge (cut.upperEmbedding i) (cut.upperEmbedding j)
      upper := by
        intro i j h
        have hij := r.dep.upper (cut.upperEmbedding i) (cut.upperEmbedding j) h
        simpa [upperEmbedding] using hij
    }
  }
  requires j :=
    ((r.requires (cut.upperEmbedding j)).filter fun i => threshold ≤ i.val).pmap
      (fun i h =>
        ⟨i.val - threshold, by
          rw [List.mem_filter] at h
          have hi_ge : threshold ≤ i.val := by
            simpa using h.2
          exact Nat.sub_lt_sub_right hi_ge i.isLt⟩)
      (fun _ h => h)
  c1 j i hi := by
    change i ∈ ((r.requires (cut.upperEmbedding j)).filter fun i => threshold ≤ i.val).pmap _ _ at hi
    rw [List.mem_pmap] at hi
    obtain ⟨i', hi'mem, hi'eq⟩ := hi
    rw [List.mem_filter] at hi'mem
    obtain ⟨hi'req, hi'ge⟩ := hi'mem
    have hval_sub : i'.val - threshold = i.val := by
      have := congrArg Fin.val hi'eq
      simpa using this
    have hi'ge' : threshold ≤ i'.val := by
      simpa using hi'ge
    have hval : i'.val = threshold + i.val := by
      omega
    have hedge : r.dep.edge i' (cut.upperEmbedding j) = true :=
      r.c1 (cut.upperEmbedding j) i' hi'req
    have hcast : cut.upperEmbedding i = i' := by
      apply Fin.ext
      simpa [upperEmbedding] using hval.symm
    simpa [hcast] using hedge

/-- Shadow-model cofiber-style package attached to a canonical threshold cut.
It records the actual lower and upper reindexed completed records together
with the ambient inclusion/projection data available in this finite model. -/
structure CofiberSequenceData (cut : CanonicalThresholdCut r threshold) where
  lowerRecord : CompletedRecord threshold
  totalRecord : CompletedRecord n
  upperRecord : CompletedRecord (n - threshold)
  lowerToTotal : Fin threshold → Fin n
  totalToUpper : Fin n → Option (Fin (n - threshold))
  lowerProjectionVanishes : ∀ i : Fin threshold, totalToUpper (lowerToTotal i) = none
  upperProjectionSplits : ∀ i : Fin (n - threshold),
    totalToUpper (cut.upperEmbedding i) = some i

/-- Canonical shadow-model cofiber-style package for a threshold cut. -/
def cofiberSequence (cut : CanonicalThresholdCut r threshold) : CofiberSequenceData cut where
  lowerRecord := cut.lowerRecord
  totalRecord := r
  upperRecord := cut.upperRecord
  lowerToTotal := cut.lowerEmbedding
  totalToUpper := cut.upperProjection
  lowerProjectionVanishes := cut.upperProjection_lowerEmbedding
  upperProjectionSplits := cut.upperProjection_upperEmbedding

/-- In the shadow model, the canonical projection identifies the complementary
upper block on the nose. -/
theorem cofiberIdentifiesUpper (cut : CanonicalThresholdCut r threshold)
    (i : Fin (n - threshold)) :
    (cut.cofiberSequence.totalToUpper (cut.upperEmbedding i)) = some i :=
  cut.cofiberSequence.upperProjectionSplits i

end CanonicalThresholdCut

/-! ### Connecting C1 to the trace produced by reconstruction

Per the user instruction of 2026-04-23 (cycle 3): connect the C1-completed
record to the actual output of `reconstruct` via a minimal honest predicate.

**Slice scope** (per the anti-impersonation rule): the predicate captures the
*combinatorial topological-ordering* content of correctness — the trace
enumerates packets and respects declared dependencies — which is the slice
shadow of the manuscript's claim that the algorithm produces a deterministic
trace realizing `∂*`. It does **not** address certified-trace admissibility,
gluing semantics, completion conditions C2/C3/C4, or the manuscript's
`Glue`/`Attach` payload. -/

/-- A trace `tr` satisfies the slice requirements of a C1-completed record `r`
iff:

1. `tr.length = n` — the trace enumerates exactly the packet count;
2. each packet index `k : Fin n` appears in `tr` at position `k.val`
   (positional coverage);
3. every declared requirement `i ∈ requires j` is realized as positional
   precedence: there exist trace positions `ki < kj` with
   `tr[ki]? = some i.val` and `tr[kj]? = some j.val`.

In the slice, conditions (1)+(2) say `tr` is `List.range n` exactly. Condition
(3) is then automatic from C1 + upper-triangularity, but it is the substantive
"requirements are respected by the trace" claim and is recorded as its own
field rather than left as an `iff`-derivable corollary. -/
structure TraceSatisfiesRequirements {n : Nat}
    (r : CompletedRecord n) (tr : Trace) : Prop where
  /-- The trace enumerates exactly the packet count. -/
  length    : tr.length = n
  /-- Each packet index appears at its own position. -/
  positions : ∀ (k : Fin n), tr.get? k.val = some k.val
  /-- Every declared requirement is realized as positional precedence. -/
  realized  : ∀ (j i : Fin n), i ∈ r.requires j →
    ∃ ki kj : Nat, ki < kj ∧ tr.get? ki = some i.val ∧ tr.get? kj = some j.val

namespace TraceSatisfiesRequirements

/-- **Scope: empty case.** The empty trace satisfies the empty record's
requirements vacuously. -/
theorem empty (r : CompletedRecord 0) :
    TraceSatisfiesRequirements r [] where
  length      := rfl
  positions k := k.elim0
  realized j _ _ := j.elim0

/-- **Scope: sink-step preservation under `reattach`.**
If `tr` satisfies the predecessor's requirements, then `reattach _ n tr` —
which in the slice is `tr ++ [n]` — satisfies the original record's
requirements. This is the slice analogue of the inductive step in the proof
that the canonical reconstruction produces a topologically-ordered enumeration
of packets. -/
theorem sink_step
    {n : Nat} (r : CompletedRecord (n+1)) (tr : Trace)
    (h : TraceSatisfiesRequirements r.predecessor tr) :
    TraceSatisfiesRequirements r
      (reattach r.predecessor.toReconstructionRecord n tr) := by
  -- `reattach _ n tr` definitionally equals `tr ++ [n]`.
  show TraceSatisfiesRequirements r (tr ++ [n])
  have hlen_tr : tr.length = n := h.length
  have hlen : (tr ++ [n]).length = n + 1 := by
    rw [List.length_append, hlen_tr]; rfl
  -- Positional coverage on `tr ++ [n]`: split on whether the index lands in
  -- `tr` (carry across via `h.positions`) or at the appended slot (compute).
  have hpos : ∀ (k : Fin (n+1)), (tr ++ [n]).get? k.val = some k.val := by
    intro k
    rcases Nat.lt_or_ge k.val n with hk | hk
    · -- index in `tr`
      have hk_tr : k.val < tr.length := hlen_tr ▸ hk
      rw [List.get?_append hk_tr]
      exact h.positions ⟨k.val, hk⟩
    · -- index = n (the appended slot), since k.val < n+1
      have hkv : k.val = n :=
        Nat.le_antisymm (Nat.lt_succ_iff.mp k.isLt) hk
      rw [hkv, List.get?_append_right hlen_tr.le, hlen_tr, Nat.sub_self]
      rfl
  refine ⟨hlen, hpos, ?_⟩
  -- Realization: by C1 + upper-triangularity, `i.val < j.val`. Then `hpos`
  -- supplies the witness positions `ki := i.val` and `kj := j.val`.
  intro j i hi
  have hedge := r.c1 j i hi
  have hlt   := r.dep.upper i j hedge
  exact ⟨i.val, j.val, hlt, hpos i, hpos j⟩

/-- **Scope: correctness of `reconstruct` against slice-C1 requirements.**
The trace produced by canonical-sink-peel reconstruction satisfies the slice's
requirements predicate. By induction on the packet count, using `empty` for
the base case and `sink_step` for the inductive case.

This is the slice analogue of the manuscript's correctness claim that
`thm:canonical-reconstruction-algorithm` produces a trace realizing `∂*`.
**It is not the full theorem** — see file docstring items 1–7 for what is
still elided. -/
theorem reconstruct :
    ∀ {n : Nat} (r : CompletedRecord n),
      TraceSatisfiesRequirements r
        (TraceCalc.LayerB.ShadowModel.reconstruct r.toReconstructionRecord)
  | 0,     r => empty r
  | _ + 1, r => sink_step r _ (reconstruct r.predecessor)

end TraceSatisfiesRequirements

/-! ### Permutation-style correctness predicate

Per the user instruction of 2026-04-23 (cycle 4): replace the strong
`positions` clause (which fixes `tr` to the exact identity ordering
`[0,1,…,n-1]`) with a more semantic predicate that says only

* the trace lists each packet exactly once (it is a permutation of
  `{0,…,n-1}`), and
* declared dependencies are respected by relative order in the trace
  (if `i ∈ requires j` then every occurrence of `i.val` precedes every
  occurrence of `j.val`).

This predicate does **not** bake in the choice that `Key = id`; in
particular, any permutation of the trace that respects dependencies would
satisfy it. The reconstruction algorithm of this slice happens to produce
the identity-ordered permutation, but the predicate does not require that.

**Slice scope** (per the anti-impersonation rule): this is still
correctness for the *normalized serialization model* — a packet is its
index, dependencies are upper-triangular `Bool` adjacency, and the trace
is `List Nat`. It is closer to the manuscript's "deterministic trace
realizing `∂*`" than `TraceSatisfiesRequirements` was, but it remains
silent on certified-trace admissibility, gluing semantics, completion
conditions C2/C3/C4, and the tensor-factorization branch. -/

/-- `reconstruct` always produces the canonical key-order list. The
permutation-style theorem below is *derived* from this fact via
`TraceIsValidReconstruction.of_reconstruct`; one could instead establish
the permutation predicate without reference to the identity ordering by
inducting directly on the algorithm, but going through this lemma is the
shortest honest route given the current representation choices. -/
theorem reconstruct_eq_range :
    ∀ {n : Nat} (r : ReconstructionRecord n),
      reconstruct r = List.range n
  | 0,     _ => rfl
  | n+1,   r => by
      change reattach r.predecessor n (reconstruct r.predecessor) = List.range (n+1)
      rw [reconstruct_eq_range r.predecessor, List.range_succ]
      rfl

/-- Helper: `(List.range n).get? k = some k` when `k < n`.

Proved by induction on `n` to avoid relying on a particular API name in
mathlib (where `List.get?_range` is sometimes only available under its
deprecated name). -/
private theorem range_get?_self : ∀ (n k : Nat), k < n →
    (List.range n).get? k = some k
  | 0,     _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, k, h => by
      rw [List.range_succ]
      have hkn : k ≤ n := Nat.lt_succ_iff.mp h
      rcases Nat.lt_or_eq_of_le hkn with hk | hk
      · -- index falls in `List.range n`
        have hk_len : k < (List.range n).length := by
          rw [List.length_range]; exact hk
        rw [List.get?_append hk_len]
        exact range_get?_self n k hk
      · -- index = n (the appended slot)
        subst hk
        have hge : (List.range k).length ≤ k := by rw [List.length_range]
        rw [List.get?_append_right hge, List.length_range, Nat.sub_self]
        rfl

/-- Helper inverse: if `(List.range n).get? k = some v`, then `k = v` and
`k < n`. -/
private theorem range_get?_eq_some {n k v : Nat}
    (h : (List.range n).get? k = some v) : k = v ∧ k < n := by
  by_cases hk : k < n
  · refine ⟨?_, hk⟩
    have := range_get?_self n k hk
    rw [this] at h
    exact (Option.some_inj.mp h)
  · exfalso
    push_neg at hk
    have hge : (List.range n).length ≤ k := by rw [List.length_range]; exact hk
    rw [List.get?_eq_none.mpr hge] at h
    exact Option.noConfusion h

/-- Permutation-style trace correctness predicate.

A trace `tr` is a *valid reconstruction* of a C1-completed record `r` iff
it permutes the packet indices and respects all declared requirements by
relative order. Compared to `TraceSatisfiesRequirements` (which fixes
`tr` to the exact identity listing), this predicate decouples
"correctness" from the slice's specific normalization choice. -/
structure TraceIsValidReconstruction {n : Nat}
    (r : CompletedRecord n) (tr : Trace) : Prop where
  /-- The trace has length `n`. -/
  length   : tr.length = n
  /-- Each entry appears at most once (no duplicate packets). -/
  nodup    : tr.Nodup
  /-- Every packet index appears in the trace (coverage). -/
  covers   : ∀ k : Fin n, k.val ∈ tr
  /-- Declared requirements are respected by relative order: every
  occurrence of `i.val` strictly precedes every occurrence of `j.val`
  whenever `i ∈ requires j`. -/
  respects : ∀ (j i : Fin n), i ∈ r.requires j →
             ∀ (ki kj : Nat),
               tr.get? ki = some i.val →
               tr.get? kj = some j.val →
               ki < kj

namespace TraceIsValidReconstruction

/-- **Scope: correctness of `reconstruct` against the permutation-style
predicate.**

Derived from `reconstruct_eq_range` plus `range_get?_self`/`range_get?_eq_some`.
The proof is essentially: `reconstruct r = List.range n`, hence the trace
is `[0,…,n-1]`, which is nodup and contains every `k < n`; the `respects`
clause then reduces, on positional witnesses, to `i.val < j.val`, which
follows from C1 + upper-triangularity.

This is the slice analogue of *"the canonical reconstruction algorithm
returns a deterministic trace realizing `∂*`"* (manuscript L1149),
restricted to the normalized serialization model. It does **not** claim
the manuscript's full reconstruction theorem — see the file docstring
items 1–7 for what is still elided. -/
theorem of_reconstruct {n : Nat} (r : CompletedRecord n) :
    TraceIsValidReconstruction r
      (TraceCalc.LayerB.ShadowModel.reconstruct r.toReconstructionRecord) := by
  have hrange : TraceCalc.LayerB.ShadowModel.reconstruct r.toReconstructionRecord
                  = List.range n := reconstruct_eq_range r.toReconstructionRecord
  refine
    { length := ?_
      nodup := ?_
      covers := ?_
      respects := ?_ }
  · rw [hrange, List.length_range]
  · rw [hrange]; exact List.nodup_range n
  · intro k
    rw [hrange, List.mem_range]
    exact k.isLt
  · intro j i hi ki kj hki hkj
    rw [hrange] at hki hkj
    obtain ⟨hki_eq, _⟩ := range_get?_eq_some hki
    obtain ⟨hkj_eq, _⟩ := range_get?_eq_some hkj
    -- `hki_eq : ki = i.val`, `hkj_eq : kj = j.val`
    rw [hki_eq, hkj_eq]
    exact r.dep.upper i j (r.c1 j i hi)

end TraceIsValidReconstruction

/-! ### Tensor-factorization branch (binary slice)

Per the user instruction of 2026-04-23 (cycle 5): open the
tensor-factorization branch of `thm:canonical-reconstruction-algorithm`.
The minimal honest content is *not* a re-recursion of the algorithm along
weakly-connected components, but the **structural correctness statement**
that motivates such a recursion: a vertex partition with no cross-side
required-input lifts independent valid reconstructions of the two sides
to a valid reconstruction of the whole, by concatenation.

This is **strictly stronger** than `TraceIsValidReconstruction.of_reconstruct`:
for a record whose dependency graph splits into two non-interacting
components, this theorem produces additional valid reconstructions besides
the canonical key-order one. It is the slice form of clause (d) of
`thm:tensor-factor-independence` (manuscript L1278) — "Reconstruction
commutes with tensoring" — restricted to the binary case in the normalized
serialization model.

**Slice scope** (per the anti-impersonation rule):

* binary partition, not the manuscript's full WCC decomposition;
* only `requires`-side cross-flow is hypothesized as absent (the
  combinatorially relevant condition for the slice's `respects` clause);
  a faithful version once payload/gluing exist will additionally need
  `NoCrossDependencies`, port-typing, and the manuscript's full Step 1
  recursion;
* "tensoring" of traces is realized as `List.append` — there is no
  monoidal symmetry data, no `⊗` constructor, and no claim about reordering
  factors.
-/

/-- A trace `tr` covers a subset `s ⊆ Fin n` of a C1-completed record
`r` iff it permutes exactly the indices in `s` and respects every
within-`s` requirement by relative order. This is the per-component
analogue of `TraceIsValidReconstruction` for the binary-tensor slice. -/
structure TraceCoversSubset {n : Nat}
    (r : CompletedRecord n) (s : Finset (Fin n)) (tr : Trace) : Prop where
  length    : tr.length = s.card
  nodup     : tr.Nodup
  covers    : ∀ i ∈ s, i.val ∈ tr
  in_subset : ∀ x ∈ tr, ∃ i ∈ s, x = i.val
  respects  : ∀ (j i : Fin n), i ∈ s → j ∈ s → i ∈ r.requires j →
              ∀ ki kj, tr.get? ki = some i.val → tr.get? kj = some j.val → ki < kj

namespace TraceIsValidReconstruction

/-- **Scope: binary tensor-factorization preserves valid reconstruction
(slice form of `thm:tensor-factor-independence` clause (d), L1278).**

If `Fin n = sA ⊔ sB` (disjoint, covering) and no required-input crosses
the partition in either direction, then concatenating valid coverings of
the two sides yields a valid reconstruction of the whole.

**Note on hypotheses.** In this slice only `hcrossBA` is load-bearing:
the `i ∈ trA, j ∈ trB` case of `respects` is automatic from positions
(`ki < trA.length ≤ kj`), so the analogous `hcrossAB` direction is not
needed. We retain `hcrossAB` in the signature because (i) it makes the
hypothesis symmetric and (ii) once `NoCrossDependencies` is added, the
edge-direction analogue of this case will require it. -/
theorem of_concat
    {n : Nat} {r : CompletedRecord n}
    {sA sB : Finset (Fin n)}
    (hcover   : sA ∪ sB = Finset.univ)
    (hdisj    : Disjoint sA sB)
    (hcrossAB : ∀ (j i : Fin n), i ∈ sA → j ∈ sB → i ∉ r.requires j)
    (hcrossBA : ∀ (j i : Fin n), i ∈ sB → j ∈ sA → i ∉ r.requires j)
    {trA trB : Trace}
    (hA : TraceCoversSubset r sA trA)
    (hB : TraceCoversSubset r sB trB) :
    TraceIsValidReconstruction r (trA ++ trB) := by
  -- Length: |sA| + |sB| = n.
  have hsum : sA.card + sB.card = n := by
    have hu : (sA ∪ sB).card = n := by
      rw [hcover, Finset.card_univ, Fintype.card_fin]
    rw [Finset.card_union_of_disjoint hdisj] at hu
    exact hu
  have hlen : (trA ++ trB).length = n := by
    rw [List.length_append, hA.length, hB.length, hsum]
  -- Nodup: both sides nodup, and disjoint by `Fin.val`-injectivity + `hdisj`.
  have hnd : (trA ++ trB).Nodup := by
    rw [List.nodup_append]
    refine ⟨hA.nodup, hB.nodup, ?_⟩
    intro x hxA hxB
    obtain ⟨i, hiA, hxi⟩ := hA.in_subset x hxA
    obtain ⟨j, hjB, hxj⟩ := hB.in_subset x hxB
    have hij : i = j := Fin.val_injective (hxi.symm.trans hxj)
    subst hij
    exact (Finset.disjoint_left.mp hdisj) hiA hjB
  -- Covers: every k : Fin n is in sA ∪ sB = univ, so its val is in some side.
  have hcov : ∀ k : Fin n, k.val ∈ trA ++ trB := by
    intro k
    have hk : k ∈ sA ∪ sB := by rw [hcover]; exact Finset.mem_univ k
    rw [Finset.mem_union] at hk
    rw [List.mem_append]
    cases hk with
    | inl h => exact Or.inl (hA.covers k h)
    | inr h => exact Or.inr (hB.covers k h)
  -- Respects: case-split on which side ki and kj land on.
  have hresp : ∀ (j i : Fin n), i ∈ r.requires j →
      ∀ ki kj, (trA ++ trB).get? ki = some i.val →
                (trA ++ trB).get? kj = some j.val → ki < kj := by
    intro j i hi ki kj hki hkj
    by_cases hkiA : ki < trA.length
    · -- ki lands in trA
      rw [List.get?_append hkiA] at hki
      have hi_mem : i.val ∈ trA := List.get?_mem hki
      obtain ⟨i', hi'A, hi'eq⟩ := hA.in_subset i.val hi_mem
      have : i = i' := Fin.val_injective hi'eq
      subst this
      by_cases hkjA : kj < trA.length
      · -- both in trA
        rw [List.get?_append hkjA] at hkj
        have hj_mem : j.val ∈ trA := List.get?_mem hkj
        obtain ⟨j', hj'A, hj'eq⟩ := hA.in_subset j.val hj_mem
        have : j = j' := Fin.val_injective hj'eq
        subst this
        exact hA.respects j i hi'A hj'A hi ki kj hki hkj
      · -- ki in trA, kj in trB ⇒ ki < trA.length ≤ kj
        push_neg at hkjA
        omega
    · -- ki lands in trB
      push_neg at hkiA
      rw [List.get?_append_right hkiA] at hki
      have hi_mem : i.val ∈ trB := List.get?_mem hki
      obtain ⟨i', hi'B, hi'eq⟩ := hB.in_subset i.val hi_mem
      have : i = i' := Fin.val_injective hi'eq
      subst this
      by_cases hkjA : kj < trA.length
      · -- ki in trB, kj in trA: requirement crosses sB → sA, contradiction
        rw [List.get?_append hkjA] at hkj
        have hj_mem : j.val ∈ trA := List.get?_mem hkj
        obtain ⟨j', hj'A, hj'eq⟩ := hA.in_subset j.val hj_mem
        have : j = j' := Fin.val_injective hj'eq
        subst this
        exact absurd hi (hcrossBA j i hi'B hj'A)
      · -- both in trB
        push_neg at hkjA
        rw [List.get?_append_right hkjA] at hkj
        have hj_mem : j.val ∈ trB := List.get?_mem hkj
        obtain ⟨j', hj'B, hj'eq⟩ := hB.in_subset j.val hj_mem
        have : j = j' := Fin.val_injective hj'eq
        subst this
        have hsub :
            ki - trA.length < kj - trA.length :=
          hB.respects j i hi'B hj'B hi (ki - trA.length) (kj - trA.length) hki hkj
        omega
  exact { length := hlen, nodup := hnd, covers := hcov, respects := hresp }

end TraceIsValidReconstruction

end ShadowModel
end LayerB
end TraceCalc

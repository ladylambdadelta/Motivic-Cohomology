import TraceCalc.LayerB.RealObjects.CompletedRecord
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.OfFn
import Mathlib.Order.Basic

/-!
# Real-objects formalization: sink peeling preserves completedness

**Real-objects path, cycle 6 (2026-04-23).**

This file faithfully encodes:

* The notion of a **sink** in the dependence DAG of a completed
  reconstruction record (informal in `our_paper_draft.tex` L1149,
  L1155, L1186; the manuscript uses "sink" to mean a vertex with no
  outgoing dependence edges).
* The **predecessor subrecord** `∂*\s` of
  `lem:sink-peel-preserves-completedness` (`our_paper_draft.tex` L1191):
  the eight-tuple obtained by removing a sink `s` from a completed
  reconstruction record.
* The manuscript-tagged lemma
  `lem:sink-peel-preserves-completedness` (L1191), proved against the
  real `IsCompleted` predicate of cycle 2.

## Honesty about the encoded content (Phase 3A item 2 closure)

As of Phase 3A item 2 sub-items 1, 2, 3 (2026-04-23), all three of the
manuscript's predecessor-subrecord components — `Y_s`
(`def:boundary-exposure`, L1211/L1224), `Tensor'` (L1196), and `Key'`
(L1196) — are built **intrinsically** from `R` and `s` with no
auxiliary input:

* `Key'` ↔ `restrictedKey R s : CanonicalKey (R.n - 1)`, built by
  deleting `R.key.pos s`'s slot from `R.key.pos` and renumbering.
  Manuscript clause (b) of `prop:key-total-injective` (L1146) is
  recovered by `restrictedKey_compatible_with_restrictedDep` from
  `R.IsCompleted.c4`.
* `Y_s` ↔ `restrictedY R s : setup.BoundaryObject`, built directly
  from `setup.exposeBoundaryUnderSinkDeletion` applied to the
  manuscript's three numbered inputs. The `externalOut` companion
  list `restrictedExternalOut R s` is the additive content of step
  (ii); see its docstring for the auxiliary/display caveat at the
  abstract setup level.
* `Tensor'` ↔ `restrictedTensor R s : TensorDecomposition (R.n - 1)`,
  built by enumerating `(restrictedDep R s).WCC`-classes through
  `List.ofFn`. The manuscript's C3' shape is discharged by
  `restrictedTensor_isWCCDecomp`, with no auxiliary input.

Consequently the auxiliary `PredecessorData` structure is **gone**;
`peelSink R s : CompletedReconstructionRecord setup` is a pure
function of `R` and `s`, and
`sink_peel_preserves_completedness` takes only `hSink` and `hC`.

The substantive content of `lem:sink-peel-preserves-completedness` is
clause C1' (every refined input still matched after sink removal), and
the proof here is the genuine manuscript proof: a remaining packet
`j` cannot have consumed an output of `s` because `s` is a sink.

## Namespace

Everything lives under `TraceCalc.LayerB.RealObjects`.
-/

universe u

namespace TraceCalc
namespace LayerB
namespace RealObjects

namespace RewriteCalculusSetup

/-! ### Sink predicate -/

/-- A vertex `s` is a **sink** in a `DepGraph` iff it has no outgoing
dependence edge. Faithful to the manuscript's informal usage at
`our_paper_draft.tex` L1155 ("vertices with no outgoing edge") and
L1186 ("Removing a sink from a DAG yields a DAG"). -/
def DepGraph.IsSink {n : Nat} (G : DepGraph n) (s : Fin n) : Prop :=
  ∀ j : Fin n, G.edge s j = false

namespace CompletedReconstructionRecord

variable {setup : RewriteCalculusSetup.{u}}

/-- The dependence sink predicate lifted to a completed reconstruction
record. -/
def IsSink (R : CompletedReconstructionRecord setup) (s : Fin R.n) : Prop :=
  R.dep.IsSink s

/-! ### Index-skipping embedding `Fin (R.n - 1) → Fin R.n`

We embed `Fin (R.n - 1)` into `Fin R.n` skipping the index `s`. This is
the manuscript's `Packets \ {s}` re-enumeration. We define it
explicitly: `embedSkip s i = i` if `i < s`, else `i + 1`. -/

/-- Embedding of `Fin (R.n - 1)` into `Fin R.n` skipping the sink `s`. -/
def embedSkip {n : Nat} (s : Fin n) (i : Fin (n - 1)) : Fin n :=
  if h : i.val < s.val then
    ⟨i.val, Nat.lt_of_lt_of_le h (Nat.le_of_lt s.isLt)⟩
  else
    ⟨i.val + 1, by
      have hi : i.val < n - 1 := i.isLt
      have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) s.isLt
      omega⟩

/-- Equation lemma for `embedSkip` in the lower half. -/
lemma embedSkip_lt {n : Nat} (s : Fin n) (i : Fin (n - 1))
    (h : i.val < s.val) :
    (embedSkip s i).val = i.val := by
  unfold embedSkip; simp [h]

/-- Equation lemma for `embedSkip` in the upper half. -/
lemma embedSkip_ge {n : Nat} (s : Fin n) (i : Fin (n - 1))
    (h : ¬ i.val < s.val) :
    (embedSkip s i).val = i.val + 1 := by
  unfold embedSkip; simp [h]

/-- The embedding `embedSkip s` never lands on `s`. -/
lemma embedSkip_ne {n : Nat} (s : Fin n) (i : Fin (n - 1)) :
    embedSkip s i ≠ s := by
  intro heq
  by_cases h : i.val < s.val
  · have := embedSkip_lt s i h
    rw [heq] at this
    omega
  · have := embedSkip_ge s i h
    rw [heq] at this
    omega

/-- Inverse of `embedSkip` for indices `i < s`. -/
def predIndexLt {n : Nat} (s : Fin n) (i : Fin n) (hlt : i.val < s.val) :
    Fin (n - 1) :=
  ⟨i.val, by
    have : s.val ≤ n - 1 := by
      have : s.val + 1 ≤ n := s.isLt
      omega
    omega⟩

/-- Inverse of `embedSkip` for indices `i > s`. -/
def predIndexGt {n : Nat} (s : Fin n) (i : Fin n) (hgt : s.val < i.val) :
    Fin (n - 1) :=
  ⟨i.val - 1, by
    have := i.isLt
    omega⟩

lemma embedSkip_predIndexLt {n : Nat} (s : Fin n) (i : Fin n)
    (hlt : i.val < s.val) :
    embedSkip s (predIndexLt s i hlt) = i := by
  apply Fin.ext
  show (embedSkip s (predIndexLt s i hlt)).val = i.val
  rw [embedSkip_lt _ _ (show (predIndexLt s i hlt).val < s.val from hlt)]
  rfl
lemma embedSkip_predIndexGt {n : Nat} (s : Fin n) (i : Fin n)
    (hgt : s.val < i.val) :
    embedSkip s (predIndexGt s i hgt) = i := by
  apply Fin.ext
  have hnotlt : ¬ ((predIndexGt s i hgt).val < s.val) := by
    show ¬ (i.val - 1 < s.val)
    omega
  rw [embedSkip_ge _ _ hnotlt]
  show i.val - 1 + 1 = i.val
  omega

/-! ### Restricted dependence DAG -/

/-- The dependence DAG of the predecessor subrecord: restriction of
`R.dep` to indices skipping `s`. -/
def restrictedDep (R : CompletedReconstructionRecord setup)
    (s : Fin R.n) : DepGraph (R.n - 1) where
  edge i j := R.dep.edge (embedSkip s i) (embedSkip s j)
  acyclic := by
    intro i hcyc
    apply R.dep.acyclic (embedSkip s i)
    have lift :
        ∀ {a b : Fin (R.n - 1)},
          Relation.TransGen
            (fun a' b' : Fin (R.n - 1) =>
              R.dep.edge (embedSkip s a') (embedSkip s b') = true) a b →
          Relation.TransGen
            (fun a' b' : Fin R.n => R.dep.edge a' b' = true)
            (embedSkip s a) (embedSkip s b) := by
      intro a b h
      induction h with
      | single h => exact Relation.TransGen.single h
      | tail _ h ih => exact Relation.TransGen.tail ih h
    exact lift hcyc

/-! ### `embedSkip` is injective -/

/-- The index-skipping embedding `Fin (n-1) → Fin n` is injective. -/
lemma embedSkip_injective {n : Nat} (s : Fin n) :
    Function.Injective (embedSkip s) := by
  intro i j hij
  by_cases hi : i.val < s.val
  · by_cases hj : j.val < s.val
    · have := congrArg Fin.val hij
      simp [embedSkip, hi, hj] at this
      exact Fin.ext this
    · have := congrArg Fin.val hij
      simp [embedSkip, hi, hj] at this
      omega
  · by_cases hj : j.val < s.val
    · have := congrArg Fin.val hij
      simp [embedSkip, hi, hj] at this
      omega
    · have := congrArg Fin.val hij
      simp [embedSkip, hi, hj] at this
      have heq : i.val = j.val := by omega
      exact Fin.ext heq

/-! ### Intrinsic restricted canonical key

For `i : Fin (R.n - 1)`, look up `R.key.pos (embedSkip s i)`. Since
`R.key.pos` is injective and `embedSkip s i ≠ s`, this value is
always different from `R.key.pos s`. Delete `R.key.pos s` from the
range `Fin R.n` and renumber: values strictly below `R.key.pos s`
stay; values strictly above are shifted down by one. -/

/-- The key position of the embedded non-sink packet is never equal
to the sink's key position. -/
lemma key_pos_embed_ne_sink (R : CompletedReconstructionRecord setup)
    (s : Fin R.n) (i : Fin (R.n - 1)) :
    R.key.pos (embedSkip s i) ≠ R.key.pos s := by
  intro h
  exact embedSkip_ne s i (R.key.total h)

/-- The renumbered key position. Defined by case-split on whether
`R.key.pos (embedSkip s i)` falls below or above `R.key.pos s`. -/
def restrictedKeyPos (R : CompletedReconstructionRecord setup)
    (s : Fin R.n) (i : Fin (R.n - 1)) : Fin (R.n - 1) :=
  let p := R.key.pos (embedSkip s i)
  if hlt : p.val < (R.key.pos s).val then
    ⟨p.val, Nat.lt_of_lt_of_le hlt (Nat.le_pred_of_lt (R.key.pos s).isLt)⟩
  else
    ⟨p.val - 1, by
      have hne : p.val ≠ (R.key.pos s).val := fun h =>
        key_pos_embed_ne_sink R s i (Fin.ext h)
      have hgt : (R.key.pos s).val < p.val :=
        lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne)
      have hpval : p.val < R.n := p.isLt
      have : p.val - 1 < R.n - 1 := by omega
      exact this⟩

/-- Clause (a) of `prop:key-total-injective` (L1146) — total
(= `Function.Injective restrictedKeyPos`). -/
lemma restrictedKeyPos_injective (R : CompletedReconstructionRecord setup)
    (s : Fin R.n) :
    Function.Injective (restrictedKeyPos R s) := by
  intro i j hij
  set pi := R.key.pos (embedSkip s i)
  set pj := R.key.pos (embedSkip s j)
  set ps := R.key.pos s
  have hi_ne : pi.val ≠ ps.val := fun h =>
    key_pos_embed_ne_sink R s i (Fin.ext h)
  have hj_ne : pj.val ≠ ps.val := fun h =>
    key_pos_embed_ne_sink R s j (Fin.ext h)
  have hij_val :
      (restrictedKeyPos R s i).val = (restrictedKeyPos R s j).val := by
    rw [hij]
  have hpi : pi.val = pj.val := by
    by_cases hi : pi.val < ps.val
    · by_cases hj : pj.val < ps.val
      · simp [restrictedKeyPos, hi, hj] at hij_val; exact hij_val
      · have hjgt : ps.val < pj.val :=
          lt_of_le_of_ne (not_lt.mp hj) (Ne.symm hj_ne)
        simp [restrictedKeyPos, hi, hj] at hij_val
        omega
    · by_cases hj : pj.val < ps.val
      · have hibig : ps.val < pi.val :=
          lt_of_le_of_ne (not_lt.mp hi) (Ne.symm hi_ne)
        simp [restrictedKeyPos, hi, hj] at hij_val
        omega
      · have hibig : ps.val < pi.val :=
          lt_of_le_of_ne (not_lt.mp hi) (Ne.symm hi_ne)
        have hjbig : ps.val < pj.val :=
          lt_of_le_of_ne (not_lt.mp hj) (Ne.symm hj_ne)
        simp [restrictedKeyPos, hi, hj] at hij_val
        omega
  have hpi_eq : pi = pj := Fin.ext hpi
  have hembed : embedSkip s i = embedSkip s j := R.key.total hpi_eq
  exact embedSkip_injective s hembed

/-- Clause (c) of `prop:key-total-injective` (L1146) — bijective. -/
lemma restrictedKeyPos_bijective (R : CompletedReconstructionRecord setup)
    (s : Fin R.n) :
    Function.Bijective (restrictedKeyPos R s) :=
  Finite.injective_iff_bijective.mp (restrictedKeyPos_injective R s)

/-- **Intrinsic restricted canonical key** — `def:completed-reconstruction-record`
clause (f) (`our_paper_draft.tex` L1120) for the predecessor record
`∂*\s` (L1196), built intrinsically from `R.key` and `s` with no
auxiliary data. -/
def restrictedKey (R : CompletedReconstructionRecord setup)
    (s : Fin R.n) : CanonicalKey (R.n - 1) where
  pos := restrictedKeyPos R s
  total := restrictedKeyPos_injective R s
  bijective := restrictedKeyPos_bijective R s

/-- The renumbering preserves strict inequalities: if `pi < pj` as
key positions in `R`, with neither equal to `R.key.pos s`, then their
renumbered images are strictly ordered. -/
private lemma restrictedKeyPos_lt_of_pi_lt_pj
    (R : CompletedReconstructionRecord setup) (s : Fin R.n)
    (i j : Fin (R.n - 1))
    (hpi_lt_pj :
      (R.key.pos (embedSkip s i)).val < (R.key.pos (embedSkip s j)).val) :
    restrictedKeyPos R s i < restrictedKeyPos R s j := by
  set pi := R.key.pos (embedSkip s i)
  set pj := R.key.pos (embedSkip s j)
  set ps := R.key.pos s
  have hi_ne : pi.val ≠ ps.val := fun h =>
    key_pos_embed_ne_sink R s i (Fin.ext h)
  have hj_ne : pj.val ≠ ps.val := fun h =>
    key_pos_embed_ne_sink R s j (Fin.ext h)
  show (restrictedKeyPos R s i).val < (restrictedKeyPos R s j).val
  by_cases hi : pi.val < ps.val
  · by_cases hj : pj.val < ps.val
    · simp [restrictedKeyPos, hi, hj]; exact hpi_lt_pj
    · simp [restrictedKeyPos, hi, hj]
      have hpj_gt : ps.val < pj.val :=
        lt_of_le_of_ne (not_lt.mp hj) (Ne.symm hj_ne)
      omega
  · by_cases hj : pj.val < ps.val
    · have hi_ge : ps.val ≤ pi.val :=
        le_of_lt (lt_of_le_of_ne (not_lt.mp hi) (Ne.symm hi_ne))
      omega
    · simp [restrictedKeyPos, hi, hj]
      have hpi_gt : ps.val < pi.val :=
        lt_of_le_of_ne (not_lt.mp hi) (Ne.symm hi_ne)
      have hpj_gt : ps.val < pj.val :=
        lt_of_le_of_ne (not_lt.mp hj) (Ne.symm hj_ne)
      omega

/-- **Manuscript clause (b)** for the intrinsic restricted key
(`prop:key-total-injective` L1146). Conditional on the original
record's `IsCompleted.c4` (the canonical key's monotonicity along
`R.dep`), the restricted key is monotone along `restrictedDep R s`. -/
lemma restrictedKey_compatible_with_restrictedDep
    (R : CompletedReconstructionRecord setup) (s : Fin R.n)
    (hc4 :
      ∀ i j : Fin R.n,
        R.dep.edge i j = true → R.key.pos i < R.key.pos j) :
    (restrictedKey R s).IsCompatibleWith (restrictedDep R s) := by
  intro i j hEdge
  have hRedge : R.dep.edge (embedSkip s i) (embedSkip s j) = true := hEdge
  have hpos_lt :
      R.key.pos (embedSkip s i) < R.key.pos (embedSkip s j) :=
    hc4 (embedSkip s i) (embedSkip s j) hRedge
  exact restrictedKeyPos_lt_of_pi_lt_pj R s i j hpos_lt

/-! ### Intrinsic restricted tensor decomposition

**Phase 3A item 2 sub-item 3 (2026-04-23).** Discharges the *third*
(and final) of the three manuscript-clarity flags on the (now-retired)
`PredecessorData`: `Tensor'` of L1196 is built **intrinsically** as
the canonical WCC factorization of `restrictedDep R s`.

`TensorDecomposition.blocks` is `List (Fin n → Prop)` — each block is
a membership predicate, NOT a finite enumeration. This is exactly the
shape needed: we list one block per index `i : Fin (R.n - 1)`, where
each block is the predicate `fun j => (restrictedDep R s).WCC i j`.
Duplicates are mathematically harmless (the C3 condition only requires
*surjectivity onto WCC classes* and *every block is some WCC class*,
both satisfied with arbitrary multiplicity). The construction needs
**no decidability hypothesis** on `RefinedInterface`, on the WCC
relation, or on anything else. -/

/-- **Intrinsic restricted tensor decomposition** for the predecessor
record `∂*\s` of `lem:sink-peel-preserves-completedness` L1191:
the canonical WCC factorization of `restrictedDep R s`. -/
def restrictedTensor (R : CompletedReconstructionRecord setup)
    (s : Fin R.n) : TensorDecomposition (R.n - 1) where
  blocks :=
    List.ofFn
      (fun i : Fin (R.n - 1) =>
        fun j : Fin (R.n - 1) => (restrictedDep R s).WCC i j)

/-- **Manuscript C3' shape** for the intrinsic restricted tensor: the
two halves of `IsCompleted.c3` ("every block is a WCC class" and
"every vertex lies in some block") hold definitionally for
`restrictedTensor R s`. No hypothesis needed. -/
lemma restrictedTensor_isWCCDecomp
    (R : CompletedReconstructionRecord setup) (s : Fin R.n) :
    (∀ (B : Fin (R.n - 1) → Prop), B ∈ (restrictedTensor R s).blocks →
        ∃ (i₀ : Fin (R.n - 1)), B i₀ ∧
          ∀ (j : Fin (R.n - 1)), B j ↔ (restrictedDep R s).WCC i₀ j) ∧
    (∀ (i : Fin (R.n - 1)),
        ∃ (B : Fin (R.n - 1) → Prop),
          B ∈ (restrictedTensor R s).blocks ∧ B i) := by
  refine ⟨?_, ?_⟩
  · intro B hB
    rw [restrictedTensor, List.mem_ofFn] at hB
    obtain ⟨i, hi⟩ := hB
    refine ⟨i, ?_, ?_⟩
    · rw [← hi]; exact Relation.EqvGen.refl _
    · intro j; rw [← hi]
  · intro i
    refine ⟨fun j => (restrictedDep R s).WCC i j, ?_, ?_⟩
    · show (fun j => (restrictedDep R s).WCC i j) ∈
          (restrictedTensor R s).blocks
      rw [restrictedTensor, List.mem_ofFn]
      exact ⟨i, rfl⟩
    · exact Relation.EqvGen.refl _

/-! ### Intrinsic exposed boundary `Y'` and external-output list

**Phase 3A item 2 sub-item 2 (2026-04-23).** Discharges the *second*
of three manuscript-clarity flags on `PredecessorData`: `Y'` (and its
`externalOut'` companion list) of L1196 are now built *intrinsically*
from `R`, `s`, and the carrier-level boundary-exposure operation
`setup.exposeBoundaryUnderSinkDeletion` (`def:boundary-exposure`,
`our_paper_draft.tex` L1224).

**Manuscript reading (faithful)**: when `s` is a sink in `R.dep`,
none of `s`'s refined outputs are consumed by other packets (no
outgoing edges in `R.dep`), so `R.ports.packetOut s` lives entirely
on the boundary `R.Y` and is exactly the list to be removed
(step (i) of `def:boundary-exposure`). The newly-exposed predecessor
ports (step (ii)) are typed identically to `R.ports.packetIn s`,
because `IsCompleted.c1` matches each refined input of `s` to either
an external input or a predecessor's refined output, so removing `s`
exposes exactly that many ports of those types. Hence
`R.ports.packetIn s` is the manuscript-correct typed-list witness for
"exposedFromPredecessors". -/

/-- **Intrinsic exposed boundary** `Y_s` of `def:boundary-exposure`
(`our_paper_draft.tex` L1211/L1224). Built directly from the
carrier-level operation `setup.exposeBoundaryUnderSinkDeletion`,
applied to the original boundary `R.Y`, the sink's refined outputs
(step (i)), and the typed list of refined inputs of `s` (which by
`IsCompleted.c1` enumerates the types of the predecessor ports newly
exposed by step (ii)). -/
def restrictedY (R : CompletedReconstructionRecord setup) (s : Fin R.n) :
    setup.BoundaryObject :=
  setup.exposeBoundaryUnderSinkDeletion R.Y
    (R.ports.packetOut s) (R.ports.packetIn s)

/-- **Intrinsic external-output list** for the predecessor record.

`def:completed-reconstruction-record` carries `externalOut : List
RefinedInterface` separately from the `BoundaryObject` because the
typed-list view records the multiset of refined output slots; the
`BoundaryObject` records the boundary cirquent itself.

**At the abstract `RewriteCalculusSetup` level, the boundary-object
view (`restrictedY`) is the *theorem-bearing* object.** The typed-list
view is auxiliary/display content: the `IsCompleted` predicate (cycle
2) imposes constraints on `packetIn` / `externalIn` / `packetOut` (in
clause C1) and on `attach` / `tensor` / `key` (in C2/C3/C4), but
**makes no reference to `externalOut`** — confirming that
`externalOut` is unconstrained by the four manuscript completedness
conditions, so an additive presentation is honest.

**Definition (additive presentation).** We record only the *additive*
content of step (ii) of `def:boundary-exposure` (L1224): the
previously-exposed external outputs together with the newly-exposed
predecessor outputs (typed identically to the sink's refined inputs).
The carrier-level removal of the sink's refined outputs (step (i))
is handled exactly inside `restrictedY` via the opaque
`exposeBoundaryUnderSinkDeletion`.

**On the `DecidableEq RefinedInterface` flag (acknowledged honestly).**
The current definition uses pure list concatenation `(++)`; it does
*not* perform list-level subtraction and therefore needs no
`DecidableEq` hypothesis. A *subtractive* presentation — removing
`R.ports.packetOut s` from `R.ports.externalOut` to produce a
strict step-(i) list — would require `[DecidableEq
setup.RefinedInterface]`; concrete instantiations (e.g., the Lane B
`Bridge` which produces refined interfaces decidable in the inductive
carrier) can supply that instance and sharpen this list. Until then,
the additive presentation is the manuscript-faithful choice on the
abstract setup, and the boundary-object level remains the
theorem-bearing locus. -/
def restrictedExternalOut (R : CompletedReconstructionRecord setup)
    (s : Fin R.n) : List setup.RefinedInterface :=
  R.ports.externalOut ++ R.ports.packetIn s

/-! ### The predecessor subrecord

**Phase 3A item 2 closure (2026-04-23).** All three components
`Y_s` / `Tensor'` / `Key'` are now intrinsic; `peelSink R s` is a
pure function of `R` and `s`. -/

/-- The predecessor subrecord `∂*\s` of
`lem:sink-peel-preserves-completedness` (`our_paper_draft.tex` L1191),
built **intrinsically** from `R` and `s` alone. -/
def peelSink (R : CompletedReconstructionRecord setup)
    (s : Fin R.n) : CompletedReconstructionRecord setup where
  n := R.n - 1
  X := R.X
  Y := restrictedY R s
  ports :=
    { externalIn := R.ports.externalIn
      externalOut := restrictedExternalOut R s
      packetIn := fun i => R.ports.packetIn (embedSkip s i)
      packetOut := fun i => R.ports.packetOut (embedSkip s i) }
  packets := fun i => R.packets (embedSkip s i)
  dep := restrictedDep R s
  attach := fun i => R.attach (embedSkip s i)
  tensor := restrictedTensor R s
  key := restrictedKey R s

/-! ### The manuscript-tagged lemma -/

/-- **`lem:sink-peel-preserves-completedness`** (`our_paper_draft.tex`
L1191): if `R` is a completed reconstruction record and `s` is a sink
in its dependence DAG, then the predecessor subrecord `peelSink R s`
is again completed. **No auxiliary input.**

The substantive content (C1') uses the manuscript proof: a remaining
packet's input was not produced by the sink, so the witness lifts
through `embedSkip`. C2' is preserved against the cycle-2 placeholder.
C3' uses `restrictedTensor_isWCCDecomp`; C4' uses
`restrictedKey_compatible_with_restrictedDep` applied to `hC.c4`.

This is the **second manuscript-tagged theorem of the real-objects
path**, after `lem:trace-equivalence-congruence` (cycle 5). -/
theorem sink_peel_preserves_completedness
    {R : CompletedReconstructionRecord setup} {s : Fin R.n}
    (hSink : R.IsSink s) (hC : R.IsCompleted) :
    (peelSink R s).IsCompleted := by
  refine
    { c1 := ?c1
      c2 := ?c2
      c3 := ?c3
      c4 := ?c4 }
  · -- C1'.
    intro j r hr
    have h₀ : (r ∈ R.ports.externalIn) ∨
        (∃ i : Fin R.n, R.dep.edge i (embedSkip s j) = true ∧
            r ∈ R.ports.packetOut i) := by
      apply hC.c1 (embedSkip s j) r
      simpa [peelSink] using hr
    rcases h₀ with hExt | ⟨i, hEdge, hOut⟩
    · left
      simpa [peelSink] using hExt
    · have hi_ne : i ≠ s := by
        intro hsel
        have hfalse : R.dep.edge i (embedSkip s j) = false := by
          rw [hsel]; exact hSink (embedSkip s j)
        rw [hfalse] at hEdge
        cases hEdge
      right
      by_cases hlt : i.val < s.val
      · refine ⟨predIndexLt s i hlt, ?_, ?_⟩
        · show R.dep.edge (embedSkip s (predIndexLt s i hlt))
              (embedSkip s j) = true
          rw [embedSkip_predIndexLt]; exact hEdge
        · show r ∈ R.ports.packetOut (embedSkip s (predIndexLt s i hlt))
          rw [embedSkip_predIndexLt]; exact hOut
      · have hi_gt : s.val < i.val := by
          rcases Nat.lt_or_ge s.val i.val with h | h
          · exact h
          · exact absurd (Fin.ext (show i.val = s.val by omega)) hi_ne
        refine ⟨predIndexGt s i hi_gt, ?_, ?_⟩
        · show R.dep.edge (embedSkip s (predIndexGt s i hi_gt))
              (embedSkip s j) = true
          rw [embedSkip_predIndexGt]; exact hEdge
        · show r ∈ R.ports.packetOut (embedSkip s (predIndexGt s i hi_gt))
          rw [embedSkip_predIndexGt]; exact hOut
  · -- C2': vacuous.
    intro _; trivial
  · -- C3': intrinsic via `restrictedTensor_isWCCDecomp`.
    show (∀ (B : Fin (R.n - 1) → Prop), B ∈ (restrictedTensor R s).blocks →
        ∃ (i₀ : Fin (R.n - 1)), B i₀ ∧
          ∀ (j : Fin (R.n - 1)), B j ↔ (restrictedDep R s).WCC i₀ j) ∧
      (∀ (i : Fin (R.n - 1)),
        ∃ (B : Fin (R.n - 1) → Prop), B ∈ (restrictedTensor R s).blocks ∧ B i)
    exact restrictedTensor_isWCCDecomp R s
  · -- C4': intrinsic via `restrictedKey_compatible_with_restrictedDep`.
    intro i j hEdge
    exact restrictedKey_compatible_with_restrictedDep R s hC.c4 i j hEdge

end CompletedReconstructionRecord
end RewriteCalculusSetup

end RealObjects
end LayerB
end TraceCalc

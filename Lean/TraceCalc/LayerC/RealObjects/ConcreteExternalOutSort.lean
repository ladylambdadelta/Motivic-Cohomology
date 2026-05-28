import Mathlib.Data.List.Sort
import TraceCalc.LayerB.RealObjects.CanNFProductionSystem
import TraceCalc.LayerB.RealObjects.Composition
import TraceCalc.LayerC.RealObjects.ConcreteBoundaryContent
import TraceCalc.LayerC.RealObjects.HolographicReconstruction
import TraceCalc.LayerC.RealObjects.CanonicalReconstructionEngine

/-!
# Concrete externalOut adjacent-swap rule and EOSort closure

**Phase 3B (2026-04-29).** This file provides:

1. **`invCount`** — inversion count for adjacent-swap termination.
2. **`swapFirstAdj`** — swap the first adjacent inversion in a list.
3. **`concreteExternalOutSwapData`** — concrete `BoundaryBlockSwapExposureData`
   implementing adjacent externalOut swap; `disjoint_reapplication` is
   parameterised by an abstract assumption `DR`.
4. **`concreteExternalOutSortData`** — concrete `CanNFProductionExternalOutSortData`
   with `canonicalExtOut = mergeSort` and `reduce_to_fully_canonical` proved
   via strong induction on `invCount`.

## Theorem names

* Adjacent swap rule: `concreteExternalOutSwapData`
* Sort reduction:     embedded in `concreteExternalOutSortData.reduce_to_fully_canonical`
* EOSort evidence:    `concreteExternalOutSortData`

## Obligation status

`disjoint_reapplication` in `concreteExternalOutSwapData` is parameterised by
`DR`, consistent with `AdministrativeIdentityRemovalData.disjoint_reapplication`
and `AdjacentCertifiedStepCompositionData.disjoint_reapplication` being abstract
obligations in the current system design.
-/

universe u

namespace TraceCalc
namespace LayerB
namespace RealObjects
namespace RewriteCalculusSetup

open CompletedReconstructionRecord
open CompletedReconstructionRecord.PeelChain
open PeelChain
open PeelChain.FrontierObservation

/-! ## Part 1: Inversion count -/

/-- Count inversions: for each element, count how many later elements are
strictly smaller. Provides the termination measure for adjacent swaps. -/
private def invCount {α : Type*} [LinearOrder α] : List α → ℕ
  | []      => 0
  | x :: xs => xs.countP (fun y => decide (y < x)) + invCount xs

private theorem invCount_cons {α : Type*} [LinearOrder α] (x : α) (xs : List α) :
    invCount (x :: xs) = xs.countP (fun y => decide (y < x)) + invCount xs := rfl

/-- Swapping an adjacent inverted pair decreases inversion count by 1. -/
private theorem invCount_swap_head {α : Type*} [LinearOrder α]
    (x y : α) (rest : List α) (h : x > y) :
    invCount (x :: y :: rest) = invCount (y :: x :: rest) + 1 := by
  simp only [invCount_cons]
  have h1 : List.countP (fun z => decide (z < x)) (y :: rest) =
            List.countP (fun z => decide (z < x)) rest + 1 := by
    rw [List.countP_cons]; simp [h]
  have h2 : List.countP (fun z => decide (z < y)) (x :: rest) =
            List.countP (fun z => decide (z < y)) rest := by
    rw [List.countP_cons]; simp [not_lt.mpr (le_of_lt h)]
  omega

/-- Monotonicity of `countP (· < x)` with respect to `≤`. -/
private theorem countP_lt_mono {α : Type*} [LinearOrder α]
    {x y : α} (h : x ≤ y) (l : List α) :
    l.countP (fun z => decide (z < x)) ≤ l.countP (fun z => decide (z < y)) :=
  List.countP_mono_left (fun a _ ha => by
    simp only [decide_eq_true_iff] at ha ⊢
    exact lt_of_lt_of_le ha h)

/-! ## Part 2: First-adjacent swap -/

/-- Swap the first adjacent pair `(xs[i], xs[i+1])` where `xs[i] > xs[i+1]`.
If the list is sorted, returns it unchanged. -/
private def swapFirstAdj {α : Type*} [LinearOrder α] : List α → List α
  | []             => []
  | [x]            => [x]
  | x :: y :: rest => if x > y then y :: x :: rest else x :: swapFirstAdj (y :: rest)

/-- `swapFirstAdj xs` is a permutation of `xs`. -/
private theorem swapFirstAdj_perm {α : Type*} [LinearOrder α] :
    ∀ xs : List α, List.Perm (swapFirstAdj xs) xs
  | []             => List.Perm.nil
  | [x]            => List.Perm.refl [x]
  | x :: y :: rest => by
      simp only [swapFirstAdj]
      split_ifs with h
      · exact List.Perm.swap x y rest
      · exact (swapFirstAdj_perm (y :: rest)).cons x

/-- When `invCount xs > 0`, one swap strictly decreases `invCount`. -/
private theorem swapFirstAdj_invCount_lt {α : Type*} [LinearOrder α]
    (xs : List α) (h : 0 < invCount xs) :
    invCount (swapFirstAdj xs) < invCount xs := by
  induction xs with
  | nil => simp [invCount] at h
  | cons x ys ih =>
    cases ys with
    | nil => simp [invCount, invCount_cons] at h
    | cons y rest =>
      simp only [swapFirstAdj]
      split_ifs with hxy
      · -- x > y: direct swap decreases by 1
        rw [invCount_swap_head x y rest hxy]
        omega
      · -- x ≤ y: the inversion must be inside y :: rest
        push_neg at hxy
        have hle : x ≤ y := hxy
        -- countP (< x) is unchanged when we cons x ≤ y in front
        have h_cPyx : List.countP (fun z => decide (z < x)) (y :: rest) =
                      List.countP (fun z => decide (z < x)) rest := by
          simp only [List.countP_cons]
          simp [show decide (y < x) = false from by simp [not_lt.mpr hle]]
        -- invCount (x :: y :: rest) = countP (< x) rest + invCount (y :: rest)
        have h_inv_eq : invCount (x :: y :: rest) =
            List.countP (fun z => decide (z < x)) rest + invCount (y :: rest) := by
          rw [invCount_cons, h_cPyx]
        -- The inversion must be in y :: rest
        have h_inv_pos : 0 < invCount (y :: rest) := by
          by_contra hle2
          push_neg at hle2
          have hIvY0 : invCount (y :: rest) = 0 := Nat.le_zero.mp hle2
          have hcPY0 : List.countP (fun z => decide (z < y)) rest = 0 := by
            simp only [invCount_cons] at hIvY0; omega
          have hmono := countP_lt_mono hle rest
          have hcPX0 : List.countP (fun z => decide (z < x)) rest = 0 :=
            Nat.le_zero.mp (by omega)
          omega
        -- countP (< x) is preserved under swapFirstAdj (perm)
        have h_perm := swapFirstAdj_perm (y :: rest)
        have h_cPsw : List.countP (fun z => decide (z < x)) (swapFirstAdj (y :: rest)) =
                      List.countP (fun z => decide (z < x)) rest := by
          rw [h_perm.countP_eq, h_cPyx]
        -- invCount (x :: swapFirstAdj (y :: rest)) = countP (< x) rest + invCount (swapFirstAdj ...)
        have h_inv_sw : invCount (x :: swapFirstAdj (y :: rest)) =
            List.countP (fun z => decide (z < x)) rest + invCount (swapFirstAdj (y :: rest)) := by
          rw [invCount_cons, h_cPsw]
        rw [h_inv_sw, h_inv_eq]
        have := ih h_inv_pos
        omega

/-! ## Part 3: Sorted lists and mergeSort -/

/-- A list with zero inversions is sorted. -/
private theorem invCount_zero_sorted {α : Type*} [LinearOrder α] {xs : List α}
    (h : invCount xs = 0) : xs.Sorted (· ≤ ·) := by
  induction xs with
  | nil       => exact List.sorted_nil
  | cons x rest ih =>
      have hcP  : rest.countP (fun y => decide (y < x)) = 0 := by
        simp only [invCount_cons] at h; omega
      have hInv : invCount rest = 0 := by simp only [invCount_cons] at h; omega
      rw [List.sorted_cons]
      refine ⟨fun y hy => ?_, ih hInv⟩
      by_contra hlt
      push_neg at hlt
      have hlt' : y < x := hlt
      have : 0 < rest.countP (fun z => decide (z < x)) :=
        List.countP_pos_iff.mpr ⟨y, hy, by simp [hlt']⟩
      omega

/-- `mergeSort` is invariant under permutation of input. -/
private theorem sort_congr_perm_mergeSort {α : Type*} [LinearOrder α]
    {xs ys : List α} (h : List.Perm xs ys) : xs.mergeSort = ys.mergeSort :=
  List.eq_of_perm_of_sorted
    ((List.mergeSort_perm xs _).trans (h.trans (List.mergeSort_perm ys _).symm))
    (List.sorted_mergeSort' xs)
    (List.sorted_mergeSort' ys)

/-! ## Part 4: Concrete externalOut swap `BoundaryBlockSwapExposureData` -/

/-- The `disjoint_reapplication` assumption for the concrete externalOut swap rule. -/
private abbrev ConcreteSwapDR (setup : RewriteCalculusSetup.{u}) [LinearOrder setup.RefinedInterface] :=
  ∀ {j : ProductionSchemaIdx setup}
    (S : ProductionSchemaFamilySpec setup j)
    {w : FrontierWord setup}
    (hB : 0 < invCount w.residue.ports.externalOut)
    (hS : S.applies w),
    ResidueFieldTag.Disjoint
      (ProductionSchemaIdx.expose_boundary_block_swap (setup := setup)).writeTag
      j.writeTag →
    ∃ hS' : S.applies
              { w with residue := { w.residue with ports :=
                  { w.residue.ports with
                    externalOut := swapFirstAdj w.residue.ports.externalOut } } },
      S.result
        { w with residue := { w.residue with ports :=
            { w.residue.ports with
              externalOut := swapFirstAdj w.residue.ports.externalOut } } }
        hS' =
      S.result w hS

/-- **`concreteExternalOutSwapData`**: concrete `BoundaryBlockSwapExposureData`
that swaps the first adjacent inversion in `externalOut`.

All fields are concrete except `disjoint_reapplication`, which is an abstract
assumption `DR`. -/
def concreteExternalOutSwapData
    {setup : RewriteCalculusSetup.{u}} [LinearOrder setup.RefinedInterface]
    (DR : ConcreteSwapDR setup) :
    BoundaryBlockSwapExposureData setup where
  applies w := 0 < invCount w.residue.ports.externalOut
  result w _h :=
    { w with residue := { w.residue with ports :=
        { w.residue.ports with externalOut := swapFirstAdj w.residue.ports.externalOut } } }
  sound w _h := {
    n_eq             := rfl
    X_eq             := rfl
    Y_rel            := BoundaryAdminEquiv.refl w.residue.Y
    externalIn_eq    := rfl
    externalOut_perm := (swapFirstAdj_perm w.residue.ports.externalOut).symm
    packetIn_eq      := fun _ => rfl
    packetOut_eq     := fun _ => rfl
    packets_eq       := fun _ => rfl
    dep_edge_eq      := fun _ _ => rfl
    attach_eq        := fun _ => rfl }
  localMeasure w := invCount w.residue.ports.externalOut
  step_decreases w h := swapFirstAdj_invCount_lt _ h
  coherence _h₁ _h₂ := rfl
  boundary_compat w _h := BoundaryAdminEquiv.refl w.residue.Y
  ports_compat w _h := ⟨rfl, swapFirstAdj_perm w.residue.ports.externalOut⟩
  preserves_non_boundary_ports_fields w _h := ⟨rfl, rfl⟩
  disjoint_reapplication := DR

/-! ## Part 5: Canonical mergeSort and EOSort evidence -/

/-- **`concreteExternalOutSortData`**: concrete `CanNFProductionExternalOutSortData`
with `canonicalExtOut = mergeSort` and `reduce_to_fully_canonical` proved
by strong induction on `invCount`. -/
noncomputable def concreteExternalOutSortData
    {setup : RewriteCalculusSetup.{u}} [LinearOrder setup.RefinedInterface]
    {B       : BoundaryAdminCanonicalizeData setup}
    {Dep     : DependencyOrderCanonicalizeData setup}
    {Tensor  : TensorFactorOrderCanonicalizeData setup}
    {Key     : KeyOrderCanonicalizeData setup}
    {Remove  : AdministrativeIdentityRemovalData setup}
    {Compose : AdjacentCertifiedStepCompositionData setup}
    {DR      : ConcreteSwapDR setup}
    {C : ProductionSchemaOperationalSideConditions
           (productionFamilySpecs_allConcreteOrConditional
             B Dep Tensor Key Remove Compose (concreteExternalOutSwapData DR))} :
    CanNFProductionExternalOutSortData B Dep Tensor Key
      (productionSchemaOperationalSpec_concrete B Dep Tensor Key Remove Compose
        (concreteExternalOutSwapData DR) C) where

  canonicalExtOut xs := xs.mergeSort

  sort_congr_perm _xs _ys h := sort_congr_perm_mergeSort h

  reduce_to_fully_canonical w := by
    set spec := productionSchemaOperationalSpec_concrete B Dep Tensor Key Remove Compose
                  (concreteExternalOutSwapData DR) C with hspec_def
    set S    := productionFrontierReductionSystem_from_spec spec with hS_def
    -- Replicate schema_step_to_prod_step (private in CanNFProductionSystem)
    have do_step : ∀ (i : ProductionSchemaIdx setup) (u : FrontierWord setup)
        (h_app : spec.applies i u), S.Step u (spec.result i u h_app) :=
      fun i u h =>
        ⟨{ family := i.family, before := u, after := spec.result i u h,
           valid := spec.applies i u, application_sound := spec.sound i u },
         rfl, rfl, h⟩
    -- ── PART 1: sort externalOut by strong induction on invCount ──────────
    have h_sort : S.MultiStep w
        { w with residue := { w.residue with ports := { w.residue.ports with
            externalOut := w.residue.ports.externalOut.mergeSort } } } := by
      suffices h_gen : ∀ (n : ℕ) (u : FrontierWord setup),
          invCount u.residue.ports.externalOut = n →
          S.MultiStep u { u with residue := { u.residue with ports := { u.residue.ports with
              externalOut := u.residue.ports.externalOut.mergeSort } } } from
        h_gen _ w rfl
      intro n
      induction n using Nat.strongRecOn with
      | _ n ih =>
        intro u hn
        by_cases h_pos : 0 < invCount u.residue.ports.externalOut
        · have h_app : spec.applies .expose_boundary_block_swap u := h_pos
          let u' : FrontierWord setup :=
            { u with residue := { u.residue with ports := { u.residue.ports with
                externalOut := swapFirstAdj u.residue.ports.externalOut } } }
          have h_step : S.Step u u' :=
            show S.Step u (spec.result .expose_boundary_block_swap u h_app) from
              do_step .expose_boundary_block_swap u h_app
          have h_inv_lt : invCount u'.residue.ports.externalOut <
                          invCount u.residue.ports.externalOut :=
            swapFirstAdj_invCount_lt _ h_pos
          have h_merge_eq : u'.residue.ports.externalOut.mergeSort =
                             u.residue.ports.externalOut.mergeSort :=
            sort_congr_perm_mergeSort (swapFirstAdj_perm _)
          have h_rest : S.MultiStep u'
              { u' with residue := { u'.residue with ports := { u'.residue.ports with
                  externalOut := u'.residue.ports.externalOut.mergeSort } } } :=
            ih (invCount u'.residue.ports.externalOut) (hn ▸ h_inv_lt) u' rfl
          have h_target_eq :
              { u' with residue := { u'.residue with ports := { u'.residue.ports with
                  externalOut := u'.residue.ports.externalOut.mergeSort } } } =
              { u with residue := { u.residue with ports := { u.residue.ports with
                  externalOut := u.residue.ports.externalOut.mergeSort } } } := by
            ext; simp [u', h_merge_eq]
          exact FrontierReductionSystem.MultiStep.trans h_step (h_target_eq ▸ h_rest)
        · push_neg at h_pos
          have h0 : invCount u.residue.ports.externalOut = 0 := Nat.le_zero.mp h_pos
          have h_sorted_eq : u.residue.ports.externalOut.mergeSort =
                             u.residue.ports.externalOut :=
            List.mergeSort_eq_self (invCount_zero_sorted h0)
          have h_eq : { u with residue := { u.residue with ports := { u.residue.ports with
                          externalOut := u.residue.ports.externalOut.mergeSort } } } = u := by
            ext; simp [h_sorted_eq]
          rw [h_eq]
          exact FrontierReductionSystem.MultiStep.refl u
    -- ── PART 2: canonicalize Y / dep / tensor / key from the sorted word ──
    let ws : FrontierWord setup :=
      { w with residue := { w.residue with ports := { w.residue.ports with
          externalOut := w.residue.ports.externalOut.mergeSort } } }
    let ws_B : FrontierWord setup :=
      { residue := { ws.residue with Y := B.canonicalizeY ws.residue.Y } }
    let ws_dep : FrontierWord setup :=
      { residue := { ws_B.residue with dep := Dep.canonicalizeDep ws_B.residue.dep } }
    let ws_tensor : FrontierWord setup :=
      { residue := { ws_dep.residue with
          tensor := Tensor.canonicalizeTensor ws_dep.residue.tensor } }
    let target : FrontierWord setup :=
      { residue := { w.residue with
          Y      := B.canonicalizeY w.residue.Y
          dep    := Dep.canonicalizeDep w.residue.dep
          tensor := Tensor.canonicalizeTensor w.residue.tensor
          key    := Key.canonicalizeKey w.residue.key
          ports  := { w.residue.ports with
            externalOut := w.residue.ports.externalOut.mergeSort } } }
    have h_bdk : S.MultiStep ws target := by
      have h_B : S.MultiStep ws ws_B := by
        by_cases hBA : productionBoundaryAdminApplies B ws
        · exact FrontierReductionSystem.MultiStep.trans
            (do_step .boundary_admin_canonicalize ws hBA)
            (FrontierReductionSystem.MultiStep.refl _)
        · have hY : B.canonicalizeY ws.residue.Y = ws.residue.Y :=
            Classical.not_not.mp hBA
          have heqw : ws_B = ws := by ext; simp [ws_B, hY]
          rw [heqw]; exact FrontierReductionSystem.MultiStep.refl ws
      have h_dep : S.MultiStep ws_B ws_dep := by
        by_cases hDep : productionDependencyOrderApplies Dep ws_B
        · exact FrontierReductionSystem.MultiStep.trans
            (do_step .dependency_order_canonicalize ws_B hDep)
            (FrontierReductionSystem.MultiStep.refl _)
        · have hD : Dep.canonicalizeDep ws_B.residue.dep = ws_B.residue.dep :=
            Classical.not_not.mp hDep
          have heqw : ws_dep = ws_B := by ext; simp [ws_dep, hD]
          rw [heqw]; exact FrontierReductionSystem.MultiStep.refl ws_B
      have h_tensor : S.MultiStep ws_dep ws_tensor := by
        by_cases hTns : productionTensorFactorOrderApplies Tensor ws_dep
        · exact FrontierReductionSystem.MultiStep.trans
            (do_step .tensor_factor_order_canonicalize ws_dep hTns)
            (FrontierReductionSystem.MultiStep.refl _)
        · have hT : Tensor.canonicalizeTensor ws_dep.residue.tensor = ws_dep.residue.tensor :=
            Classical.not_not.mp hTns
          have heqw : ws_tensor = ws_dep := by ext; simp [ws_tensor, hT]
          rw [heqw]; exact FrontierReductionSystem.MultiStep.refl ws_dep
      have h_key : S.MultiStep ws_tensor target := by
        by_cases hKey : productionKeyOrderApplies Key ws_tensor
        · have hstep := do_step .key_order_canonicalize ws_tensor hKey
          have heqt : productionKeyOrderResult Key ws_tensor hKey = target := by
            ext; simp [productionKeyOrderResult, target, ws_tensor, ws_dep, ws_B, ws]
          exact heqt ▸ FrontierReductionSystem.MultiStep.trans hstep
            (FrontierReductionSystem.MultiStep.refl _)
        · have hK : Key.canonicalizeKey ws_tensor.residue.key = ws_tensor.residue.key :=
            Classical.not_not.mp hKey
          have heqt : target = ws_tensor := by
            ext; simp [target, ws_tensor, ws_dep, ws_B, ws, hK]
          rw [heqt]; exact FrontierReductionSystem.MultiStep.refl ws_tensor
      exact h_B.appendTrans (h_dep.appendTrans (h_tensor.appendTrans h_key))
    exact h_sort.appendTrans h_bdk

/-! ## Part 6: Closed corrected residue package for concrete expose/remove -/

/-- Corrected concrete expose family: adjacent-swap on `externalOut`, with no
legacy schema-level disjointness parameter. -/
private def concreteResidueExposeFamilySpec
    {setup : RewriteCalculusSetup.{u}} [LinearOrder setup.RefinedInterface] :
    ResidueProductionFamilySpec setup
      (ResidueProductionSchemaIdx.expose_boundary_block_swap (setup := setup)) where
  applies w := 0 < invCount w.residue.ports.externalOut
  result w _ :=
    { w with residue := { w.residue with ports :=
        { w.residue.ports with externalOut := swapFirstAdj w.residue.ports.externalOut } } }

/-- Corrected concrete remove family. Applicability is the concrete existential
administrative-identity predicate, while the result deletes the chosen witness
selected from that proof. -/
private noncomputable def concreteResidueRemoveFamilySpec
    (setup : RewriteCalculusSetup.{u}) :
    ResidueProductionFamilySpec setup
      (ResidueProductionSchemaIdx.administrative_identity_contraction (setup := setup)) where
  applies w := ∃ k : Fin w.residue.n, IsAdministrativeIdentityPacket w k
  result w h :=
    removeAdministrativeIdentityResult w (Classical.choose h) (Classical.choose_spec h)

/-- Fully concrete corrected residue inventory: canonicalizers, explicit
externalOut swap, and explicit administrative contraction. -/
noncomputable def residueProductionFamilySpecs_concrete_closed
    {setup : RewriteCalculusSetup.{u}} [LinearOrder setup.RefinedInterface]
    (B : BoundaryAdminCanonicalizeData setup)
    (Dep : DependencyOrderCanonicalizeData setup)
    (Tensor : TensorFactorOrderCanonicalizeData setup)
    (Key : KeyOrderCanonicalizeData setup) :
    ResidueProductionFamilySpecs setup where
  family
    | .boundary_admin_canonicalize =>
        { applies := productionBoundaryAdminApplies B
          result := productionBoundaryAdminResult B }
    | .dependency_order_canonicalize =>
        { applies := productionDependencyOrderApplies Dep
          result := productionDependencyOrderResult Dep }
    | .tensor_factor_order_canonicalize =>
        { applies := productionTensorFactorOrderApplies Tensor
          result := productionTensorFactorOrderResult Tensor }
    | .key_order_canonicalize =>
        { applies := productionKeyOrderApplies Key
          result := productionKeyOrderResult Key }
    | .expose_boundary_block_swap => concreteResidueExposeFamilySpec
    | .administrative_identity_contraction => concreteResidueRemoveFamilySpec setup

private theorem concreteResidueRemove_preserves_Y
    {setup : RewriteCalculusSetup.{u}} (w : FrontierWord setup)
    (h : (concreteResidueRemoveFamilySpec setup).applies w) :
    ((concreteResidueRemoveFamilySpec setup).result w h).residue.Y = w.residue.Y := by
  let k := Classical.choose h
  let hId := Classical.choose_spec h
  rcases w with ⟨⟨m, X, Y, ports, packets, dep, attach, tensor, key⟩⟩
  cases m with
  | zero =>
      have hkFalse : False := by simpa using k.2
      exact False.elim hkFalse
  | succ n =>
      simp [concreteResidueRemoveFamilySpec, removeAdministrativeIdentityResult]

private theorem concreteResidueRemove_preserves_externalIn
    {setup : RewriteCalculusSetup.{u}} (w : FrontierWord setup)
    (h : (concreteResidueRemoveFamilySpec setup).applies w) :
    ((concreteResidueRemoveFamilySpec setup).result w h).residue.ports.externalIn =
      w.residue.ports.externalIn := by
  let k := Classical.choose h
  let hId := Classical.choose_spec h
  rcases w with ⟨⟨m, X, Y, ports, packets, dep, attach, tensor, key⟩⟩
  cases m with
  | zero =>
      have hkFalse : False := by simpa using k.2
      exact False.elim hkFalse
  | succ n =>
      rcases ports with ⟨externalIn, externalOut, packetIn, packetOut⟩
      simp [concreteResidueRemoveFamilySpec, removeAdministrativeIdentityResult]
      rfl

private theorem concreteResidueRemove_preserves_externalOut
    {setup : RewriteCalculusSetup.{u}} (w : FrontierWord setup)
    (h : (concreteResidueRemoveFamilySpec setup).applies w) :
    ((concreteResidueRemoveFamilySpec setup).result w h).residue.ports.externalOut =
      w.residue.ports.externalOut := by
  let k := Classical.choose h
  let hId := Classical.choose_spec h
  rcases w with ⟨⟨m, X, Y, ports, packets, dep, attach, tensor, key⟩⟩
  cases m with
  | zero =>
      have hkFalse : False := by simpa using k.2
      exact False.elim hkFalse
  | succ n =>
      rcases ports with ⟨externalIn, externalOut, packetIn, packetOut⟩
      simp [concreteResidueRemoveFamilySpec, removeAdministrativeIdentityResult]
      rfl

private theorem concreteResidueRemove_applies_after_boundary
    {setup : RewriteCalculusSetup.{u}}
    (B : BoundaryAdminCanonicalizeData setup)
    {w : FrontierWord setup}
    (hR : (concreteResidueRemoveFamilySpec setup).applies w)
    (hB : productionBoundaryAdminApplies B w) :
    (concreteResidueRemoveFamilySpec setup).applies (productionBoundaryAdminResult B w hB) := by
  let k := Classical.choose hR
  let hId := Classical.choose_spec hR
  exact ⟨k, by simpa [IsAdministrativeIdentityPacket, productionBoundaryAdminResult] using hId⟩

private theorem concreteResidueRemove_applies_after_expose
    {setup : RewriteCalculusSetup.{u}} [LinearOrder setup.RefinedInterface]
    {w : FrontierWord setup}
    (hR : (concreteResidueRemoveFamilySpec setup).applies w)
    (hE : (concreteResidueExposeFamilySpec (setup := setup)).applies w) :
    (concreteResidueRemoveFamilySpec setup).applies
      ((concreteResidueExposeFamilySpec (setup := setup)).result w hE) := by
  let k := Classical.choose hR
  let hId := Classical.choose_spec hR
  exact ⟨k, by
    simpa [IsAdministrativeIdentityPacket, concreteResidueExposeFamilySpec] using hId⟩

private theorem concreteResidueBoundary_after_remove_eq_remove_after_boundary
    {setup : RewriteCalculusSetup.{u}}
    (B : BoundaryAdminCanonicalizeData setup)
    {w : FrontierWord setup}
    (hR : (concreteResidueRemoveFamilySpec setup).applies w)
    (hB : productionBoundaryAdminApplies B w) :
    productionBoundaryAdminResult B ((concreteResidueRemoveFamilySpec setup).result w hR)
      (by
        simpa [productionBoundaryAdminApplies, concreteResidueRemove_preserves_Y _ hR] using hB) =
    (concreteResidueRemoveFamilySpec setup).result (productionBoundaryAdminResult B w hB)
      (concreteResidueRemove_applies_after_boundary B hR hB) := by
  let k := Classical.choose hR
  let hId := Classical.choose_spec hR
  rcases w with ⟨⟨m, X, Y, ports, packets, dep, attach, tensor, key⟩⟩
  cases m with
  | zero =>
      have hkFalse : False := by simpa using k.2
      exact False.elim hkFalse
  | succ n =>
      simp [concreteResidueRemoveFamilySpec, productionBoundaryAdminResult,
        removeAdministrativeIdentityResult]

private theorem concreteResidueExpose_after_remove_eq_remove_after_expose
    {setup : RewriteCalculusSetup.{u}} [LinearOrder setup.RefinedInterface]
    {w : FrontierWord setup}
    (hR : (concreteResidueRemoveFamilySpec setup).applies w)
    (hE : (concreteResidueExposeFamilySpec (setup := setup)).applies w) :
    (concreteResidueExposeFamilySpec (setup := setup)).result
      ((concreteResidueRemoveFamilySpec setup).result w hR)
      (by
        simpa [concreteResidueExposeFamilySpec, concreteResidueRemove_preserves_externalOut _ hR]
          using hE) =
    (concreteResidueRemoveFamilySpec setup).result
      ((concreteResidueExposeFamilySpec (setup := setup)).result w hE)
      (concreteResidueRemove_applies_after_expose hR hE) := by
  let k := Classical.choose hR
  let hId := Classical.choose_spec hR
  rcases w with ⟨⟨m, X, Y, ports, packets, dep, attach, tensor, key⟩⟩
  cases m with
  | zero =>
      have hkFalse : False := by simpa using k.2
      exact False.elim hkFalse
  | succ n =>
      rcases ports with ⟨externalIn, externalOut, packetIn, packetOut⟩
      let w0 : FrontierWord setup := {
        residue := {
          n := n + 1,
          X := X,
          Y := Y,
          ports := {
            externalIn := externalIn,
            externalOut := externalOut,
            packetIn := packetIn,
            packetOut := packetOut
          },
          packets := packets,
          dep := dep,
          attach := attach,
          tensor := tensor,
          key := key
        }
      }
      simpa [w0, concreteResidueExposeFamilySpec, concreteResidueRemoveFamilySpec]
        using removeAdministrativeIdentityResult_replaceExternalOut
          (w := w0) (k := k) (hId := hId) (externalOut' := swapFirstAdj externalOut)

private def concreteResidueProjectionInterface
    (setup : RewriteCalculusSetup.{u}) :
    ResidueProductionSchemaIdx.ResidueSlotProjectionInterface setup where
  SameOnSlot s w₁ w₂ :=
    match s with
    | .shape => w₁.residue.n = w₂.residue.n
    | .Y => w₁.residue.Y = w₂.residue.Y
    | .externalIn => w₁.residue.ports.externalIn = w₂.residue.ports.externalIn
    | .externalOut => w₁.residue.ports.externalOut = w₂.residue.ports.externalOut
    | .packetPorts =>
        HEq w₁.residue.ports.packetIn w₂.residue.ports.packetIn ∧
          HEq w₁.residue.ports.packetOut w₂.residue.ports.packetOut
    | .packets => HEq w₁.residue.packets w₂.residue.packets
    | .dep => HEq w₁.residue.dep w₂.residue.dep
    | .attach => HEq w₁.residue.attach w₂.residue.attach
    | .tensor => HEq w₁.residue.tensor w₂.residue.tensor
    | .key => HEq w₁.residue.key w₂.residue.key
  refl s w := by
    cases s <;> simp
  symm s := by
    cases s
    · intro w₁ w₂ h; exact h.symm
    · intro w₁ w₂ h; exact h.symm
    · intro w₁ w₂ h; exact h.symm
    · intro w₁ w₂ h; exact h.symm
    · intro w₁ w₂ h
      rcases h with ⟨hIn, hOut⟩
      exact ⟨hIn.symm, hOut.symm⟩
    · intro w₁ w₂ h; exact h.symm
    · intro w₁ w₂ h; exact h.symm
    · intro w₁ w₂ h; exact h.symm
    · intro w₁ w₂ h; exact h.symm
    · intro w₁ w₂ h; exact h.symm
  trans s := by
    cases s
    · intro w₁ w₂ w₃ h₁ h₂; exact h₁.trans h₂
    · intro w₁ w₂ w₃ h₁ h₂; exact h₁.trans h₂
    · intro w₁ w₂ w₃ h₁ h₂; exact h₁.trans h₂
    · intro w₁ w₂ w₃ h₁ h₂; exact h₁.trans h₂
    · intro w₁ w₂ w₃ h₁ h₂; exact ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
    · intro w₁ w₂ w₃ h₁ h₂; exact h₁.trans h₂
    · intro w₁ w₂ w₃ h₁ h₂; exact h₁.trans h₂
    · intro w₁ w₂ w₃ h₁ h₂; exact h₁.trans h₂
    · intro w₁ w₂ w₃ h₁ h₂; exact h₁.trans h₂
    · intro w₁ w₂ w₃ h₁ h₂; exact h₁.trans h₂

private theorem concreteEqToHEq {α : Sort _} {a b : α} (h : a = b) : HEq a b := by
  cases h
  rfl

private noncomputable def residueProductionLocalMeasure_concrete_closed
    {setup : RewriteCalculusSetup.{u}} [LinearOrder setup.RefinedInterface]
    (B : BoundaryAdminCanonicalizeData setup)
    (Dep : DependencyOrderCanonicalizeData setup)
    (Tensor : TensorFactorOrderCanonicalizeData setup)
    (Key : KeyOrderCanonicalizeData setup) :
    ResidueProductionSchemaIdx setup → FrontierWord setup → Nat
  | .boundary_admin_canonicalize => productionBoundaryAdminMeasure B
  | .dependency_order_canonicalize => productionDependencyOrderMeasure Dep
  | .tensor_factor_order_canonicalize => productionTensorFactorOrderMeasure Tensor
  | .key_order_canonicalize => productionKeyOrderMeasure Key
  | .expose_boundary_block_swap => fun w => invCount w.residue.ports.externalOut
  | .administrative_identity_contraction => fun w => w.residue.n

private def residueProductionIsNormal_concrete_closed
    {setup : RewriteCalculusSetup.{u}} [LinearOrder setup.RefinedInterface]
    (B : BoundaryAdminCanonicalizeData setup)
    (Dep : DependencyOrderCanonicalizeData setup)
    (Tensor : TensorFactorOrderCanonicalizeData setup)
    (Key : KeyOrderCanonicalizeData setup)
    (w : FrontierWord setup) : Prop :=
  ¬ ∃ app : ResidueProductionApplication setup,
      app.before = w ∧
        ResidueProductionApplication.ValidForFamilySpecs
          (residueProductionFamilySpecs_concrete_closed B Dep Tensor Key) app

private theorem residueProductionMultiStep_single
    {setup : RewriteCalculusSetup.{u}}
    (F : ResidueProductionFamilySpecs setup)
    (i : ResidueProductionSchemaIdx setup)
    (w : FrontierWord setup)
    (h : (F.family i).applies w) :
    ResidueProductionMultiStep F w ((F.family i).result w h) := by
  exact Relation.ReflTransGen.single (ResidueProductionStep.mk i w h)

/-- Concrete corrected residue side conditions for the closed six-family route.

This is the concrete-production `C` object for the corrected residue path.
The old seven-family production path is separate legacy infrastructure.
The corrected residue inventory has exactly six families: boundary admin,
dependency order, tensor order, key order, expose-boundary swap, and remove as
administrative contraction. Compose is trace/provenance-layer only and is not a
residue CanNF family. -/
noncomputable def residueProductionOperationalSideConditions_concrete_closed
    {setup : RewriteCalculusSetup.{u}} [LinearOrder setup.RefinedInterface]
    (B : BoundaryAdminCanonicalizeData setup)
    (Dep : DependencyOrderCanonicalizeData setup)
    (Tensor : TensorFactorOrderCanonicalizeData setup)
    (Key : KeyOrderCanonicalizeData setup) :
    ResidueProductionOperationalSideConditions setup
      (residueProductionFamilySpecs_concrete_closed B Dep Tensor Key) := by
  classical
  refine residueProductionOperationalSideConditions_ofFamilySpecs
    (F := residueProductionFamilySpecs_concrete_closed B Dep Tensor Key)
    (residueProductionLocalMeasure_concrete_closed B Dep Tensor Key)
    (residueProductionIsNormal_concrete_closed B Dep Tensor Key)
    ?_ ?_ ?_ (concreteResidueProjectionInterface setup) ?_ ?_
  · intro i w h
    cases i with
    | boundary_admin_canonicalize => exact productionBoundaryAdminStepDecreases B w h
    | dependency_order_canonicalize => exact productionDependencyOrderStepDecreases Dep w h
    | tensor_factor_order_canonicalize => exact productionTensorFactorOrderStepDecreases Tensor w h
    | key_order_canonicalize => exact productionKeyOrderStepDecreases Key w h
    | expose_boundary_block_swap => exact swapFirstAdj_invCount_lt _ h
    | administrative_identity_contraction =>
      let k := Classical.choose h
      rcases w with ⟨⟨m, X, Y, ports, packets, dep, attach, tensor, key⟩⟩
      cases m with
      | zero =>
        have hkFalse : False := by simpa using k.2
        exact False.elim hkFalse
      | succ n =>
        change
          (removeAdministrativeIdentityResult
            { residue :=
                { n := n + 1, X := X, Y := Y, ports := ports, packets := packets,
                  dep := dep, attach := attach, tensor := tensor, key := key } }
            (Classical.choose h) (Classical.choose_spec h)).residue.n < n + 1
        simpa [removeAdministrativeIdentityResult] using Nat.lt_succ_self n
  · intro w hN
    exact hN
  · intro w hNo
    exact hNo
  · intro i w h s hOutside
    cases i with
    | boundary_admin_canonicalize =>
      cases s with
      | shape => exact rfl
      | Y => cases hOutside
      | externalIn => exact rfl
      | externalOut => exact rfl
      | packetPorts => exact ⟨HEq.rfl, HEq.rfl⟩
      | packets => exact HEq.rfl
      | dep => exact concreteEqToHEq (Eq.symm (productionBoundaryAdmin_preserves_dep B w h))
      | attach => exact HEq.rfl
      | tensor => exact concreteEqToHEq (Eq.symm (productionBoundaryAdmin_preserves_tensor B w h))
      | key => exact concreteEqToHEq (Eq.symm (productionBoundaryAdmin_preserves_key B w h))
    | dependency_order_canonicalize =>
      cases s with
      | shape => exact rfl
      | Y => exact productionDependencyOrder_preserves_Y Dep w h
      | externalIn =>
        have hPorts : w.residue.ports = (productionDependencyOrderResult Dep w h).residue.ports :=
          Eq.symm (productionDependencyOrder_preserves_ports Dep w h)
        exact congrArg (fun p => p.externalIn) hPorts
      | externalOut =>
        have hPorts : w.residue.ports = (productionDependencyOrderResult Dep w h).residue.ports :=
          Eq.symm (productionDependencyOrder_preserves_ports Dep w h)
        exact congrArg (fun p => p.externalOut) hPorts
      | packetPorts =>
        have hPorts : w.residue.ports = (productionDependencyOrderResult Dep w h).residue.ports :=
          Eq.symm (productionDependencyOrder_preserves_ports Dep w h)
        exact ⟨concreteEqToHEq (congrArg (fun p => p.packetIn) hPorts), concreteEqToHEq (congrArg (fun p => p.packetOut) hPorts)⟩
      | packets => exact HEq.rfl
      | dep => cases hOutside
      | attach => exact concreteEqToHEq (Eq.symm (productionDependencyOrder_preserves_attach Dep w h))
      | tensor => exact concreteEqToHEq (Eq.symm (productionDependencyOrder_preserves_tensor Dep w h))
      | key => exact concreteEqToHEq (Eq.symm (productionDependencyOrder_preserves_key Dep w h))
    | tensor_factor_order_canonicalize =>
      cases s with
      | shape => exact rfl
      | Y => exact productionTensorFactorOrder_preserves_Y Tensor w h
      | externalIn =>
        have hPorts : w.residue.ports = (productionTensorFactorOrderResult Tensor w h).residue.ports :=
          Eq.symm (productionTensorFactorOrder_preserves_ports Tensor w h)
        exact congrArg (fun p => p.externalIn) hPorts
      | externalOut =>
        have hPorts : w.residue.ports = (productionTensorFactorOrderResult Tensor w h).residue.ports :=
          Eq.symm (productionTensorFactorOrder_preserves_ports Tensor w h)
        exact congrArg (fun p => p.externalOut) hPorts
      | packetPorts =>
        have hPorts : w.residue.ports = (productionTensorFactorOrderResult Tensor w h).residue.ports :=
          Eq.symm (productionTensorFactorOrder_preserves_ports Tensor w h)
        exact ⟨concreteEqToHEq (congrArg (fun p => p.packetIn) hPorts), concreteEqToHEq (congrArg (fun p => p.packetOut) hPorts)⟩
      | packets => exact HEq.rfl
      | dep => exact concreteEqToHEq (Eq.symm (productionTensorFactorOrder_preserves_dep Tensor w h))
      | attach => exact concreteEqToHEq (Eq.symm (productionTensorFactorOrder_preserves_attach Tensor w h))
      | tensor => cases hOutside
      | key => exact concreteEqToHEq (Eq.symm (productionTensorFactorOrder_preserves_key Tensor w h))
    | key_order_canonicalize =>
      cases s with
      | shape => exact rfl
      | Y => exact productionKeyOrder_preserves_Y Key w h
      | externalIn =>
        have hPorts : w.residue.ports = (productionKeyOrderResult Key w h).residue.ports :=
          Eq.symm (productionKeyOrder_preserves_ports Key w h)
        exact congrArg (fun p => p.externalIn) hPorts
      | externalOut =>
        have hPorts : w.residue.ports = (productionKeyOrderResult Key w h).residue.ports :=
          Eq.symm (productionKeyOrder_preserves_ports Key w h)
        exact congrArg (fun p => p.externalOut) hPorts
      | packetPorts =>
        have hPorts : w.residue.ports = (productionKeyOrderResult Key w h).residue.ports :=
          Eq.symm (productionKeyOrder_preserves_ports Key w h)
        exact ⟨concreteEqToHEq (congrArg (fun p => p.packetIn) hPorts), concreteEqToHEq (congrArg (fun p => p.packetOut) hPorts)⟩
      | packets => exact HEq.rfl
      | dep => exact concreteEqToHEq (Eq.symm (productionKeyOrder_preserves_dep Key w h))
      | attach => exact concreteEqToHEq (Eq.symm (productionKeyOrder_preserves_attach Key w h))
      | tensor => exact concreteEqToHEq (Eq.symm (productionKeyOrder_preserves_tensor Key w h))
      | key => cases hOutside
    | expose_boundary_block_swap =>
      cases s with
      | shape => exact rfl
      | Y => exact rfl
      | externalIn => exact rfl
      | externalOut => cases hOutside
      | packetPorts => exact ⟨HEq.rfl, HEq.rfl⟩
      | packets => exact HEq.rfl
      | dep => exact HEq.rfl
      | attach => exact HEq.rfl
      | tensor => exact HEq.rfl
      | key => exact HEq.rfl
    | administrative_identity_contraction =>
      cases s with
      | shape => cases hOutside
      | Y => exact Eq.symm (concreteResidueRemove_preserves_Y w h)
      | externalIn => exact Eq.symm (concreteResidueRemove_preserves_externalIn w h)
      | externalOut => exact Eq.symm (concreteResidueRemove_preserves_externalOut w h)
      | packetPorts => cases hOutside
      | packets => cases hOutside
      | dep => cases hOutside
      | attach => cases hOutside
      | tensor => cases hOutside
      | key => cases hOutside
  · intro i₁ i₂ w h₁ h₂ hDisjoint
    cases i₁ <;> cases i₂ <;>
      simp [ResidueProductionSchemaIdx.footprint,
        ResidueProductionSchemaIdx.ResidueWriteFootprint.Disjoint] at hDisjoint ⊢

  /-- Concrete corrected residue operational package for the closed six-family
  route.

  This packages the corrected residue `C` object for the concrete-production
  path. The seven-family production aliases remain separate legacy machinery;
  compose stays in the trace/provenance layer, while remove is the corrected
  residue contraction family. -/
  noncomputable def residueProductionOperationalSpec_concrete_closed
    {setup : RewriteCalculusSetup.{u}} [LinearOrder setup.RefinedInterface]
    (B : BoundaryAdminCanonicalizeData setup)
    (Dep : DependencyOrderCanonicalizeData setup)
    (Tensor : TensorFactorOrderCanonicalizeData setup)
    (Key : KeyOrderCanonicalizeData setup) :
    ResidueProductionOperationalSpec setup :=
  ResidueProductionOperationalSpec.ofFamilySpecs
    (residueProductionFamilySpecs_concrete_closed B Dep Tensor Key)
    (residueProductionOperationalSideConditions_concrete_closed B Dep Tensor Key)

private abbrev concreteClosedSetup (RI : Type u) [DecidableEq RI] : RewriteCalculusSetup.{u} :=
  concreteBoundaryMinimalSetup RI

private instance concreteClosedSetupDecidableEq
  (RI : Type u) [DecidableEq RI] :
  DecidableEq (concreteClosedSetup RI).RefinedInterface := ‹DecidableEq RI›

private instance concreteClosedSetupLinearOrder
  (RI : Type u) [DecidableEq RI] [LinearOrder RI] :
  LinearOrder (concreteClosedSetup RI).RefinedInterface := ‹LinearOrder RI›

private noncomputable def concreteClosedBoundaryData
    (RI : Type u) [DecidableEq RI] :
    BoundaryAdminCanonicalizeData (concreteClosedSetup RI) :=
  concreteBoundaryCanonicalizeData
    (setup := concreteClosedSetup RI)
    (show (concreteClosedSetup RI).ExposeBoundaryCommutes from
      ExposeBoundaryCommutes_for_concreteMinimalSetup RI)

private def concreteClosedDependencyData
    (RI : Type u) [DecidableEq RI] :
    DependencyOrderCanonicalizeData (concreteClosedSetup RI) :=
  trivialDependencyOrderCanonicalizeData (concreteClosedSetup RI)

private def concreteClosedTensorData
    (RI : Type u) [DecidableEq RI] :
    TensorFactorOrderCanonicalizeData (concreteClosedSetup RI) :=
  trivialTensorFactorOrderCanonicalizeData (concreteClosedSetup RI)

private def concreteClosedTensorUniqueData
    (RI : Type u) [DecidableEq RI] :
    TensorFactorOrderCanonicalizeUniqueData (concreteClosedTensorData RI) :=
  trivialTensorFactorOrderCanonicalizeUniqueData (concreteClosedSetup RI)

private def concreteClosedKeyData
    (RI : Type u) [DecidableEq RI] :
    KeyOrderCanonicalizeData (concreteClosedSetup RI) :=
  trivialKeyOrderCanonicalizeData (concreteClosedSetup RI)

private def concreteClosedKeyUniqueData
    (RI : Type u) [DecidableEq RI] :
    KeyOrderCanonicalizeUniqueData (concreteClosedKeyData RI) :=
  trivialKeyOrderCanonicalizeUniqueData (concreteClosedSetup RI)

private noncomputable def concreteClosedResidueFamilySpecs
    (RI : Type u) [DecidableEq RI] [LinearOrder RI] :
    ResidueProductionFamilySpecs (concreteClosedSetup RI) :=
  residueProductionFamilySpecs_concrete_closed
    (setup := concreteClosedSetup RI)
    (concreteClosedBoundaryData RI)
    (concreteClosedDependencyData RI)
    (concreteClosedTensorData RI)
    (concreteClosedKeyData RI)

private theorem concreteResidueRemove_applies_after_tensor
    {setup : RewriteCalculusSetup.{u}}
    (Tensor : TensorFactorOrderCanonicalizeData setup)
    {w : FrontierWord setup}
    (hR : (concreteResidueRemoveFamilySpec setup).applies w)
    (hT : productionTensorFactorOrderApplies Tensor w) :
    (concreteResidueRemoveFamilySpec setup).applies
      (productionTensorFactorOrderResult Tensor w hT) := by
  let k := Classical.choose hR
  let hId := Classical.choose_spec hR
  exact ⟨k, by
    simpa [IsAdministrativeIdentityPacket, productionTensorFactorOrderResult] using hId⟩

private theorem concreteResidueRemove_applies_after_key
    {setup : RewriteCalculusSetup.{u}}
    (Key : KeyOrderCanonicalizeData setup)
    {w : FrontierWord setup}
    (hR : (concreteResidueRemoveFamilySpec setup).applies w)
    (hK : productionKeyOrderApplies Key w) :
    (concreteResidueRemoveFamilySpec setup).applies
      (productionKeyOrderResult Key w hK) := by
  let k := Classical.choose hR
  let hId := Classical.choose_spec hR
  exact ⟨k, by
    simpa [IsAdministrativeIdentityPacket, productionKeyOrderResult] using hId⟩

private theorem concreteClosedTensor_reduces_to_canonical
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (w : FrontierWord (concreteClosedSetup RI)) :
    ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI) w
      { residue :=
          { w.residue with
              tensor := (concreteClosedTensorData RI).canonicalizeTensor w.residue.tensor } } := by
  by_cases hT : productionTensorFactorOrderApplies (concreteClosedTensorData RI) w
  · simpa [concreteClosedResidueFamilySpecs, residueProductionFamilySpecs_concrete_closed,
      concreteClosedTensorData] using
      (residueProductionMultiStep_single
        (F := concreteClosedResidueFamilySpecs RI)
        .tensor_factor_order_canonicalize w
        (show ((concreteClosedResidueFamilySpecs RI).family
            .tensor_factor_order_canonicalize).applies w from hT))
  · have hEq : (concreteClosedTensorData RI).canonicalizeTensor w.residue.tensor =
        w.residue.tensor := by
      simpa [productionTensorFactorOrderApplies] using hT
    simpa [hEq] using
      (show ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI) w w from
        Relation.ReflTransGen.refl :
        ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI) w w)

private theorem concreteClosedKey_reduces_to_canonical
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (w : FrontierWord (concreteClosedSetup RI)) :
    ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI) w
      { residue :=
          { w.residue with
              key := (concreteClosedKeyData RI).canonicalizeKey w.residue.key } } := by
  by_cases hK : productionKeyOrderApplies (concreteClosedKeyData RI) w
  · simpa [concreteClosedResidueFamilySpecs, residueProductionFamilySpecs_concrete_closed,
      concreteClosedKeyData] using
      (residueProductionMultiStep_single
        (F := concreteClosedResidueFamilySpecs RI)
        .key_order_canonicalize w
        (show ((concreteClosedResidueFamilySpecs RI).family
            .key_order_canonicalize).applies w from hK))
  · have hEq : (concreteClosedKeyData RI).canonicalizeKey w.residue.key =
        w.residue.key := by
      simpa [productionKeyOrderApplies] using hK
    simpa [hEq] using
      (show ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI) w w from
        Relation.ReflTransGen.refl :
        ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI) w w)

private theorem remove_dependencyOrder_critical_pair_join
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    {w : FrontierWord (concreteClosedSetup RI)}
    (hR : (concreteResidueRemoveFamilySpec (concreteClosedSetup RI)).applies w)
    (hD : productionDependencyOrderApplies (concreteClosedDependencyData RI) w) :
    ∃ v : FrontierWord (concreteClosedSetup RI),
      ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI)
        ((concreteResidueRemoveFamilySpec (concreteClosedSetup RI)).result w hR) v ∧
      ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI)
        (productionDependencyOrderResult (concreteClosedDependencyData RI) w hD) v := by
  exact False.elim (hD rfl)

private theorem remove_tensorOrder_critical_pair_join
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    {w : FrontierWord (concreteClosedSetup RI)}
    (hR : (concreteResidueRemoveFamilySpec (concreteClosedSetup RI)).applies w)
    (hT : productionTensorFactorOrderApplies (concreteClosedTensorData RI) w) :
    ∃ v : FrontierWord (concreteClosedSetup RI),
      ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI)
        ((concreteResidueRemoveFamilySpec (concreteClosedSetup RI)).result w hR) v ∧
      ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI)
        (productionTensorFactorOrderResult (concreteClosedTensorData RI) w hT) v := by
  let wR := (concreteResidueRemoveFamilySpec (concreteClosedSetup RI)).result w hR
  let hRT := concreteResidueRemove_applies_after_tensor (concreteClosedTensorData RI) hR hT
  let wTR :=
    (concreteResidueRemoveFamilySpec (concreteClosedSetup RI)).result
      (productionTensorFactorOrderResult (concreteClosedTensorData RI) w hT) hRT
  let v : FrontierWord (concreteClosedSetup RI) :=
    { residue :=
        { wR.residue with
            tensor := (concreteClosedTensorData RI).canonicalizeTensor wR.residue.tensor } }
  have hwRv : ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI) wR v :=
    concreteClosedTensor_reduces_to_canonical RI wR
  have hwTRv : ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI) wTR v := by
    have hwTRcanon := concreteClosedTensor_reduces_to_canonical RI wTR
    have hEqCanon :
        { residue :=
            { wTR.residue with
                tensor := (concreteClosedTensorData RI).canonicalizeTensor wTR.residue.tensor } } = v := by
      rcases w with ⟨⟨m, X, Y, ports, packets, dep, attach, tensor, key⟩⟩
      cases m with
      | zero =>
          have hkFalse : False := by
            simpa using (Classical.choose hR).2
          exact False.elim hkFalse
      | succ n =>
          simp [wR, wTR, v, concreteResidueRemoveFamilySpec, productionTensorFactorOrderResult,
            removeAdministrativeIdentityResult]
          exact (concreteClosedTensorUniqueData RI).canonicalizeTensor_unique _ _
    simpa [hEqCanon] using hwTRcanon
  refine ⟨v, hwRv, ?_⟩
  exact Relation.ReflTransGen.trans
    (Relation.ReflTransGen.single
      (ResidueProductionStep.mk .administrative_identity_contraction
        (productionTensorFactorOrderResult (concreteClosedTensorData RI) w hT)
        (show ((concreteClosedResidueFamilySpecs RI).family
            .administrative_identity_contraction).applies
            (productionTensorFactorOrderResult (concreteClosedTensorData RI) w hT) from hRT)))
    hwTRv

private theorem remove_keyOrder_critical_pair_join
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    {w : FrontierWord (concreteClosedSetup RI)}
    (hR : (concreteResidueRemoveFamilySpec (concreteClosedSetup RI)).applies w)
    (hK : productionKeyOrderApplies (concreteClosedKeyData RI) w) :
    ∃ v : FrontierWord (concreteClosedSetup RI),
      ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI)
        ((concreteResidueRemoveFamilySpec (concreteClosedSetup RI)).result w hR) v ∧
      ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI)
        (productionKeyOrderResult (concreteClosedKeyData RI) w hK) v := by
  let wR := (concreteResidueRemoveFamilySpec (concreteClosedSetup RI)).result w hR
  let hRK := concreteResidueRemove_applies_after_key (concreteClosedKeyData RI) hR hK
  let wKR :=
    (concreteResidueRemoveFamilySpec (concreteClosedSetup RI)).result
      (productionKeyOrderResult (concreteClosedKeyData RI) w hK) hRK
  let v : FrontierWord (concreteClosedSetup RI) :=
    { residue :=
        { wR.residue with
            key := (concreteClosedKeyData RI).canonicalizeKey wR.residue.key } }
  have hwRv : ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI) wR v :=
    concreteClosedKey_reduces_to_canonical RI wR
  have hwKRv : ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI) wKR v := by
    have hwKRcanon := concreteClosedKey_reduces_to_canonical RI wKR
    have hEqCanon :
        { residue :=
            { wKR.residue with
                key := (concreteClosedKeyData RI).canonicalizeKey wKR.residue.key } } = v := by
      rcases w with ⟨⟨m, X, Y, ports, packets, dep, attach, tensor, key⟩⟩
      cases m with
      | zero =>
          have hkFalse : False := by
            simpa using (Classical.choose hR).2
          exact False.elim hkFalse
      | succ n =>
          simp [wR, wKR, v, concreteResidueRemoveFamilySpec, productionKeyOrderResult,
            removeAdministrativeIdentityResult]
          exact (concreteClosedKeyUniqueData RI).canonicalizeKey_unique _ _
    simpa [hEqCanon] using hwKRcanon
  refine ⟨v, hwRv, ?_⟩
  exact Relation.ReflTransGen.trans
    (Relation.ReflTransGen.single
      (ResidueProductionStep.mk .administrative_identity_contraction
        (productionKeyOrderResult (concreteClosedKeyData RI) w hK)
        (show ((concreteClosedResidueFamilySpecs RI).family
            .administrative_identity_contraction).applies
            (productionKeyOrderResult (concreteClosedKeyData RI) w hK) from hRK)))
    hwKRv

private theorem boundary_tensor_critical_pair_join
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    {w : FrontierWord (concreteClosedSetup RI)}
    (hB : ((concreteClosedResidueFamilySpecs RI).family
      .boundary_admin_canonicalize).applies w)
    (hT : ((concreteClosedResidueFamilySpecs RI).family
      .tensor_factor_order_canonicalize).applies w) :
    ∃ v : FrontierWord (concreteClosedSetup RI),
      ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI)
        (((concreteClosedResidueFamilySpecs RI).family
            .boundary_admin_canonicalize).result w hB) v ∧
      ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI)
        (((concreteClosedResidueFamilySpecs RI).family
            .tensor_factor_order_canonicalize).result w hT) v := by
  let wB := ((concreteClosedResidueFamilySpecs RI).family .boundary_admin_canonicalize).result w hB
  let wT := ((concreteClosedResidueFamilySpecs RI).family .tensor_factor_order_canonicalize).result w hT
  have hTB : ((concreteClosedResidueFamilySpecs RI).family
      .tensor_factor_order_canonicalize).applies wB := by
    simpa [concreteClosedResidueFamilySpecs, residueProductionFamilySpecs_concrete_closed,
      concreteClosedBoundaryData, productionBoundaryAdminResult, productionTensorFactorOrderApplies,
      wB]
      using hT
  have hBT : ((concreteClosedResidueFamilySpecs RI).family
      .boundary_admin_canonicalize).applies wT := by
    simpa [concreteClosedResidueFamilySpecs, residueProductionFamilySpecs_concrete_closed,
      concreteClosedTensorData, productionTensorFactorOrderResult, productionBoundaryAdminApplies,
      wT]
      using hB
  let v := ((concreteClosedResidueFamilySpecs RI).family .tensor_factor_order_canonicalize).result wB hTB
  refine ⟨v, ?_, ?_⟩
  · exact Relation.ReflTransGen.single
      (ResidueProductionStep.mk .tensor_factor_order_canonicalize wB hTB)
  · have hEq : ((concreteClosedResidueFamilySpecs RI).family .boundary_admin_canonicalize).result wT hBT = v := by
      simp [concreteClosedResidueFamilySpecs, residueProductionFamilySpecs_concrete_closed,
        concreteClosedBoundaryData, concreteClosedTensorData, productionBoundaryAdminResult,
        productionTensorFactorOrderResult, wB, wT, v]
    simpa [hEq, v] using
      (Relation.ReflTransGen.single
        (ResidueProductionStep.mk .boundary_admin_canonicalize wT hBT))

private theorem boundary_key_critical_pair_join
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    {w : FrontierWord (concreteClosedSetup RI)}
    (hB : ((concreteClosedResidueFamilySpecs RI).family
      .boundary_admin_canonicalize).applies w)
    (hK : ((concreteClosedResidueFamilySpecs RI).family
      .key_order_canonicalize).applies w) :
    ∃ v : FrontierWord (concreteClosedSetup RI),
      ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI)
        (((concreteClosedResidueFamilySpecs RI).family
            .boundary_admin_canonicalize).result w hB) v ∧
      ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI)
        (((concreteClosedResidueFamilySpecs RI).family
            .key_order_canonicalize).result w hK) v := by
  let wB := ((concreteClosedResidueFamilySpecs RI).family .boundary_admin_canonicalize).result w hB
  let wK := ((concreteClosedResidueFamilySpecs RI).family .key_order_canonicalize).result w hK
  have hKB : ((concreteClosedResidueFamilySpecs RI).family
      .key_order_canonicalize).applies wB := by
    simpa [concreteClosedResidueFamilySpecs, residueProductionFamilySpecs_concrete_closed,
      concreteClosedBoundaryData, productionBoundaryAdminResult, productionKeyOrderApplies,
      wB]
      using hK
  have hBK : ((concreteClosedResidueFamilySpecs RI).family
      .boundary_admin_canonicalize).applies wK := by
    simpa [concreteClosedResidueFamilySpecs, residueProductionFamilySpecs_concrete_closed,
      concreteClosedKeyData, productionKeyOrderResult, productionBoundaryAdminApplies,
      wK]
      using hB
  let v := ((concreteClosedResidueFamilySpecs RI).family .key_order_canonicalize).result wB hKB
  refine ⟨v, ?_, ?_⟩
  · exact Relation.ReflTransGen.single
      (ResidueProductionStep.mk .key_order_canonicalize wB hKB)
  · have hEq : ((concreteClosedResidueFamilySpecs RI).family .boundary_admin_canonicalize).result wK hBK = v := by
      simp [concreteClosedResidueFamilySpecs, residueProductionFamilySpecs_concrete_closed,
        concreteClosedBoundaryData, concreteClosedKeyData, productionBoundaryAdminResult,
        productionKeyOrderResult, wB, wK, v]
    simpa [hEq, v] using
      (Relation.ReflTransGen.single
        (ResidueProductionStep.mk .boundary_admin_canonicalize wK hBK))

private theorem boundary_expose_critical_pair_join
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    {w : FrontierWord (concreteClosedSetup RI)}
    (hB : ((concreteClosedResidueFamilySpecs RI).family .boundary_admin_canonicalize).applies w)
    (hE : ((concreteClosedResidueFamilySpecs RI).family .expose_boundary_block_swap).applies w) :
    ∃ v : FrontierWord (concreteClosedSetup RI),
      ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI)
        (((concreteClosedResidueFamilySpecs RI).family .boundary_admin_canonicalize).result w hB) v ∧
      ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI)
        (((concreteClosedResidueFamilySpecs RI).family .expose_boundary_block_swap).result w hE) v := by
  let wB := ((concreteClosedResidueFamilySpecs RI).family .boundary_admin_canonicalize).result w hB
  let wE := ((concreteClosedResidueFamilySpecs RI).family .expose_boundary_block_swap).result w hE
  have hEB : ((concreteClosedResidueFamilySpecs RI).family .expose_boundary_block_swap).applies wB := by
    simpa [concreteClosedResidueFamilySpecs, residueProductionFamilySpecs_concrete_closed,
      concreteClosedBoundaryData, productionBoundaryAdminResult, concreteResidueExposeFamilySpec, wB] using hE
  have hBE : ((concreteClosedResidueFamilySpecs RI).family .boundary_admin_canonicalize).applies wE := by
    simpa [concreteClosedResidueFamilySpecs, residueProductionFamilySpecs_concrete_closed,
      concreteClosedBoundaryData, productionBoundaryAdminApplies, concreteResidueExposeFamilySpec, wE] using hB
  let v := ((concreteClosedResidueFamilySpecs RI).family .expose_boundary_block_swap).result wB hEB
  refine ⟨v, ?_, ?_⟩
  · exact Relation.ReflTransGen.single (ResidueProductionStep.mk .expose_boundary_block_swap wB hEB)
  · have hEq : ((concreteClosedResidueFamilySpecs RI).family .boundary_admin_canonicalize).result wE hBE = v := by
      simp [concreteClosedResidueFamilySpecs, residueProductionFamilySpecs_concrete_closed,
        concreteClosedBoundaryData, productionBoundaryAdminResult, concreteResidueExposeFamilySpec, wB, wE, v]
    simpa [hEq, v] using
      (Relation.ReflTransGen.single (ResidueProductionStep.mk .boundary_admin_canonicalize wE hBE))

private theorem tensor_key_critical_pair_join
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    {w : FrontierWord (concreteClosedSetup RI)}
    (hT : ((concreteClosedResidueFamilySpecs RI).family .tensor_factor_order_canonicalize).applies w)
    (hK : ((concreteClosedResidueFamilySpecs RI).family .key_order_canonicalize).applies w) :
    ∃ v : FrontierWord (concreteClosedSetup RI),
      ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI)
        (((concreteClosedResidueFamilySpecs RI).family .tensor_factor_order_canonicalize).result w hT) v ∧
      ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI)
        (((concreteClosedResidueFamilySpecs RI).family .key_order_canonicalize).result w hK) v := by
  let wT := ((concreteClosedResidueFamilySpecs RI).family .tensor_factor_order_canonicalize).result w hT
  let wK := ((concreteClosedResidueFamilySpecs RI).family .key_order_canonicalize).result w hK
  have hKT : ((concreteClosedResidueFamilySpecs RI).family .key_order_canonicalize).applies wT := by
    simpa [concreteClosedResidueFamilySpecs, residueProductionFamilySpecs_concrete_closed,
      concreteClosedTensorData, productionTensorFactorOrderResult, productionKeyOrderApplies, wT] using hK
  have hTK : ((concreteClosedResidueFamilySpecs RI).family .tensor_factor_order_canonicalize).applies wK := by
    simpa [concreteClosedResidueFamilySpecs, residueProductionFamilySpecs_concrete_closed,
      concreteClosedKeyData, productionKeyOrderResult, productionTensorFactorOrderApplies, wK] using hT
  let v := ((concreteClosedResidueFamilySpecs RI).family .key_order_canonicalize).result wT hKT
  refine ⟨v, ?_, ?_⟩
  · exact Relation.ReflTransGen.single (ResidueProductionStep.mk .key_order_canonicalize wT hKT)
  · have hEq : ((concreteClosedResidueFamilySpecs RI).family .tensor_factor_order_canonicalize).result wK hTK = v := by
      simp [concreteClosedResidueFamilySpecs, residueProductionFamilySpecs_concrete_closed,
        concreteClosedTensorData, concreteClosedKeyData, productionTensorFactorOrderResult,
        productionKeyOrderResult, wT, wK, v]
    simpa [hEq, v] using
      (Relation.ReflTransGen.single (ResidueProductionStep.mk .tensor_factor_order_canonicalize wK hTK))

private theorem tensor_expose_critical_pair_join
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    {w : FrontierWord (concreteClosedSetup RI)}
    (hT : ((concreteClosedResidueFamilySpecs RI).family .tensor_factor_order_canonicalize).applies w)
    (hE : ((concreteClosedResidueFamilySpecs RI).family .expose_boundary_block_swap).applies w) :
    ∃ v : FrontierWord (concreteClosedSetup RI),
      ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI)
        (((concreteClosedResidueFamilySpecs RI).family .tensor_factor_order_canonicalize).result w hT) v ∧
      ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI)
        (((concreteClosedResidueFamilySpecs RI).family .expose_boundary_block_swap).result w hE) v := by
  let wT := ((concreteClosedResidueFamilySpecs RI).family .tensor_factor_order_canonicalize).result w hT
  let wE := ((concreteClosedResidueFamilySpecs RI).family .expose_boundary_block_swap).result w hE
  have hET : ((concreteClosedResidueFamilySpecs RI).family .expose_boundary_block_swap).applies wT := by
    simpa [concreteClosedResidueFamilySpecs, residueProductionFamilySpecs_concrete_closed,
      concreteClosedTensorData, productionTensorFactorOrderResult, concreteResidueExposeFamilySpec, wT] using hE
  have hTE : ((concreteClosedResidueFamilySpecs RI).family .tensor_factor_order_canonicalize).applies wE := by
    simpa [concreteClosedResidueFamilySpecs, residueProductionFamilySpecs_concrete_closed,
      concreteClosedTensorData, productionTensorFactorOrderApplies, concreteResidueExposeFamilySpec, wE] using hT
  let v := ((concreteClosedResidueFamilySpecs RI).family .expose_boundary_block_swap).result wT hET
  refine ⟨v, ?_, ?_⟩
  · exact Relation.ReflTransGen.single (ResidueProductionStep.mk .expose_boundary_block_swap wT hET)
  · have hEq : ((concreteClosedResidueFamilySpecs RI).family .tensor_factor_order_canonicalize).result wE hTE = v := by
      simp [concreteClosedResidueFamilySpecs, residueProductionFamilySpecs_concrete_closed,
        concreteClosedTensorData, productionTensorFactorOrderResult, concreteResidueExposeFamilySpec, wT, wE, v]
    simpa [hEq, v] using
      (Relation.ReflTransGen.single (ResidueProductionStep.mk .tensor_factor_order_canonicalize wE hTE))

private theorem key_expose_critical_pair_join
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    {w : FrontierWord (concreteClosedSetup RI)}
    (hK : ((concreteClosedResidueFamilySpecs RI).family .key_order_canonicalize).applies w)
    (hE : ((concreteClosedResidueFamilySpecs RI).family .expose_boundary_block_swap).applies w) :
    ∃ v : FrontierWord (concreteClosedSetup RI),
      ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI)
        (((concreteClosedResidueFamilySpecs RI).family .key_order_canonicalize).result w hK) v ∧
      ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI)
        (((concreteClosedResidueFamilySpecs RI).family .expose_boundary_block_swap).result w hE) v := by
  let wK := ((concreteClosedResidueFamilySpecs RI).family .key_order_canonicalize).result w hK
  let wE := ((concreteClosedResidueFamilySpecs RI).family .expose_boundary_block_swap).result w hE
  have hEK : ((concreteClosedResidueFamilySpecs RI).family .expose_boundary_block_swap).applies wK := by
    simpa [concreteClosedResidueFamilySpecs, residueProductionFamilySpecs_concrete_closed,
      concreteClosedKeyData, productionKeyOrderResult, concreteResidueExposeFamilySpec, wK] using hE
  have hKE : ((concreteClosedResidueFamilySpecs RI).family .key_order_canonicalize).applies wE := by
    simpa [concreteClosedResidueFamilySpecs, residueProductionFamilySpecs_concrete_closed,
      concreteClosedKeyData, productionKeyOrderApplies, concreteResidueExposeFamilySpec, wE] using hK
  let v := ((concreteClosedResidueFamilySpecs RI).family .expose_boundary_block_swap).result wK hEK
  refine ⟨v, ?_, ?_⟩
  · exact Relation.ReflTransGen.single (ResidueProductionStep.mk .expose_boundary_block_swap wK hEK)
  · have hEq : ((concreteClosedResidueFamilySpecs RI).family .key_order_canonicalize).result wE hKE = v := by
      simp [concreteClosedResidueFamilySpecs, residueProductionFamilySpecs_concrete_closed,
        concreteClosedKeyData, productionKeyOrderResult, concreteResidueExposeFamilySpec, wK, wE, v]
    simpa [hEq, v] using
      (Relation.ReflTransGen.single (ResidueProductionStep.mk .key_order_canonicalize wE hKE))

private theorem boundary_remove_critical_pair_join
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    {w : FrontierWord (concreteClosedSetup RI)}
    (hB : ((concreteClosedResidueFamilySpecs RI).family .boundary_admin_canonicalize).applies w)
    (hR : ((concreteClosedResidueFamilySpecs RI).family .administrative_identity_contraction).applies w) :
    ∃ v : FrontierWord (concreteClosedSetup RI),
      ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI)
        (((concreteClosedResidueFamilySpecs RI).family .boundary_admin_canonicalize).result w hB) v ∧
      ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI)
        (((concreteClosedResidueFamilySpecs RI).family .administrative_identity_contraction).result w hR) v := by
  let wB := ((concreteClosedResidueFamilySpecs RI).family .boundary_admin_canonicalize).result w hB
  let wR := ((concreteClosedResidueFamilySpecs RI).family .administrative_identity_contraction).result w hR
  have hRB : ((concreteClosedResidueFamilySpecs RI).family .administrative_identity_contraction).applies wB := by
    simpa [concreteClosedResidueFamilySpecs, residueProductionFamilySpecs_concrete_closed,
      concreteClosedBoundaryData, concreteResidueRemoveFamilySpec, productionBoundaryAdminResult, wB] using
      concreteResidueRemove_applies_after_boundary (concreteClosedBoundaryData RI)
        (show (concreteResidueRemoveFamilySpec (concreteClosedSetup RI)).applies w from hR)
        (show productionBoundaryAdminApplies (concreteClosedBoundaryData RI) w from hB)
  have hBR : ((concreteClosedResidueFamilySpecs RI).family .boundary_admin_canonicalize).applies wR := by
    dsimp [wR]
    change (concreteClosedBoundaryData RI).canonicalizeY
        ((concreteResidueRemoveFamilySpec (concreteClosedSetup RI)).result w
          (show (concreteResidueRemoveFamilySpec (concreteClosedSetup RI)).applies w from hR)).residue.Y ≠
      ((concreteResidueRemoveFamilySpec (concreteClosedSetup RI)).result w
        (show (concreteResidueRemoveFamilySpec (concreteClosedSetup RI)).applies w from hR)).residue.Y
    rw [concreteResidueRemove_preserves_Y w
      (show (concreteResidueRemoveFamilySpec (concreteClosedSetup RI)).applies w from hR)]
    exact (show (concreteClosedBoundaryData RI).canonicalizeY w.residue.Y ≠ w.residue.Y from hB)
  let v := ((concreteClosedResidueFamilySpecs RI).family .administrative_identity_contraction).result wB hRB
  have hEq : ((concreteClosedResidueFamilySpecs RI).family .boundary_admin_canonicalize).result wR hBR = v := by
    simpa [concreteClosedResidueFamilySpecs, residueProductionFamilySpecs_concrete_closed,
      concreteClosedBoundaryData, concreteResidueRemoveFamilySpec, productionBoundaryAdminResult, wB, wR, v]
      using (concreteResidueBoundary_after_remove_eq_remove_after_boundary
        (concreteClosedBoundaryData RI)
        (show (concreteResidueRemoveFamilySpec (concreteClosedSetup RI)).applies w from hR)
        (show productionBoundaryAdminApplies (concreteClosedBoundaryData RI) w from hB))
  refine ⟨v, ?_, ?_⟩
  · exact Relation.ReflTransGen.single (ResidueProductionStep.mk .administrative_identity_contraction wB hRB)
  · simpa [v, hEq] using
      (Relation.ReflTransGen.single (ResidueProductionStep.mk .boundary_admin_canonicalize wR hBR))

private theorem expose_remove_critical_pair_join
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    {w : FrontierWord (concreteClosedSetup RI)}
    (hE : ((concreteClosedResidueFamilySpecs RI).family .expose_boundary_block_swap).applies w)
    (hR : ((concreteClosedResidueFamilySpecs RI).family .administrative_identity_contraction).applies w) :
    ∃ v : FrontierWord (concreteClosedSetup RI),
      ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI)
        (((concreteClosedResidueFamilySpecs RI).family .expose_boundary_block_swap).result w hE) v ∧
      ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI)
        (((concreteClosedResidueFamilySpecs RI).family .administrative_identity_contraction).result w hR) v := by
  let wE := ((concreteClosedResidueFamilySpecs RI).family .expose_boundary_block_swap).result w hE
  let wR := ((concreteClosedResidueFamilySpecs RI).family .administrative_identity_contraction).result w hR
  have hRE : ((concreteClosedResidueFamilySpecs RI).family .administrative_identity_contraction).applies wE := by
    simpa [concreteClosedResidueFamilySpecs, residueProductionFamilySpecs_concrete_closed,
      concreteResidueRemoveFamilySpec, concreteResidueExposeFamilySpec, wE] using
      concreteResidueRemove_applies_after_expose
        (show (concreteResidueRemoveFamilySpec (concreteClosedSetup RI)).applies w from hR)
        (show (concreteResidueExposeFamilySpec (setup := concreteClosedSetup RI)).applies w from hE)
  have hER : ((concreteClosedResidueFamilySpecs RI).family .expose_boundary_block_swap).applies wR := by
    dsimp [wR]
    change 0 < invCount
      (((concreteResidueRemoveFamilySpec (concreteClosedSetup RI)).result w
          (show (concreteResidueRemoveFamilySpec (concreteClosedSetup RI)).applies w from hR)).residue.ports.externalOut)
    rw [concreteResidueRemove_preserves_externalOut w
      (show (concreteResidueRemoveFamilySpec (concreteClosedSetup RI)).applies w from hR)]
    exact (show 0 < invCount w.residue.ports.externalOut from hE)
  let v := ((concreteClosedResidueFamilySpecs RI).family .administrative_identity_contraction).result wE hRE
  have hEq : ((concreteClosedResidueFamilySpecs RI).family .expose_boundary_block_swap).result wR hER = v := by
    simpa [concreteClosedResidueFamilySpecs, residueProductionFamilySpecs_concrete_closed,
      concreteResidueRemoveFamilySpec, concreteResidueExposeFamilySpec, wE, wR, v]
      using (concreteResidueExpose_after_remove_eq_remove_after_expose
        (show (concreteResidueRemoveFamilySpec (concreteClosedSetup RI)).applies w from hR)
        (show (concreteResidueExposeFamilySpec (setup := concreteClosedSetup RI)).applies w from hE))
  refine ⟨v, ?_, ?_⟩
  · exact Relation.ReflTransGen.single (ResidueProductionStep.mk .administrative_identity_contraction wE hRE)
  · simpa [v, hEq] using
      (Relation.ReflTransGen.single (ResidueProductionStep.mk .expose_boundary_block_swap wR hER))

/-- Concrete corrected residue JP for the closed six-family route.

This is the concrete-production non-disjoint join primitive for the corrected
residue path. The legacy seven-family production route is separate; compose is
trace/provenance-layer only, and remove is the corrected residue contraction
family. -/
noncomputable def residueProductionJoinEnvPrimitive_concrete_closed
    (RI : Type u) [DecidableEq RI] [LinearOrder RI] :
    ResidueProductionJoinEnvPrimitive (concreteClosedResidueFamilySpecs RI) where
  join_all_non_disjoint := by
    set_option maxHeartbeats 800000 in
    intro i₁ i₂ w h₁ h₂ hNonDisjoint
    cases i₁ <;> cases i₂
    case boundary_admin_canonicalize.boundary_admin_canonicalize =>
      refine ⟨((concreteClosedResidueFamilySpecs RI).family
        .boundary_admin_canonicalize).result w h₁, ?_, ?_⟩
      · exact (show ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI)
        (((concreteClosedResidueFamilySpecs RI).family
          .boundary_admin_canonicalize).result w h₁)
        (((concreteClosedResidueFamilySpecs RI).family
          .boundary_admin_canonicalize).result w h₁) from
        Relation.ReflTransGen.refl)
      · have hh : h₂ = h₁ := Subsingleton.elim _ _
        cases hh
        exact (show ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI)
          (((concreteClosedResidueFamilySpecs RI).family
            .boundary_admin_canonicalize).result w h₁)
          (((concreteClosedResidueFamilySpecs RI).family
            .boundary_admin_canonicalize).result w h₁) from
          Relation.ReflTransGen.refl)
    case boundary_admin_canonicalize.dependency_order_canonicalize =>
      exact False.elim (by
        simpa [concreteClosedResidueFamilySpecs, residueProductionFamilySpecs_concrete_closed,
          concreteClosedDependencyData, trivialDependencyOrderCanonicalizeData,
          productionDependencyOrderApplies] using h₂)
    case boundary_admin_canonicalize.expose_boundary_block_swap =>
      exact boundary_expose_critical_pair_join RI h₁ h₂
    case boundary_admin_canonicalize.administrative_identity_contraction =>
      exact boundary_remove_critical_pair_join RI h₁ h₂
    case dependency_order_canonicalize.boundary_admin_canonicalize =>
      exact False.elim (by
        simpa [concreteClosedResidueFamilySpecs, residueProductionFamilySpecs_concrete_closed,
          concreteClosedDependencyData, trivialDependencyOrderCanonicalizeData,
          productionDependencyOrderApplies] using h₁)
    case dependency_order_canonicalize.dependency_order_canonicalize =>
      exact False.elim (h₁ rfl)
    case dependency_order_canonicalize.administrative_identity_contraction =>
      exact False.elim (by
        simpa [concreteClosedResidueFamilySpecs, residueProductionFamilySpecs_concrete_closed,
          concreteClosedDependencyData, trivialDependencyOrderCanonicalizeData,
          productionDependencyOrderApplies] using h₁)
    case boundary_admin_canonicalize.tensor_factor_order_canonicalize =>
      exact boundary_tensor_critical_pair_join RI h₁ h₂
    case tensor_factor_order_canonicalize.boundary_admin_canonicalize =>
      simpa [and_comm] using boundary_tensor_critical_pair_join RI h₂ h₁
    case dependency_order_canonicalize.tensor_factor_order_canonicalize =>
      exact False.elim (by
        simpa [concreteClosedResidueFamilySpecs, residueProductionFamilySpecs_concrete_closed,
          concreteClosedDependencyData, trivialDependencyOrderCanonicalizeData,
          productionDependencyOrderApplies] using h₁)
    case dependency_order_canonicalize.key_order_canonicalize =>
      exact False.elim (by
        simpa [concreteClosedResidueFamilySpecs, residueProductionFamilySpecs_concrete_closed,
          concreteClosedDependencyData, trivialDependencyOrderCanonicalizeData,
          productionDependencyOrderApplies] using h₁)
    case dependency_order_canonicalize.expose_boundary_block_swap =>
      exact False.elim (by
        simpa [concreteClosedResidueFamilySpecs, residueProductionFamilySpecs_concrete_closed,
          concreteClosedDependencyData, trivialDependencyOrderCanonicalizeData,
          productionDependencyOrderApplies] using h₁)
    case tensor_factor_order_canonicalize.dependency_order_canonicalize =>
      exact False.elim (by
        simpa [concreteClosedResidueFamilySpecs, residueProductionFamilySpecs_concrete_closed,
          concreteClosedDependencyData, trivialDependencyOrderCanonicalizeData,
          productionDependencyOrderApplies] using h₂)
    case tensor_factor_order_canonicalize.key_order_canonicalize =>
      exact tensor_key_critical_pair_join RI h₁ h₂
    case tensor_factor_order_canonicalize.expose_boundary_block_swap =>
      exact tensor_expose_critical_pair_join RI h₁ h₂
    case tensor_factor_order_canonicalize.tensor_factor_order_canonicalize =>
      refine ⟨((concreteClosedResidueFamilySpecs RI).family
        .tensor_factor_order_canonicalize).result w h₁, ?_, ?_⟩
      · exact (show ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI)
        (((concreteClosedResidueFamilySpecs RI).family
          .tensor_factor_order_canonicalize).result w h₁)
        (((concreteClosedResidueFamilySpecs RI).family
          .tensor_factor_order_canonicalize).result w h₁) from
        Relation.ReflTransGen.refl)
      · have hh : h₂ = h₁ := Subsingleton.elim _ _
        cases hh
        exact (show ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI)
          (((concreteClosedResidueFamilySpecs RI).family
            .tensor_factor_order_canonicalize).result w h₁)
          (((concreteClosedResidueFamilySpecs RI).family
            .tensor_factor_order_canonicalize).result w h₁) from
          Relation.ReflTransGen.refl)
    case tensor_factor_order_canonicalize.administrative_identity_contraction =>
      rcases remove_tensorOrder_critical_pair_join RI
        (show (concreteResidueRemoveFamilySpec (concreteClosedSetup RI)).applies w from h₂)
        (show productionTensorFactorOrderApplies (concreteClosedTensorData RI) w from h₁) with
        ⟨v, hvRemove, hvTensor⟩
      exact ⟨v, hvTensor, hvRemove⟩
    case boundary_admin_canonicalize.key_order_canonicalize =>
      exact boundary_key_critical_pair_join RI h₁ h₂
    case key_order_canonicalize.boundary_admin_canonicalize =>
      rcases boundary_key_critical_pair_join RI h₂ h₁ with ⟨v, hvBoundary, hvKey⟩
      exact ⟨v, hvKey, hvBoundary⟩
    case key_order_canonicalize.dependency_order_canonicalize =>
      exact False.elim (by
        simpa [concreteClosedResidueFamilySpecs, residueProductionFamilySpecs_concrete_closed,
          concreteClosedDependencyData, trivialDependencyOrderCanonicalizeData,
          productionDependencyOrderApplies] using h₂)
    case key_order_canonicalize.tensor_factor_order_canonicalize =>
      rcases tensor_key_critical_pair_join RI h₂ h₁ with ⟨v, hvTensor, hvKey⟩
      exact ⟨v, hvKey, hvTensor⟩
    case key_order_canonicalize.expose_boundary_block_swap =>
      exact key_expose_critical_pair_join RI h₁ h₂
    case key_order_canonicalize.key_order_canonicalize =>
      refine ⟨((concreteClosedResidueFamilySpecs RI).family
        .key_order_canonicalize).result w h₁, ?_, ?_⟩
      · exact (show ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI)
        (((concreteClosedResidueFamilySpecs RI).family
          .key_order_canonicalize).result w h₁)
        (((concreteClosedResidueFamilySpecs RI).family
          .key_order_canonicalize).result w h₁) from
        Relation.ReflTransGen.refl)
      · have hh : h₂ = h₁ := Subsingleton.elim _ _
        cases hh
        exact (show ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI)
          (((concreteClosedResidueFamilySpecs RI).family
            .key_order_canonicalize).result w h₁)
          (((concreteClosedResidueFamilySpecs RI).family
            .key_order_canonicalize).result w h₁) from
          Relation.ReflTransGen.refl)
    case key_order_canonicalize.administrative_identity_contraction =>
      rcases remove_keyOrder_critical_pair_join RI
        (show (concreteResidueRemoveFamilySpec (concreteClosedSetup RI)).applies w from h₂)
        (show productionKeyOrderApplies (concreteClosedKeyData RI) w from h₁) with
        ⟨v, hvRemove, hvKey⟩
      exact ⟨v, hvKey, hvRemove⟩
    case expose_boundary_block_swap.expose_boundary_block_swap =>
      refine ⟨(concreteResidueExposeFamilySpec (setup := concreteClosedSetup RI)).result w h₁, ?_, ?_⟩
      · exact (show ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI)
            ((concreteResidueExposeFamilySpec (setup := concreteClosedSetup RI)).result w h₁)
            ((concreteResidueExposeFamilySpec (setup := concreteClosedSetup RI)).result w h₁) from
          Relation.ReflTransGen.refl)
      · have hh : h₂ = h₁ := Subsingleton.elim _ _
        cases hh
        exact (show ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI)
            ((concreteResidueExposeFamilySpec (setup := concreteClosedSetup RI)).result w h₁)
            ((concreteResidueExposeFamilySpec (setup := concreteClosedSetup RI)).result w h₁) from
          Relation.ReflTransGen.refl)
    case administrative_identity_contraction.dependency_order_canonicalize =>
      exact False.elim (by
        simpa [concreteClosedResidueFamilySpecs, residueProductionFamilySpecs_concrete_closed,
          concreteClosedDependencyData, trivialDependencyOrderCanonicalizeData,
          productionDependencyOrderApplies] using h₂)
    case administrative_identity_contraction.tensor_factor_order_canonicalize =>
      exact remove_tensorOrder_critical_pair_join RI h₁ h₂
    case administrative_identity_contraction.key_order_canonicalize =>
      exact remove_keyOrder_critical_pair_join RI h₁ h₂
    case expose_boundary_block_swap.boundary_admin_canonicalize =>
      rcases boundary_expose_critical_pair_join RI h₂ h₁ with ⟨v, hvBoundary, hvExpose⟩
      exact ⟨v, hvExpose, hvBoundary⟩
    case expose_boundary_block_swap.dependency_order_canonicalize =>
      exact False.elim (by
        simpa [concreteClosedResidueFamilySpecs, residueProductionFamilySpecs_concrete_closed,
          concreteClosedDependencyData, trivialDependencyOrderCanonicalizeData,
          productionDependencyOrderApplies] using h₂)
    case expose_boundary_block_swap.tensor_factor_order_canonicalize =>
      rcases tensor_expose_critical_pair_join RI h₂ h₁ with ⟨v, hvTensor, hvExpose⟩
      exact ⟨v, hvExpose, hvTensor⟩
    case expose_boundary_block_swap.key_order_canonicalize =>
      rcases key_expose_critical_pair_join RI h₂ h₁ with ⟨v, hvKey, hvExpose⟩
      exact ⟨v, hvExpose, hvKey⟩
    case expose_boundary_block_swap.administrative_identity_contraction =>
      exact expose_remove_critical_pair_join RI h₁ h₂
    case administrative_identity_contraction.boundary_admin_canonicalize =>
      rcases boundary_remove_critical_pair_join RI h₂ h₁ with ⟨v, hvBoundary, hvRemove⟩
      exact ⟨v, hvRemove, hvBoundary⟩
    case administrative_identity_contraction.expose_boundary_block_swap =>
      rcases expose_remove_critical_pair_join RI h₂ h₁ with ⟨v, hvExpose, hvRemove⟩
      exact ⟨v, hvRemove, hvExpose⟩
    case administrative_identity_contraction.administrative_identity_contraction =>
      refine ⟨(concreteResidueRemoveFamilySpec (concreteClosedSetup RI)).result w h₁, ?_, ?_⟩
      · exact (show ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI)
            ((concreteResidueRemoveFamilySpec (concreteClosedSetup RI)).result w h₁)
            ((concreteResidueRemoveFamilySpec (concreteClosedSetup RI)).result w h₁) from
          Relation.ReflTransGen.refl)
      · have hh : h₂ = h₁ := Subsingleton.elim _ _
        cases hh
        exact (show ResidueProductionMultiStep (concreteClosedResidueFamilySpecs RI)
            ((concreteResidueRemoveFamilySpec (concreteClosedSetup RI)).result w h₁)
            ((concreteResidueRemoveFamilySpec (concreteClosedSetup RI)).result w h₁) from
          Relation.ReflTransGen.refl)

/-- Final concrete-production CanNF closure for the corrected residue route.

This closes the corrected six-family residue path: boundary admin,
dependency/tensor/key canonicalizers, expose-boundary swap, and remove as
contraction. The legacy seven-family production route remains separate, and
compose is trace/provenance-layer only. -/
noncomputable def residueProductionCanNFObligations_concrete_closed
    (RI : Type u) [DecidableEq RI] [LinearOrder RI] :
    ResidueProductionCanNFObligations (concreteClosedSetup RI) :=
  residueProductionCanNFObligations_from_halves
    (concreteClosedResidueFamilySpecs RI)
    (residueProductionOperationalSideConditions_concrete_closed
      (setup := concreteClosedSetup RI)
      (concreteClosedBoundaryData RI)
      (concreteClosedDependencyData RI)
      (concreteClosedTensorData RI)
      (concreteClosedKeyData RI))
    (residueProductionJoinEnvPrimitive_concrete_closed RI)

/-- One corrected-residue canonicalization sweep on the concrete closed setup:
sort `externalOut`, canonicalize boundary `Y`, and canonicalize the dep/tensor/key
administrative data while leaving all other frontier-word fields unchanged. -/
noncomputable def correctedResidueCanonicalFrontierWord
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (w : FrontierWord (concreteBoundaryMinimalSetup RI)) :
    FrontierWord (concreteBoundaryMinimalSetup RI) :=
  { residue :=
      { w.residue with
        Y := (concreteClosedBoundaryData RI).canonicalizeY w.residue.Y
        dep := (concreteClosedDependencyData RI).canonicalizeDep w.residue.dep
        tensor := (concreteClosedTensorData RI).canonicalizeTensor w.residue.tensor
        key := (concreteClosedKeyData RI).canonicalizeKey w.residue.key
        ports :=
          { w.residue.ports with
            externalOut := w.residue.ports.externalOut.mergeSort } } }

@[simp] theorem correctedResidueCanonicalFrontierWord_residue_n
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (w : FrontierWord (concreteBoundaryMinimalSetup RI)) :
    (correctedResidueCanonicalFrontierWord RI w).residue.n = w.residue.n :=
  rfl

/-- On the closed concrete boundary model, `BoundaryAdminEquiv` collapses to
literal equality because the boundary canonicalizer is the identity. -/
theorem concreteClosedBoundary_eq_of_adminEquiv
    (RI : Type u) [DecidableEq RI]
    {Y₁ Y₂ : (concreteClosedSetup RI).BoundaryObject}
    (h : BoundaryAdminEquiv Y₁ Y₂) :
    Y₁ = Y₂ := by
  simpa [concreteClosedBoundaryData, concreteBoundaryCanonicalizeData] using
    (concreteBoundaryAdminCanonicalizeCongr_closed RI).canonicalizeY_congr Y₁ Y₂ h

private theorem frontierWordEquiv_preserves_correctedResidueCanonicalFrontierWord
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    {w₁ w₂ : FrontierWord (concreteBoundaryMinimalSetup RI)}
    (h : FrontierWord.Equiv w₁ w₂) :
    correctedResidueCanonicalFrontierWord RI w₁ =
      correctedResidueCanonicalFrontierWord RI w₂ := by
  obtain ⟨⟨n₁, X₁, Y₁, ports₁, pkts₁, dep₁, att₁, tensor₁, key₁⟩⟩ := w₁
  obtain ⟨⟨n₂, X₂, Y₂, ports₂, pkts₂, dep₂, att₂, tensor₂, key₂⟩⟩ := w₂
  obtain rfl := h.n_eq
  have hX : X₁ = X₂ := h.X_eq
  have hY : Y₁ = Y₂ := concreteClosedBoundary_eq_of_adminEquiv RI h.Y_rel
  have hIn : ports₁.externalIn = ports₂.externalIn := h.externalIn_eq
  have hExt : ports₁.externalOut.mergeSort = ports₂.externalOut.mergeSort :=
    sort_congr_perm_mergeSort h.externalOut_perm
  have hPacketIn : ports₁.packetIn = ports₂.packetIn := by
    funext i
    have hi := h.packetIn_eq i
    simpa using hi
  have hPacketOut : ports₁.packetOut = ports₂.packetOut := by
    funext i
    have hi := h.packetOut_eq i
    simpa using hi
  have hPackets : pkts₁ = pkts₂ := by
    funext i
    have hi := h.packets_eq i
    simpa using hi
  have hDepEdge : dep₁.edge = dep₂.edge := by
    funext i j
    have hij := h.dep_edge_eq i j
    simpa using hij
  have hDep : dep₁ = dep₂ := by
    rcases dep₁ with ⟨e₁, a₁⟩
    rcases dep₂ with ⟨e₂, a₂⟩
    simp only at hDepEdge
    subst hDepEdge
    congr 1
  have hAttach : att₁ = att₂ := by
    funext i
    have hi := h.attach_eq i
    simpa using hi
  have hTensor :
      (concreteClosedTensorData RI).canonicalizeTensor tensor₁ =
        (concreteClosedTensorData RI).canonicalizeTensor tensor₂ :=
    (concreteClosedTensorUniqueData RI).canonicalizeTensor_unique _ _
  have hKey :
      (concreteClosedKeyData RI).canonicalizeKey key₁ =
        (concreteClosedKeyData RI).canonicalizeKey key₂ :=
    (concreteClosedKeyUniqueData RI).canonicalizeKey_unique _ _
  simp [correctedResidueCanonicalFrontierWord, hX, hY, hIn, hExt,
    hPacketIn, hPacketOut, hPackets, hDep, hAttach, hTensor, hKey]

private theorem concreteResidueRemove_result_decreases
    {setup : RewriteCalculusSetup.{u}}
    (w : FrontierWord setup)
    (h : (concreteResidueRemoveFamilySpec setup).applies w) :
    ((concreteResidueRemoveFamilySpec setup).result w h).residue.n < w.residue.n := by
  rcases w with ⟨⟨m, X, Y, ports, packets, dep, attach, tensor, key⟩⟩
  cases m with
  | zero =>
      have hkFalse : False := by
        simpa using (Classical.choose h).2
      exact False.elim hkFalse
  | succ n =>
      simp [concreteResidueRemoveFamilySpec, removeAdministrativeIdentityResult]

/-- Concrete corrected-residue frontier normalizer.

At each stage, perform the explicit canonical frontier-word sweep and then, if an
administrative identity packet remains, contract it and recurse on the strictly
smaller packet count. This yields a concrete residue-specific normalizer without
routing through the global `FrontierWord.Equiv` interface. -/
noncomputable def correctedResidueNormalize
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (w : FrontierWord (concreteBoundaryMinimalSetup RI)) :
    FrontierWord (concreteBoundaryMinimalSetup RI) := by
  let canonical := correctedResidueCanonicalFrontierWord RI w
  by_cases hR : (concreteResidueRemoveFamilySpec (concreteBoundaryMinimalSetup RI)).applies canonical
  · exact correctedResidueNormalize RI
      ((concreteResidueRemoveFamilySpec (concreteBoundaryMinimalSetup RI)).result canonical hR)
  · exact canonical
termination_by w.residue.n
decreasing_by
  simp_wf
  simpa [correctedResidueCanonicalFrontierWord] using
    concreteResidueRemove_result_decreases
      (w := correctedResidueCanonicalFrontierWord RI w)
      hR

private noncomputable def correctedResidueNormalizeDescend
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (canonical : FrontierWord (concreteBoundaryMinimalSetup RI)) :
    FrontierWord (concreteBoundaryMinimalSetup RI) := by
  by_cases hR : (concreteResidueRemoveFamilySpec (concreteBoundaryMinimalSetup RI)).applies canonical
  · exact correctedResidueNormalize RI
      ((concreteResidueRemoveFamilySpec (concreteBoundaryMinimalSetup RI)).result canonical hR)
  · exact canonical

private theorem correctedResidueNormalize_eq_descend
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (w : FrontierWord (concreteBoundaryMinimalSetup RI)) :
    correctedResidueNormalize RI w =
      correctedResidueNormalizeDescend RI (correctedResidueCanonicalFrontierWord RI w) := by
  classical
  unfold correctedResidueNormalize correctedResidueNormalizeDescend
  rfl

private theorem correctedResidueNormalize_eq_of_canonical_eq
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    {w₁ w₂ : FrontierWord (concreteBoundaryMinimalSetup RI)}
    (hCanon : correctedResidueCanonicalFrontierWord RI w₁ =
      correctedResidueCanonicalFrontierWord RI w₂) :
    correctedResidueNormalize RI w₁ = correctedResidueNormalize RI w₂ := by
  rw [correctedResidueNormalize_eq_descend, correctedResidueNormalize_eq_descend]
  exact congrArg (correctedResidueNormalizeDescend RI) hCanon

/-- Precise residue-specific equality relation induced by the concrete corrected
residue normalizer. This is intentionally narrower than `FrontierWord.Equiv`:
it records equality after the corrected-residue canonical frontier-word pass. -/
def CorrectedResidueFrontierEquiv
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (w₁ w₂ : FrontierWord (concreteBoundaryMinimalSetup RI)) : Prop :=
  correctedResidueNormalize RI w₁ = correctedResidueNormalize RI w₂

/-- Campaign-1 CanNF alias for the concrete corrected-residue normalizer.

This names the concrete normal form at the exact scope currently justified by
the corrected-residue production closure, without claiming completeness for the
broader `FrontierWord.Equiv` relation. -/
noncomputable abbrev correctedResidueCanNF
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (w : FrontierWord (concreteBoundaryMinimalSetup RI)) :
    FrontierWord (concreteBoundaryMinimalSetup RI) :=
  correctedResidueNormalize RI w

/-- Equality detection for the concrete corrected-residue frontier normalizer:
the residue-specific equivalence is exactly equality of normalized frontier
words. -/
theorem correctedResidueNormalize_eq_iff
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (w₁ w₂ : FrontierWord (concreteBoundaryMinimalSetup RI)) :
    correctedResidueNormalize RI w₁ = correctedResidueNormalize RI w₂ ↔
      CorrectedResidueFrontierEquiv RI w₁ w₂ := by
  rfl

/-- Campaign-1 narrow equality theorem: the corrected-residue equivalence is
exactly equality of the corrected-residue CanNF outputs. This is the precise
frontier-word equality relation decided by the corrected-residue CanNF route. -/
theorem correctedResidueFrontierEquiv_iff_correctedResidueCanNF_eq
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (w₁ w₂ : FrontierWord (concreteBoundaryMinimalSetup RI)) :
    CorrectedResidueFrontierEquiv RI w₁ w₂ ↔
      correctedResidueCanNF RI w₁ = correctedResidueCanNF RI w₂ := by
  rfl

/-- Corrected residue as a genuine relative normalizer: the chosen frontier
relation is exactly the equality relation detected by the concrete
corrected-residue normal form. This does not hide missing mathematics; it
packages the mathematics already proved on the corrected-residue path as an
instance of the generic relative-normalizer interface. -/
noncomputable def correctedResidueFrontierWordRelativeNormalizer
    (RI : Type u) [DecidableEq RI] [LinearOrder RI] :
    FrontierWordRelativeNormalizer
      (concreteBoundaryMinimalSetup RI)
      (CorrectedResidueFrontierEquiv RI) where
  NF := FrontierWord (concreteBoundaryMinimalSetup RI)
  normalize := correctedResidueCanNF RI
  sound := by
    intro w₁ w₂ h
    exact h
  complete := by
    intro w₁ w₂ h
    exact h

/-- Record-facing corrected-residue relative CanNF package.

This is the concrete specialization of the generic `RelativeCanNF` scaffold to
the corrected-residue relation on the canonical completed-record assignment.
It presents corrected residue as a theorem package on completed
reconstructions, not merely as a raw frontier-word normalization function. -/
noncomputable def correctedResidueRelativeCanNF
    (RI : Type u) [DecidableEq RI] [LinearOrder RI] :
    RelativeCanNF
      (concreteBoundaryMinimalSetup RI)
      (CorrectedResidueFrontierEquiv RI) :=
  FrontierWordRelativeCanNF
    (setup := concreteBoundaryMinimalSetup RI)
    (CorrectedResidueFrontierEquiv RI)
    (correctedResidueFrontierWordRelativeNormalizer RI)

@[simp] theorem correctedResidueRelativeCanNF_normalize
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (R : CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI)) :
    (correctedResidueRelativeCanNF RI).normalize R =
      correctedResidueCanNF RI (FrontierWord.ofResidue R) :=
  rfl

theorem correctedResidueRelativeCanNF_normalize_eq_iff
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (R₁ R₂ : CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI)) :
    (correctedResidueRelativeCanNF RI).normalize R₁ =
        (correctedResidueRelativeCanNF RI).normalize R₂ ↔
      CorrectedResidueFrontierEquiv RI (FrontierWord.ofResidue R₁) (FrontierWord.ofResidue R₂) := by
  simpa [correctedResidueRelativeCanNF]
    using frontierWordRelativeCanNF_normalize_eq_iff_rel
      (setup := concreteBoundaryMinimalSetup RI)
      (CorrectedResidueFrontierEquiv RI)
      (correctedResidueFrontierWordRelativeNormalizer RI)
      R₁ R₂

/-- The corrected-residue record-facing package uses exactly the canonical
identity-holography assignment `R ↦ FrontierWord.ofResidue R`. This is the
concrete compatibility needed to instantiate the abstract package theorems on
the corrected-residue path. -/
theorem correctedResidueRelativeCanNF_assignment_matches_identity_holography
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (R : CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI)) :
    ((correctedResidueRelativeCanNF RI).assignment.assign R).frontier =
      FrontierWord.ofResidue R :=
  rfl

/-- Direct frontier-word form of the corrected-residue soundness theorem.

Unlike the earlier trace-facing statement, this lives purely on the projected
frontier carrier and will be used to define the honest stronger frontier-word
relation detected by `correctedResidueCanNF`. -/
theorem frontierWordEquiv_preservesCorrectedResidueCanNF_onFrontierWords
  (RI : Type u) [DecidableEq RI] [LinearOrder RI]
  {w₁ w₂ : FrontierWord (concreteBoundaryMinimalSetup RI)}
  (h : FrontierWord.Equiv w₁ w₂) :
  correctedResidueCanNF RI w₁ = correctedResidueCanNF RI w₂ := by
  exact correctedResidueNormalize_eq_of_canonical_eq RI
    (frontierWordEquiv_preserves_correctedResidueCanonicalFrontierWord RI h)

/-- Plain frontier-word equivalence is sound for the corrected-residue
relative normalizer, so the corrected-residue relation is a genuine special
case of the generic relation-parameterized engine theorems. -/
theorem frontierWordEquiv_preservesCorrectedResidueFrontierEquiv
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    {w₁ w₂ : FrontierWord (concreteBoundaryMinimalSetup RI)}
    (h : FrontierWord.Equiv w₁ w₂) :
    CorrectedResidueFrontierEquiv RI w₁ w₂ :=
  (correctedResidueFrontierEquiv_iff_correctedResidueCanNF_eq RI _ _).2
    (frontierWordEquiv_preservesCorrectedResidueCanNF_onFrontierWords RI h)

/-- Honest stronger frontier-word equality candidate.

This is the smallest explicit relation on frontier words generated by the two
closed downstairs move families currently available:

1. exact corrected-residue equality (`CorrectedResidueFrontierEquiv`), and
2. plain projection-level `FrontierWord.Equiv`.

The upstairs trace-compression generator does not add a new frontier-word
generator, because it preserves the projected frontier word literally. -/
inductive GeneratedFrontierEquiv
  (RI : Type u) [DecidableEq RI] [LinearOrder RI] :
  FrontierWord (concreteBoundaryMinimalSetup RI) →
    FrontierWord (concreteBoundaryMinimalSetup RI) → Prop where
  | of_correctedResidueFrontierEquiv
    {w₁ w₂ : FrontierWord (concreteBoundaryMinimalSetup RI)} :
    CorrectedResidueFrontierEquiv RI w₁ w₂ →
    GeneratedFrontierEquiv RI w₁ w₂
  | of_projectionFrontierEquiv
    {w₁ w₂ : FrontierWord (concreteBoundaryMinimalSetup RI)} :
    FrontierWord.Equiv w₁ w₂ → GeneratedFrontierEquiv RI w₁ w₂
  | refl (w : FrontierWord (concreteBoundaryMinimalSetup RI)) :
    GeneratedFrontierEquiv RI w w
  | symm {w₁ w₂ : FrontierWord (concreteBoundaryMinimalSetup RI)} :
    GeneratedFrontierEquiv RI w₁ w₂ → GeneratedFrontierEquiv RI w₂ w₁
  | trans {w₁ w₂ w₃ : FrontierWord (concreteBoundaryMinimalSetup RI)} :
    GeneratedFrontierEquiv RI w₁ w₂ →
    GeneratedFrontierEquiv RI w₂ w₃ →
      GeneratedFrontierEquiv RI w₁ w₃

/-- The stronger frontier-word relation still factors through corrected-residue
CanNF equality. -/
theorem generatedFrontierEquiv_preservesCorrectedResidueCanNF
  (RI : Type u) [DecidableEq RI] [LinearOrder RI]
  {w₁ w₂ : FrontierWord (concreteBoundaryMinimalSetup RI)}
  (h : GeneratedFrontierEquiv RI w₁ w₂) :
  correctedResidueCanNF RI w₁ = correctedResidueCanNF RI w₂ := by
  induction h with
  | of_correctedResidueFrontierEquiv hEq =>
    exact (correctedResidueFrontierEquiv_iff_correctedResidueCanNF_eq RI _ _).1 hEq
  | of_projectionFrontierEquiv hProj =>
    exact frontierWordEquiv_preservesCorrectedResidueCanNF_onFrontierWords RI hProj
  | refl _ =>
    rfl
  | symm _ ih =>
    exact ih.symm
  | trans _ _ ih12 ih23 =>
    exact Eq.trans ih12 ih23

/-- Equality of corrected-residue CanNF outputs already generates the stronger
frontier-word relation. -/
theorem generatedFrontierEquiv_of_correctedResidueCanNF_eq
  (RI : Type u) [DecidableEq RI] [LinearOrder RI]
  {w₁ w₂ : FrontierWord (concreteBoundaryMinimalSetup RI)}
  (h : correctedResidueCanNF RI w₁ = correctedResidueCanNF RI w₂) :
  GeneratedFrontierEquiv RI w₁ w₂ :=
  GeneratedFrontierEquiv.of_correctedResidueFrontierEquiv
  ((correctedResidueFrontierEquiv_iff_correctedResidueCanNF_eq RI w₁ w₂).2 h)

/-- The stronger frontier-word relation is exactly detected by corrected-residue
CanNF equality. -/
theorem generatedFrontierEquiv_iff_correctedResidueCanNF_eq
  (RI : Type u) [DecidableEq RI] [LinearOrder RI]
  {w₁ w₂ : FrontierWord (concreteBoundaryMinimalSetup RI)} :
  GeneratedFrontierEquiv RI w₁ w₂ ↔
    correctedResidueCanNF RI w₁ = correctedResidueCanNF RI w₂ :=
  ⟨generatedFrontierEquiv_preservesCorrectedResidueCanNF RI,
  generatedFrontierEquiv_of_correctedResidueCanNF_eq RI⟩

/-- Plain `FrontierWord.Equiv` sits inside the honest stronger frontier-word
relation as a generating move. -/
theorem generatedFrontierEquiv_of_frontierWordEquiv
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    {w₁ w₂ : FrontierWord (concreteBoundaryMinimalSetup RI)}
    (h : FrontierWord.Equiv w₁ w₂) :
    GeneratedFrontierEquiv RI w₁ w₂ :=
  GeneratedFrontierEquiv.of_projectionFrontierEquiv h

/-- Campaign-2 projection theorem: trace/provenance compression preserves the
corrected-residue CanNF because the compression step leaves the underlying
residue frontier word unchanged. This is the first honest bridge from the
trace-layer `Compose` seam back to the corrected-residue normalizer. -/
theorem traceCompressionPreservesCorrectedResidueCanNF
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI))
    (t : TraceFrontierWord (concreteBoundaryMinimalSetup RI))
    (h : D.applies t) :
    correctedResidueCanNF RI (D.result t h).toFrontierWord
      = correctedResidueCanNF RI t.toFrontierWord := by
  simpa [correctedResidueCanNF] using
    congrArg (correctedResidueNormalize RI) (traceCompressionSound_fullConcrete D t h)

/-- Campaign-2 equivalence corollary: a trace-compression step stays inside the
same corrected-residue frontier-equivalence class. This is still narrower than
full `FrontierWord.Equiv`; it only records the residue-normalizer invariance
forced by projection preservation. -/
theorem traceCompressionPreservesCorrectedResidueFrontierEquiv
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI))
    (t : TraceFrontierWord (concreteBoundaryMinimalSetup RI))
    (h : D.applies t) :
    CorrectedResidueFrontierEquiv RI (D.result t h).toFrontierWord t.toFrontierWord := by
  exact (correctedResidueFrontierEquiv_iff_correctedResidueCanNF_eq RI
    (D.result t h).toFrontierWord t.toFrontierWord).2
      (traceCompressionPreservesCorrectedResidueCanNF RI D t h)

/-- One-step trace-compression relation induced by a concrete adjacent certified
step compression package. -/
def CorrectedResidueTraceCompressionStep
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI)) :
    TraceFrontierWord (concreteBoundaryMinimalSetup RI) →
      TraceFrontierWord (concreteBoundaryMinimalSetup RI) → Prop :=
  fun t₁ t₂ => ∃ h : D.applies t₁, D.result t₁ h = t₂

/-- Reflexive-transitive closure of the trace-compression step relation. -/
abbrev CorrectedResidueTraceCompressionMultiStep
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI)) :=
  Relation.ReflTransGen (CorrectedResidueTraceCompressionStep RI D)

/-- Trace-compression normal-form predicate for the corrected-residue trace
layer: no further adjacent certified-step compression applies. -/
def CorrectedResidueTraceCompressionIsNormal
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI))
    (t : TraceFrontierWord (concreteBoundaryMinimalSetup RI)) : Prop :=
  ¬ D.applies t

/-- Existence of an upstairs trace-compression normal form, obtained by
recursing on the concrete trace-compression measure. This stays entirely in the
trace/provenance layer while remembering the finite compression chain. -/
noncomputable def correctedResidueTraceCompressionNormalFormExists
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI))
    (t : TraceFrontierWord (concreteBoundaryMinimalSetup RI)) :
    { t_nf : TraceFrontierWord (concreteBoundaryMinimalSetup RI) //
      CorrectedResidueTraceCompressionMultiStep RI D t t_nf ∧
        CorrectedResidueTraceCompressionIsNormal RI D t_nf } := by
  by_cases h : D.applies t
  · let rest := correctedResidueTraceCompressionNormalFormExists RI D (D.result t h)
    refine ⟨rest.1, ?_⟩
    exact ⟨Relation.ReflTransGen.trans
      (Relation.ReflTransGen.single ⟨h, rfl⟩)
      rest.2.1, rest.2.2⟩
  · exact ⟨t, ⟨Relation.ReflTransGen.refl, h⟩⟩
termination_by D.traceMeasure t
decreasing_by
  exact D.trace_measure_decreases t h

/-- Chosen upstairs trace-compression normal form. -/
noncomputable def correctedResidueTraceCompressionNormalForm
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI))
    (t : TraceFrontierWord (concreteBoundaryMinimalSetup RI)) :
    TraceFrontierWord (concreteBoundaryMinimalSetup RI) :=
  (correctedResidueTraceCompressionNormalFormExists RI D t).1

/-- The chosen upstairs normal form is reached by a finite trace-compression
chain from the input trace state. -/
theorem correctedResidueTraceCompressionNormalForm_reaches
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI))
    (t : TraceFrontierWord (concreteBoundaryMinimalSetup RI)) :
    CorrectedResidueTraceCompressionMultiStep RI D t
      (correctedResidueTraceCompressionNormalForm RI D t) :=
  (correctedResidueTraceCompressionNormalFormExists RI D t).2.1

/-- The chosen upstairs normal form admits no further trace-compression step. -/
theorem correctedResidueTraceCompressionNormalForm_isNormal
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI))
    (t : TraceFrontierWord (concreteBoundaryMinimalSetup RI)) :
    CorrectedResidueTraceCompressionIsNormal RI D
      (correctedResidueTraceCompressionNormalForm RI D t) :=
  (correctedResidueTraceCompressionNormalFormExists RI D t).2.2

/-- Campaign-2 multistep closure: any finite trace-compression sequence
preserves the projected frontier word itself, hence cannot change any
residue-only canonicalization. -/
theorem traceCompressionMultiStepPreservesProjection
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI))
    {t₁ t₂ : TraceFrontierWord (concreteBoundaryMinimalSetup RI)}
    (hSteps : CorrectedResidueTraceCompressionMultiStep RI D t₁ t₂) :
    t₁.toFrontierWord = t₂.toFrontierWord := by
  induction hSteps with
  | refl =>
      rfl
  | tail hSteps hStep ih =>
      rcases hStep with ⟨h, rfl⟩
      exact Eq.trans ih (traceCompressionSound_fullConcrete D _ h).symm

/-- Campaign-2 multistep closure: any finite trace-compression sequence
preserves the corrected-residue CanNF of the projected frontier word. -/
theorem traceCompressionMultiStepPreservesCorrectedResidueCanNF
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI))
    {t₁ t₂ : TraceFrontierWord (concreteBoundaryMinimalSetup RI)}
    (hSteps : CorrectedResidueTraceCompressionMultiStep RI D t₁ t₂) :
    correctedResidueCanNF RI t₁.toFrontierWord
      = correctedResidueCanNF RI t₂.toFrontierWord := by
  simpa [correctedResidueCanNF] using
    congrArg (correctedResidueNormalize RI)
      (traceCompressionMultiStepPreservesProjection RI D hSteps)

/-- Multistep trace-compression corollary: compression closure stays inside a
single corrected-residue frontier-equivalence class. -/
theorem traceCompressionMultiStepPreservesCorrectedResidueFrontierEquiv
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI))
    {t₁ t₂ : TraceFrontierWord (concreteBoundaryMinimalSetup RI)}
    (hSteps : CorrectedResidueTraceCompressionMultiStep RI D t₁ t₂) :
    CorrectedResidueFrontierEquiv RI t₁.toFrontierWord t₂.toFrontierWord := by
  exact (correctedResidueFrontierEquiv_iff_correctedResidueCanNF_eq RI
    t₁.toFrontierWord t₂.toFrontierWord).2
      (traceCompressionMultiStepPreservesCorrectedResidueCanNF RI D hSteps)

/-- The chosen upstairs trace-compression normal form has exactly the same
frontier projection as the input trace state. -/
theorem correctedResidueTraceCompressionNormalForm_preservesProjection
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI))
    (t : TraceFrontierWord (concreteBoundaryMinimalSetup RI)) :
    (correctedResidueTraceCompressionNormalForm RI D t).toFrontierWord =
      t.toFrontierWord := by
  symm
  exact traceCompressionMultiStepPreservesProjection RI D
    (correctedResidueTraceCompressionNormalForm_reaches RI D t)

/-- Upstairs trace-compression normalization preserves the downstairs
corrected-residue CanNF. -/
theorem correctedResidueTraceCompressionNormalForm_preservesCorrectedResidueCanNF
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI))
    (t : TraceFrontierWord (concreteBoundaryMinimalSetup RI)) :
    correctedResidueCanNF RI
        (correctedResidueTraceCompressionNormalForm RI D t).toFrontierWord
      = correctedResidueCanNF RI t.toFrontierWord := by
  simpa [correctedResidueCanNF] using
    congrArg (correctedResidueNormalize RI)
      (correctedResidueTraceCompressionNormalForm_preservesProjection RI D t)

/-- Upstairs trace-compression normalization stays in the same narrow
corrected-residue frontier-equivalence class as the input projection. -/
theorem correctedResidueTraceCompressionNormalForm_preservesCorrectedResidueFrontierEquiv
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI))
    (t : TraceFrontierWord (concreteBoundaryMinimalSetup RI)) :
    CorrectedResidueFrontierEquiv RI
      (correctedResidueTraceCompressionNormalForm RI D t).toFrontierWord
      t.toFrontierWord := by
  exact (correctedResidueFrontierEquiv_iff_correctedResidueCanNF_eq RI
    (correctedResidueTraceCompressionNormalForm RI D t).toFrontierWord
    t.toFrontierWord).2
      (correctedResidueTraceCompressionNormalForm_preservesCorrectedResidueCanNF RI D t)

/-- Campaign-3 generation surface on full trace states: the smallest explicit
candidate equality relation generated by the three move families currently on
the table.

No separate, broader equality relation on `TraceFrontierWord` is currently
defined downstream in Layer B. Accordingly, this inductive relation is the
current full generated trace/frontier equality candidate on the full trace
carrier.

This is intentionally a generated relation, not yet identified with full trace
equality or with `FrontierWord.Equiv`. It records exactly the currently closed
ingredients: corrected-residue equality on projections, trace-compression
steps upstairs, and projection-level structural/admin equivalence. -/
inductive GeneratedTraceFrontierEquiv
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI)) :
    TraceFrontierWord (concreteBoundaryMinimalSetup RI) →
      TraceFrontierWord (concreteBoundaryMinimalSetup RI) → Prop where
  | of_correctedResidueFrontierEquiv
      {t₁ t₂ : TraceFrontierWord (concreteBoundaryMinimalSetup RI)} :
      CorrectedResidueFrontierEquiv RI t₁.toFrontierWord t₂.toFrontierWord →
        GeneratedTraceFrontierEquiv RI D t₁ t₂
  | of_traceCompressionStep
      {t₁ t₂ : TraceFrontierWord (concreteBoundaryMinimalSetup RI)} :
      CorrectedResidueTraceCompressionStep RI D t₁ t₂ →
        GeneratedTraceFrontierEquiv RI D t₁ t₂
  | of_projectionFrontierEquiv
      {t₁ t₂ : TraceFrontierWord (concreteBoundaryMinimalSetup RI)} :
      FrontierWord.Equiv t₁.toFrontierWord t₂.toFrontierWord →
        GeneratedTraceFrontierEquiv RI D t₁ t₂
  | refl (t : TraceFrontierWord (concreteBoundaryMinimalSetup RI)) :
      GeneratedTraceFrontierEquiv RI D t t
  | symm {t₁ t₂ : TraceFrontierWord (concreteBoundaryMinimalSetup RI)} :
      GeneratedTraceFrontierEquiv RI D t₁ t₂ →
        GeneratedTraceFrontierEquiv RI D t₂ t₁
  | trans {t₁ t₂ t₃ : TraceFrontierWord (concreteBoundaryMinimalSetup RI)} :
      GeneratedTraceFrontierEquiv RI D t₁ t₂ →
      GeneratedTraceFrontierEquiv RI D t₂ t₃ →
        GeneratedTraceFrontierEquiv RI D t₁ t₃

/-- Injection of the closed Campaign-1 narrow frontier equality into the new
generated full-state relation. -/
theorem generatedTraceFrontierEquiv_of_correctedResidueFrontierEquiv
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI))
    {t₁ t₂ : TraceFrontierWord (concreteBoundaryMinimalSetup RI)}
    (h : CorrectedResidueFrontierEquiv RI t₁.toFrontierWord t₂.toFrontierWord) :
    GeneratedTraceFrontierEquiv RI D t₁ t₂ :=
  .of_correctedResidueFrontierEquiv h

/-- Injection of one-step trace compression into the new generated full-state
relation. -/
theorem generatedTraceFrontierEquiv_of_traceCompressionStep
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI))
    {t₁ t₂ : TraceFrontierWord (concreteBoundaryMinimalSetup RI)}
    (h : CorrectedResidueTraceCompressionStep RI D t₁ t₂) :
    GeneratedTraceFrontierEquiv RI D t₁ t₂ :=
  .of_traceCompressionStep h

/-- Injection of projection-level structural/admin equivalence into the new
generated full-state relation. -/
theorem generatedTraceFrontierEquiv_of_projectionFrontierEquiv
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI))
    {t₁ t₂ : TraceFrontierWord (concreteBoundaryMinimalSetup RI)}
    (h : FrontierWord.Equiv t₁.toFrontierWord t₂.toFrontierWord) :
    GeneratedTraceFrontierEquiv RI D t₁ t₂ :=
  .of_projectionFrontierEquiv h

/-- Finite trace-compression chains generate the new full-state equality
candidate relation. -/
theorem generatedTraceFrontierEquiv_of_traceCompressionMultiStep
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI))
    {t₁ t₂ : TraceFrontierWord (concreteBoundaryMinimalSetup RI)}
    (hSteps : CorrectedResidueTraceCompressionMultiStep RI D t₁ t₂) :
    GeneratedTraceFrontierEquiv RI D t₁ t₂ := by
  induction hSteps with
  | refl =>
      exact GeneratedTraceFrontierEquiv.refl _
  | tail hSteps hStep ih =>
      exact GeneratedTraceFrontierEquiv.trans ih
        (GeneratedTraceFrontierEquiv.of_traceCompressionStep hStep)

/-- The chosen upstairs trace-compression normal form is related to the input by
the generated full-state equality candidate relation. -/
theorem generatedTraceFrontierEquiv_normalForm
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI))
    (t : TraceFrontierWord (concreteBoundaryMinimalSetup RI)) :
    GeneratedTraceFrontierEquiv RI D t
      (correctedResidueTraceCompressionNormalForm RI D t) :=
  generatedTraceFrontierEquiv_of_traceCompressionMultiStep RI D
    (correctedResidueTraceCompressionNormalForm_reaches RI D t)

/-- Projection of the trace-level generated equality candidate to the honest
stronger frontier-word relation. Trace-compression contributes only reflexivity
downstairs because it preserves projection literally. -/
theorem generatedTraceFrontierEquiv_projects_to_generatedFrontierEquiv
  (RI : Type u) [DecidableEq RI] [LinearOrder RI]
  (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI))
  {t₁ t₂ : TraceFrontierWord (concreteBoundaryMinimalSetup RI)}
  (h : GeneratedTraceFrontierEquiv RI D t₁ t₂) :
  GeneratedFrontierEquiv RI t₁.toFrontierWord t₂.toFrontierWord := by
  induction h with
  | of_correctedResidueFrontierEquiv hEq =>
    exact GeneratedFrontierEquiv.of_correctedResidueFrontierEquiv hEq
  | of_traceCompressionStep hStep =>
    rcases hStep with ⟨hApply, rfl⟩
    exact (traceCompressionSound_fullConcrete D _ hApply) ▸
    GeneratedFrontierEquiv.refl _
  | of_projectionFrontierEquiv hProj =>
    exact GeneratedFrontierEquiv.of_projectionFrontierEquiv hProj
  | refl _ =>
    exact GeneratedFrontierEquiv.refl _
  | symm _ ih =>
    exact GeneratedFrontierEquiv.symm ih
  | trans _ _ ih12 ih23 =>
    exact GeneratedFrontierEquiv.trans ih12 ih23

/-- Any proof in the stronger frontier-word relation lifts back to the current
generated trace/frontier equality candidate on any chosen trace representatives. -/
theorem generatedTraceFrontierEquiv_of_generatedFrontierEquiv
  (RI : Type u) [DecidableEq RI] [LinearOrder RI]
  (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI))
  {t₁ t₂ : TraceFrontierWord (concreteBoundaryMinimalSetup RI)}
  (h : GeneratedFrontierEquiv RI t₁.toFrontierWord t₂.toFrontierWord) :
  GeneratedTraceFrontierEquiv RI D t₁ t₂ := by
  exact generatedTraceFrontierEquiv_of_correctedResidueFrontierEquiv RI D
    ((correctedResidueFrontierEquiv_iff_correctedResidueCanNF_eq RI _ _).2
      (generatedFrontierEquiv_preservesCorrectedResidueCanNF RI h))

/-- The current generated trace/frontier equality candidate is exactly the lift
of the stronger frontier-word relation along `toFrontierWord`. -/
theorem generatedTraceFrontierEquiv_iff_generatedFrontierEquiv
  (RI : Type u) [DecidableEq RI] [LinearOrder RI]
  (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI))
  {t₁ t₂ : TraceFrontierWord (concreteBoundaryMinimalSetup RI)} :
  GeneratedTraceFrontierEquiv RI D t₁ t₂ ↔
    GeneratedFrontierEquiv RI t₁.toFrontierWord t₂.toFrontierWord :=
  ⟨generatedTraceFrontierEquiv_projects_to_generatedFrontierEquiv RI D,
  generatedTraceFrontierEquiv_of_generatedFrontierEquiv RI D⟩

/-- Explicit soundness-side bridge obligation for the projection-level
`FrontierWord.Equiv` constructor appearing in `GeneratedTraceFrontierEquiv`.

This isolates the current Campaign-3 gap: the broader projection equivalence is
allowed as a generator, but its preservation of the corrected-residue CanNF is
not yet derivable from the current closed residue and trace-compression layers. -/
structure GeneratedTraceFrontierEquivProjectionSoundness
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI)) : Prop where
  projection_frontier_equiv_preserves_correctedResidueCanNF :
    ∀ {t₁ t₂ : TraceFrontierWord (concreteBoundaryMinimalSetup RI)},
      FrontierWord.Equiv t₁.toFrontierWord t₂.toFrontierWord →
        correctedResidueCanNF RI t₁.toFrontierWord =
          correctedResidueCanNF RI t₂.toFrontierWord

/-- In the concrete closed setup, projection-level `FrontierWord.Equiv` already
preserves the corrected-residue CanNF: the boundary canonicalizer collapses
`BoundaryAdminEquiv` to equality, the external-output canonicalizer sorts up to
permutation, and the remaining canonicalizers are rigid or unique. -/
theorem frontierWordEquiv_preservesCorrectedResidueCanNF
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    {t₁ t₂ : TraceFrontierWord (concreteBoundaryMinimalSetup RI)}
    (h : FrontierWord.Equiv t₁.toFrontierWord t₂.toFrontierWord) :
    correctedResidueCanNF RI t₁.toFrontierWord =
      correctedResidueCanNF RI t₂.toFrontierWord := by
  exact correctedResidueNormalize_eq_of_canonical_eq RI
    (frontierWordEquiv_preserves_correctedResidueCanonicalFrontierWord RI h)

/-- Sound normalizer packaging for the concrete corrected-residue CanNF.

This is the honest Campaign-4 entry point into downstream reconstruction and
holography consumers: the corrected-residue normalizer is already sound for the
consumer-facing `FrontierWord.Equiv`. Completeness for plain
`FrontierWord.Equiv` is not merely unproved here: administrative-identity
contraction lowers packet count, so the exact complete relation for this
normalizer is the stronger `GeneratedFrontierEquiv` established below. -/
noncomputable def correctedResidueFrontierWordSoundNormalizer
    (RI : Type u) [DecidableEq RI] [LinearOrder RI] :
    FrontierWordSoundNormalizer (concreteBoundaryMinimalSetup RI) where
  NF := FrontierWord (concreteBoundaryMinimalSetup RI)
  normalize := correctedResidueCanNF RI
  sound := by
    intro w₁ w₂ hEquiv
    exact correctedResidueNormalize_eq_of_canonical_eq RI
      (frontierWordEquiv_preserves_correctedResidueCanonicalFrontierWord RI hEquiv)

/-- Campaign-4 sound holography adapter: any holographic reconstruction datum on
the concrete setup can now be consumed by the corrected-residue CanNF in the
sound direction. -/
theorem correctedResidueHolographicCanNF_sound_on_records
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (D : HolographicReconstructionData (concreteBoundaryMinimalSetup RI))
    {R₁ R₂ : CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI)}
    (h : RecordStructEquiv (@BoundaryAdminEquiv (concreteBoundaryMinimalSetup RI)) R₁ R₂) :
    correctedResidueCanNF RI (D.toFrontierWord R₁) =
      correctedResidueCanNF RI (D.toFrontierWord R₂) :=
  holographic_cannf_sound_on_records D
    (correctedResidueFrontierWordSoundNormalizer RI) h

/-- Campaign-6 trace/frontier lift over a completed-record frontier assignment.
This keeps the trace-level witness explicit while requiring that its frontier
projection agrees with the chosen reconstruction map. -/
structure CompletedRecordTraceFrontierLift
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (frontierWord :
      CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI) →
        FrontierWord (concreteBoundaryMinimalSetup RI)) where
  toTraceFrontierWord :
    CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI) →
      TraceFrontierWord (concreteBoundaryMinimalSetup RI)
  projects_frontierWord :
    ∀ R,
      (toTraceFrontierWord R).toFrontierWord = frontierWord R

/-- Concrete trace/frontier state over `concreteBoundaryMinimalSetup RI` for a
frontier word whose source and target boundaries are both zero. This is the
largest honest concrete slice of `TraceFrontierWord` available on the minimal
setup, because `State = PUnit` and `boundaryOf = fun _ => 0`. -/
def traceFrontierWord_of_zeroBoundaryFrontierWord
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (w : FrontierWord (concreteBoundaryMinimalSetup RI))
    (hX : w.residue.X = (0 : Multiset (ConcreteBoundaryAtom RI)))
    (hY : w.residue.Y = (0 : Multiset (ConcreteBoundaryAtom RI))) :
    TraceFrontierWord (concreteBoundaryMinimalSetup RI) where
  sourceState := PUnit.unit
  targetState := PUnit.unit
  word := w
  source_boundary := hX.symm
  target_boundary := hY.symm
  trace := idCertifiedTrace (setup := concreteBoundaryMinimalSetup RI) PUnit.unit

@[simp] theorem traceFrontierWord_of_zeroBoundaryFrontierWord_toFrontierWord
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (w : FrontierWord (concreteBoundaryMinimalSetup RI))
    (hX : w.residue.X = (0 : Multiset (ConcreteBoundaryAtom RI)))
    (hY : w.residue.Y = (0 : Multiset (ConcreteBoundaryAtom RI))) :
    (traceFrontierWord_of_zeroBoundaryFrontierWord RI w hX hY).toFrontierWord = w := by
  simp [traceFrontierWord_of_zeroBoundaryFrontierWord, TraceFrontierWord.toFrontierWord]

/-- Honest concrete trace/frontier lift on the minimal setup: it exists exactly
when the reconstructed frontier words land in the zero-boundary slice. -/
def completedRecordTraceFrontierLift_of_zeroBoundaries
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (frontierWord :
      CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI) →
        FrontierWord (concreteBoundaryMinimalSetup RI))
    (hSourceZero : ∀ R,
      (frontierWord R).residue.X = (0 : Multiset (ConcreteBoundaryAtom RI)))
    (hTargetZero : ∀ R,
      (frontierWord R).residue.Y = (0 : Multiset (ConcreteBoundaryAtom RI))) :
    CompletedRecordTraceFrontierLift RI frontierWord where
  toTraceFrontierWord := fun R =>
    traceFrontierWord_of_zeroBoundaryFrontierWord RI (frontierWord R)
      (hSourceZero R) (hTargetZero R)
  projects_frontierWord := by
    intro R
    simpa [traceFrontierWord_of_zeroBoundaryFrontierWord, TraceFrontierWord.toFrontierWord]

/-- On the concrete minimal setup, `FrontierWord.Equiv` between reconstructed
frontier words already feeds the generated trace/frontier equality layer once
those words lie in the zero-boundary slice. -/
theorem frontierEquiv_implies_generatedTraceFrontierEquiv_of_zeroBoundaries
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI))
    (frontierWord :
      CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI) →
        FrontierWord (concreteBoundaryMinimalSetup RI))
    (hSourceZero : ∀ R,
      (frontierWord R).residue.X = (0 : Multiset (ConcreteBoundaryAtom RI)))
    (hTargetZero : ∀ R,
      (frontierWord R).residue.Y = (0 : Multiset (ConcreteBoundaryAtom RI)))
    {R₁ R₂ : CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI)}
    (hFrontier : FrontierWord.Equiv (frontierWord R₁) (frontierWord R₂)) :
    GeneratedTraceFrontierEquiv RI D
      ((completedRecordTraceFrontierLift_of_zeroBoundaries RI frontierWord
          hSourceZero hTargetZero).toTraceFrontierWord R₁)
      ((completedRecordTraceFrontierLift_of_zeroBoundaries RI frontierWord
          hSourceZero hTargetZero).toTraceFrontierWord R₂) := by
  apply generatedTraceFrontierEquiv_of_projectionFrontierEquiv
  simpa [completedRecordTraceFrontierLift_of_zeroBoundaries,
    traceFrontierWord_of_zeroBoundaryFrontierWord, TraceFrontierWord.toFrontierWord] using hFrontier

/-- Concrete Campaign-6 bridge on the minimal setup: visible/completed-boundary
equality implies generated trace/frontier equality, provided the reconstructed
frontier words lie in the zero-boundary slice where `TraceFrontierWord` exists
honestly. -/
theorem holographicReconstruction_generatedTraceFrontierEquiv_of_zeroBoundaries
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI))
    {β : Sort _}
    (Drec : HolographicReconstructionData (concreteBoundaryMinimalSetup RI))
    (visibleBoundary :
      CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI) → β)
    (hVisibleToFrontier :
      ∀ {R₁ R₂ : CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI)},
        visibleBoundary R₁ = visibleBoundary R₂ →
          FrontierWord.Equiv (Drec.toFrontierWord R₁) (Drec.toFrontierWord R₂))
    (hSourceZero : ∀ R,
      (Drec.toFrontierWord R).residue.X = (0 : Multiset (ConcreteBoundaryAtom RI)))
    (hTargetZero : ∀ R,
      (Drec.toFrontierWord R).residue.Y = (0 : Multiset (ConcreteBoundaryAtom RI)))
    {R₁ R₂ : CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI)}
    (hVisible : visibleBoundary R₁ = visibleBoundary R₂) :
    GeneratedTraceFrontierEquiv RI D
      ((completedRecordTraceFrontierLift_of_zeroBoundaries RI Drec.toFrontierWord
          hSourceZero hTargetZero).toTraceFrontierWord R₁)
      ((completedRecordTraceFrontierLift_of_zeroBoundaries RI Drec.toFrontierWord
          hSourceZero hTargetZero).toTraceFrontierWord R₂) :=
  frontierEquiv_implies_generatedTraceFrontierEquiv_of_zeroBoundaries
    RI D Drec.toFrontierWord hSourceZero hTargetZero (hVisibleToFrontier hVisible)

/-- Campaign-6 sound bridge: any visible/completed boundary equality theorem
that already yields `FrontierWord.Equiv` can be fed directly into the current
generated trace/frontier equality layer, provided we choose a trace/frontier
lift whose projection is the reconstructed frontier word. -/
theorem visibleBoundary_eq_implies_generatedTraceFrontierEquiv
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI))
    {β : Sort _}
    (visibleBoundary :
      CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI) → β)
    (frontierWord :
      CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI) →
        FrontierWord (concreteBoundaryMinimalSetup RI))
    (hFrontier :
      ∀ {R₁ R₂ : CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI)},
        visibleBoundary R₁ = visibleBoundary R₂ →
          FrontierWord.Equiv (frontierWord R₁) (frontierWord R₂))
    (lift : CompletedRecordTraceFrontierLift RI frontierWord)
    {R₁ R₂ : CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI)}
    (hVisible : visibleBoundary R₁ = visibleBoundary R₂) :
    GeneratedTraceFrontierEquiv RI D
      (lift.toTraceFrontierWord R₁)
      (lift.toTraceFrontierWord R₂) := by
  apply generatedTraceFrontierEquiv_of_projectionFrontierEquiv
  simpa [lift.projects_frontierWord R₁, lift.projects_frontierWord R₂] using
    hFrontier hVisible

/-- Campaign-6 holographic bridge specialized to the current reconstruction
datum: once visible/completed boundary equality implies frontier equivalence for
`Drec.toFrontierWord`, the generated trace/frontier equality layer can consume
any projection-compatible trace lift. -/
theorem holographicReconstruction_generatedTraceFrontierEquiv
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI))
    {β : Sort _}
    (Drec : HolographicReconstructionData (concreteBoundaryMinimalSetup RI))
    (visibleBoundary :
      CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI) → β)
    (hVisibleToFrontier :
      ∀ {R₁ R₂ : CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI)},
        visibleBoundary R₁ = visibleBoundary R₂ →
          FrontierWord.Equiv (Drec.toFrontierWord R₁) (Drec.toFrontierWord R₂))
    (lift : CompletedRecordTraceFrontierLift RI Drec.toFrontierWord)
    {R₁ R₂ : CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI)}
    (hVisible : visibleBoundary R₁ = visibleBoundary R₂) :
    GeneratedTraceFrontierEquiv RI D
      (lift.toTraceFrontierWord R₁)
      (lift.toTraceFrontierWord R₂) :=
  visibleBoundary_eq_implies_generatedTraceFrontierEquiv
    RI D visibleBoundary Drec.toFrontierWord hVisibleToFrontier lift hVisible

/-- Canonical downstream bridge: visible/completed-boundary equality that
already yields `FrontierWord.Equiv` also yields the honest stronger
frontier-word relation directly, with no trace lift and no zero-boundary
specialization. -/
theorem visibleBoundary_eq_implies_generatedFrontierEquiv
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    {β : Sort _}
    (visibleBoundary :
      CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI) → β)
    (frontierWord :
      CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI) →
        FrontierWord (concreteBoundaryMinimalSetup RI))
    (hFrontier :
      ∀ {R₁ R₂ : CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI)},
        visibleBoundary R₁ = visibleBoundary R₂ →
          FrontierWord.Equiv (frontierWord R₁) (frontierWord R₂))
    {R₁ R₂ : CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI)}
    (hVisible : visibleBoundary R₁ = visibleBoundary R₂) :
    GeneratedFrontierEquiv RI (frontierWord R₁) (frontierWord R₂) :=
  generatedFrontierEquiv_of_frontierWordEquiv RI (hFrontier hVisible)

/-- Holographic specialization of
`visibleBoundary_eq_implies_generatedFrontierEquiv`. This is the honest
frontier-level relation produced by visible/completed-boundary equality. -/
theorem holographicReconstruction_generatedFrontierEquiv
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    {β : Sort _}
    (Drec : HolographicReconstructionData (concreteBoundaryMinimalSetup RI))
    (visibleBoundary :
      CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI) → β)
    (hVisibleToFrontier :
      ∀ {R₁ R₂ : CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI)},
        visibleBoundary R₁ = visibleBoundary R₂ →
          FrontierWord.Equiv (Drec.toFrontierWord R₁) (Drec.toFrontierWord R₂))
    {R₁ R₂ : CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI)}
    (hVisible : visibleBoundary R₁ = visibleBoundary R₂) :
    GeneratedFrontierEquiv RI (Drec.toFrontierWord R₁) (Drec.toFrontierWord R₂) :=
  visibleBoundary_eq_implies_generatedFrontierEquiv
    RI visibleBoundary Drec.toFrontierWord hVisibleToFrontier hVisible

/-- Campaign-4 sound reconstruction adapter: the existing canonical
reconstruction engine already produces the honest stronger frontier-word
relation on canonical frontier observations under contextual admin
equivalence. -/
theorem correctedResidueEngineGeneratedFrontierEquiv_under_admin_equiv
  (RI : Type u) [DecidableEq RI] [LinearOrder RI]
  (eng : CanonicalReconstructionEngine (concreteBoundaryMinimalSetup RI))
  {R : CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI)}
  {d : Nat}
  {c₁ c₂ : PeelChain R}
  (h : ContextualAdminEquiv d c₁ c₂) :
  GeneratedFrontierEquiv RI
    (canonicalFrontierWord (FrontierObservation.ofChain c₁ d))
    (canonicalFrontierWord (FrontierObservation.ofChain c₂ d)) :=
  generatedFrontierEquiv_of_frontierWordEquiv RI (eng.canonical_word_admin_stable h)

/-- Campaign-4 CanNF corollary: the existing canonical reconstruction engine
can already use the corrected-residue CanNF on canonical frontier observations,
now routed through the honest stronger frontier-word relation rather than a
sound-normalizer contract. -/
theorem correctedResidueEngineCanNF_sound_under_admin_equiv
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (eng : CanonicalReconstructionEngine (concreteBoundaryMinimalSetup RI))
    {R : CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI)}
    {d : Nat}
    {c₁ c₂ : PeelChain R}
    (h : ContextualAdminEquiv d c₁ c₂) :
    correctedResidueCanNF RI
        (canonicalFrontierWord
          (FrontierObservation.ofChain c₁ d)) =
      correctedResidueCanNF RI
        (canonicalFrontierWord
          (FrontierObservation.ofChain c₂ d)) :=
  generatedFrontierEquiv_preservesCorrectedResidueCanNF RI
    (correctedResidueEngineGeneratedFrontierEquiv_under_admin_equiv RI eng h)

/-- Campaign-4 precise relation corollary: the existing canonical
reconstruction engine already preserves the corrected-residue frontier
equivalence class on canonical frontier observations under contextual admin
equivalence. -/
theorem correctedResidueEngineFrontierEquiv_under_admin_equiv
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (eng : CanonicalReconstructionEngine (concreteBoundaryMinimalSetup RI))
    {R : CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI)}
    {d : Nat}
    {c₁ c₂ : PeelChain R}
    (h : ContextualAdminEquiv d c₁ c₂) :
    CorrectedResidueFrontierEquiv RI
        (canonicalFrontierWord
          (FrontierObservation.ofChain c₁ d))
        (canonicalFrontierWord
          (FrontierObservation.ofChain c₂ d)) :=
  CanonicalReconstructionEngine.canonical_word_relative_cannf_eq_under_admin_equiv
    eng (correctedResidueFrontierWordRelativeNormalizer RI)
    (frontierWordEquiv_preservesCorrectedResidueFrontierEquiv RI) h

/-- Closed Campaign-3 projection soundness witness for the concrete generated
relation: the projection constructor is sound without any extra hypothesis. -/
def generatedTraceFrontierEquivProjectionSoundness_closed
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI)) :
    GeneratedTraceFrontierEquivProjectionSoundness RI D where
  projection_frontier_equiv_preserves_correctedResidueCanNF :=
    frontierWordEquiv_preservesCorrectedResidueCanNF RI

/-- Campaign-3 soundness theorem: every currently generated full-state equality
preserves the downstream corrected-residue CanNF invariant.

The only non-closed generator is the projection-level `FrontierWord.Equiv`
constructor, so this theorem is parameterized by the explicit bridge obligation
`GeneratedTraceFrontierEquivProjectionSoundness`. No completeness claim is made. -/
theorem generatedTraceFrontierEquiv_preservesCorrectedResidueCanNF
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI))
    (Hproj : GeneratedTraceFrontierEquivProjectionSoundness RI D)
    {t₁ t₂ : TraceFrontierWord (concreteBoundaryMinimalSetup RI)}
    (h : GeneratedTraceFrontierEquiv RI D t₁ t₂) :
    correctedResidueCanNF RI t₁.toFrontierWord =
      correctedResidueCanNF RI t₂.toFrontierWord := by
  induction h with
  | @of_correctedResidueFrontierEquiv t₁ t₂ hEq =>
      exact (correctedResidueFrontierEquiv_iff_correctedResidueCanNF_eq RI
        t₁.toFrontierWord t₂.toFrontierWord).1 hEq
  | @of_traceCompressionStep t₁ t₂ hStep =>
      rcases hStep with ⟨hApply, rfl⟩
      exact (traceCompressionPreservesCorrectedResidueCanNF RI D t₁ hApply).symm
  | of_projectionFrontierEquiv hProj =>
      exact Hproj.projection_frontier_equiv_preserves_correctedResidueCanNF hProj
  | refl _ =>
      rfl
  | symm h ih =>
      exact ih.symm
  | trans h12 h23 ih12 ih23 =>
      exact Eq.trans ih12 ih23

/-- Narrow Campaign-3 corollary: under the same explicit projection-soundness
obligation, the generated full-state equality also preserves the corrected
residue frontier-equivalence class. -/
theorem generatedTraceFrontierEquiv_preservesCorrectedResidueFrontierEquiv
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI))
    (Hproj : GeneratedTraceFrontierEquivProjectionSoundness RI D)
    {t₁ t₂ : TraceFrontierWord (concreteBoundaryMinimalSetup RI)}
    (h : GeneratedTraceFrontierEquiv RI D t₁ t₂) :
    CorrectedResidueFrontierEquiv RI t₁.toFrontierWord t₂.toFrontierWord := by
  exact (correctedResidueFrontierEquiv_iff_correctedResidueCanNF_eq RI
    t₁.toFrontierWord t₂.toFrontierWord).2
      (generatedTraceFrontierEquiv_preservesCorrectedResidueCanNF RI D Hproj h)

/-- Concrete closed-form Campaign-3 soundness theorem: every generated full-state
equality preserves the downstream corrected-residue CanNF invariant, with the
projection constructor discharged internally. -/
theorem generatedTraceFrontierEquiv_preservesCorrectedResidueCanNF_closed
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI))
    {t₁ t₂ : TraceFrontierWord (concreteBoundaryMinimalSetup RI)}
    (h : GeneratedTraceFrontierEquiv RI D t₁ t₂) :
    correctedResidueCanNF RI t₁.toFrontierWord =
      correctedResidueCanNF RI t₂.toFrontierWord :=
  generatedTraceFrontierEquiv_preservesCorrectedResidueCanNF RI D
    (generatedTraceFrontierEquivProjectionSoundness_closed RI D) h

/-- Concrete closed-form Campaign-3 corollary: the generated full-state equality
stays inside the corrected-residue frontier-equivalence class. -/
theorem generatedTraceFrontierEquiv_preservesCorrectedResidueFrontierEquiv_closed
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI))
    {t₁ t₂ : TraceFrontierWord (concreteBoundaryMinimalSetup RI)}
    (h : GeneratedTraceFrontierEquiv RI D t₁ t₂) :
    CorrectedResidueFrontierEquiv RI t₁.toFrontierWord t₂.toFrontierWord :=
  generatedTraceFrontierEquiv_preservesCorrectedResidueFrontierEquiv RI D
    (generatedTraceFrontierEquivProjectionSoundness_closed RI D) h

/-- Honest Campaign-3 packaging theorem on the trace carrier.

At trace level, `GeneratedTraceFrontierEquiv` is now identified with the lift
of the frontier relation `GeneratedFrontierEquiv` along `toFrontierWord`, so
this theorem is the trace-facing form of the exact corrected-residue CanNF
invariance theorem. -/
theorem fullTraceFrontierEquiv_preservesCorrectedResidueCanNF
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI))
    {t₁ t₂ : TraceFrontierWord (concreteBoundaryMinimalSetup RI)}
    (h : GeneratedTraceFrontierEquiv RI D t₁ t₂) :
    correctedResidueCanNF RI t₁.toFrontierWord =
      correctedResidueCanNF RI t₂.toFrontierWord :=
  generatedTraceFrontierEquiv_preservesCorrectedResidueCanNF_closed RI D h

/-- Reverse Campaign-3 packaging theorem: equality of corrected-residue CanNF
outputs already generates the current full trace/frontier equality candidate,
because corrected-residue frontier equivalence is a generator of
`GeneratedTraceFrontierEquiv`. -/
theorem generatedTraceFrontierEquiv_of_correctedResidueCanNF_eq
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI))
    {t₁ t₂ : TraceFrontierWord (concreteBoundaryMinimalSetup RI)}
    (h : correctedResidueCanNF RI t₁.toFrontierWord =
      correctedResidueCanNF RI t₂.toFrontierWord) :
    GeneratedTraceFrontierEquiv RI D t₁ t₂ :=
  generatedTraceFrontierEquiv_of_correctedResidueFrontierEquiv RI D
    ((correctedResidueFrontierEquiv_iff_correctedResidueCanNF_eq RI
      t₁.toFrontierWord t₂.toFrontierWord).2 h)

/-- Honest Campaign-3 completeness theorem for the current full generated
trace/frontier equality candidate: it is exactly detected by equality of
corrected-residue CanNF outputs. -/
theorem fullTraceFrontierEquiv_iff_correctedResidueCanNF_eq
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI))
    {t₁ t₂ : TraceFrontierWord (concreteBoundaryMinimalSetup RI)} :
    GeneratedTraceFrontierEquiv RI D t₁ t₂ ↔
      correctedResidueCanNF RI t₁.toFrontierWord =
        correctedResidueCanNF RI t₂.toFrontierWord :=
  ⟨fullTraceFrontierEquiv_preservesCorrectedResidueCanNF RI D,
    generatedTraceFrontierEquiv_of_correctedResidueCanNF_eq RI D⟩

/-- Concrete Campaign-6 soundness corollary on the minimal setup: the generated
trace/frontier equality produced from visible/completed-boundary equality stays
inside the corrected-residue CanNF class. No reverse completeness theorem is
used. -/
theorem holographicReconstruction_preservesCorrectedResidueCanNF
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    {β : Sort _}
    (Drec : HolographicReconstructionData (concreteBoundaryMinimalSetup RI))
    (visibleBoundary :
      CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI) → β)
    (hVisibleToFrontier :
      ∀ {R₁ R₂ : CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI)},
        visibleBoundary R₁ = visibleBoundary R₂ →
          FrontierWord.Equiv (Drec.toFrontierWord R₁) (Drec.toFrontierWord R₂))
    {R₁ R₂ : CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI)}
    (hVisible : visibleBoundary R₁ = visibleBoundary R₂) :
    correctedResidueCanNF RI (Drec.toFrontierWord R₁) =
      correctedResidueCanNF RI (Drec.toFrontierWord R₂) :=
  generatedFrontierEquiv_preservesCorrectedResidueCanNF RI
    (holographicReconstruction_generatedFrontierEquiv RI Drec visibleBoundary
      hVisibleToFrontier hVisible)

/-- Concrete Campaign-6 precise frontier-level corollary: visible/completed
boundary equality also preserves the corrected-residue frontier-equivalence
class itself, not only equality of the corrected-residue CanNF outputs. -/
theorem holographicReconstruction_preservesCorrectedResidueFrontierEquiv
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    {β : Sort _}
    (Drec : HolographicReconstructionData (concreteBoundaryMinimalSetup RI))
    (visibleBoundary :
      CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI) → β)
    (hVisibleToFrontier :
      ∀ {R₁ R₂ : CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI)},
        visibleBoundary R₁ = visibleBoundary R₂ →
          FrontierWord.Equiv (Drec.toFrontierWord R₁) (Drec.toFrontierWord R₂))
    {R₁ R₂ : CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI)}
    (hVisible : visibleBoundary R₁ = visibleBoundary R₂) :
    CorrectedResidueFrontierEquiv RI
      (Drec.toFrontierWord R₁) (Drec.toFrontierWord R₂) :=
  holographic_relative_cannf_eq_of_visible_boundary_eq
    Drec (correctedResidueFrontierWordRelativeNormalizer RI)
    visibleBoundary hVisibleToFrontier
    (frontierWordEquiv_preservesCorrectedResidueFrontierEquiv RI) hVisible

/-- Concrete Campaign-6 trace-level corollary on the minimal setup: when a
trace/frontier witness is needed, the older zero-boundary route still recovers
the same corrected-residue CanNF equality. The real frontier-level theorem is
`holographicReconstruction_preservesCorrectedResidueCanNF` above. -/
theorem holographicReconstruction_preservesCorrectedResidueCanNF_of_zeroBoundaries
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI))
    {β : Sort _}
    (Drec : HolographicReconstructionData (concreteBoundaryMinimalSetup RI))
    (visibleBoundary :
      CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI) → β)
    (hVisibleToFrontier :
      ∀ {R₁ R₂ : CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI)},
        visibleBoundary R₁ = visibleBoundary R₂ →
          FrontierWord.Equiv (Drec.toFrontierWord R₁) (Drec.toFrontierWord R₂))
    (hSourceZero : ∀ R,
      (Drec.toFrontierWord R).residue.X = (0 : Multiset (ConcreteBoundaryAtom RI)))
    (hTargetZero : ∀ R,
      (Drec.toFrontierWord R).residue.Y = (0 : Multiset (ConcreteBoundaryAtom RI)))
    {R₁ R₂ : CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI)}
    (hVisible : visibleBoundary R₁ = visibleBoundary R₂) :
    correctedResidueCanNF RI (Drec.toFrontierWord R₁) =
      correctedResidueCanNF RI (Drec.toFrontierWord R₂) :=
  holographicReconstruction_preservesCorrectedResidueCanNF
    RI Drec visibleBoundary hVisibleToFrontier hVisible

/-- Honest Campaign-3 packaging theorem: the current full generated
trace/frontier equality candidate factors through the precise corrected-residue
frontier equivalence used by the closed residue-side normal-form layer. -/
theorem fullTraceFrontierEquiv_preservesCorrectedResidueFrontierEquiv
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI))
    {t₁ t₂ : TraceFrontierWord (concreteBoundaryMinimalSetup RI)}
    (h : GeneratedTraceFrontierEquiv RI D t₁ t₂) :
    CorrectedResidueFrontierEquiv RI t₁.toFrontierWord t₂.toFrontierWord :=
  generatedTraceFrontierEquiv_preservesCorrectedResidueFrontierEquiv_closed RI D h

/-- Record-facing specialization of the corrected-residue frontier equality
theorem. -/
theorem correctedResidueNormalize_ofResidue_eq_iff
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (R₁ R₂ : CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI)) :
    correctedResidueNormalize RI (FrontierWord.ofResidue R₁)
        = correctedResidueNormalize RI (FrontierWord.ofResidue R₂) ↔
      CorrectedResidueFrontierEquiv RI (FrontierWord.ofResidue R₁) (FrontierWord.ofResidue R₂) := by
  simpa [correctedResidueRelativeCanNF] using
    correctedResidueRelativeCanNF_normalize_eq_iff RI R₁ R₂

/-- Record-facing corrected-residue soundness theorem obtained by instantiating
the abstract engine-package theorem in the canonical identity-holography case. -/
theorem correctedResidueRelativeCanNF_eq_of_record_equiv
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    {R₁ R₂ : CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI)}
    (h : RecordStructEquiv (@BoundaryAdminEquiv (concreteBoundaryMinimalSetup RI)) R₁ R₂) :
    (correctedResidueRelativeCanNF RI).normalize R₁ =
      (correctedResidueRelativeCanNF RI).normalize R₂ := by
  simpa using
    (CanonicalReconstructionEngine.identity_holography_relativeCanNF_eq_of_record_equiv
      (C := correctedResidueRelativeCanNF RI)
      (hAssign := correctedResidueRelativeCanNF_assignment_matches_identity_holography RI)
      (hRel_of_frontier_equiv := frontierWordEquiv_preservesCorrectedResidueFrontierEquiv RI)
      h)

/-- Identity-holography detection theorem for the corrected-residue package:
the current record-level corrected-residue normal-form values are equal if and
only if the corresponding identity-holography frontier words are related by
the corrected-residue frontier equivalence. -/
theorem correctedResidueRelativeCanNF_detects_identity_holography_equiv
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    (R₁ R₂ : CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI)) :
    (correctedResidueRelativeCanNF RI).normalize R₁ =
      (correctedResidueRelativeCanNF RI).normalize R₂ ↔
      CorrectedResidueFrontierEquiv RI
        (FrontierWord.ofResidue R₁) (FrontierWord.ofResidue R₂) := by
  simpa using
    (CanonicalReconstructionEngine.identity_holography_rel_iff_relativeCanNF_eq
      (C := correctedResidueRelativeCanNF RI)
      (hAssign := correctedResidueRelativeCanNF_assignment_matches_identity_holography RI)
      (R₁ := R₁) (R₂ := R₂))

/-- Visible-boundary corrected-residue soundness theorem obtained by
instantiating the abstract engine-package theorem in the canonical
identity-holography case. -/
theorem correctedResidueRelativeCanNF_eq_of_visible_boundary_eq
    (RI : Type u) [DecidableEq RI] [LinearOrder RI]
    {β : Sort _}
    (visibleBoundary :
      CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI) → β)
    (hFrontier_of_visible_eq :
      ∀ {R₁ R₂ : CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI)},
        visibleBoundary R₁ = visibleBoundary R₂ →
          FrontierWord.Equiv (FrontierWord.ofResidue R₁) (FrontierWord.ofResidue R₂))
    {R₁ R₂ : CompletedReconstructionRecord (concreteBoundaryMinimalSetup RI)}
    (hVisible : visibleBoundary R₁ = visibleBoundary R₂) :
    (correctedResidueRelativeCanNF RI).normalize R₁ =
      (correctedResidueRelativeCanNF RI).normalize R₂ := by
  simpa using
    (CanonicalReconstructionEngine.identity_holography_relativeCanNF_eq_of_visible_boundary_eq
      (C := correctedResidueRelativeCanNF RI)
      (hAssign := correctedResidueRelativeCanNF_assignment_matches_identity_holography RI)
      (visibleBoundary := visibleBoundary)
      (hFrontier_of_visible_eq := hFrontier_of_visible_eq)
      (hRel_of_frontier_equiv := frontierWordEquiv_preservesCorrectedResidueFrontierEquiv RI)
      hVisible)

end RewriteCalculusSetup
end RealObjects
end LayerB
end TraceCalc

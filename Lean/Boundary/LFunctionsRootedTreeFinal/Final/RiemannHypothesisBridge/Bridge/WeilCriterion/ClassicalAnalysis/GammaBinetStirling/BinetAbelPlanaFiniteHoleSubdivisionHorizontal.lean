import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaFiniteHoleSubdivisionCore

/-!
# Horizontal finite-hole subdivision

This file owns the horizontal endpoint chain, horizontal geometric membership,
and lower/upper horizontal side decompositions for the finite-hole subdivision.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped Topology Interval


/-- Endpoint chain for the finite Abel-Plana horizontal subdivision.

The adjacent intervals are, in order,
`[0, ρ]`, `[ρ, 1 - ρ]`, `[1 - ρ, 1 + ρ]`, ...,
`[N + ρ, N + 1 - ρ]`, `[N + 1 - ρ, N + 1]`. -/
noncomputable def Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint
    (N : ℕ)
    (ρ : ℝ)
    (i : ℕ) : ℝ :=
  if i = 0 then
    0
  else if i = 2 * N + 3 then
    ((N + 1 : ℕ) : ℝ)
  else
    let j : ℕ := i - 1
    if j % 2 = 0 then
      ((j / 2 : ℕ) : ℝ) + ρ
    else
      (((j + 1) / 2 : ℕ) : ℝ) - ρ

/-- Unfolding of the finite Abel-Plana horizontal subdivision endpoint chain. -/
theorem Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_unfold
    (N : ℕ)
    (ρ : ℝ)
    (i : ℕ) :
    Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i =
      if i = 0 then
        0
      else if i = 2 * N + 3 then
        ((N + 1 : ℕ) : ℝ)
      else
        let j : ℕ := i - 1
        if j % 2 = 0 then
          ((j / 2 : ℕ) : ℝ) + ρ
        else
          (((j + 1) / 2 : ℕ) : ℝ) - ρ := by
  rfl

/-- The finite Abel-Plana horizontal chain starts at the left endpoint. -/
theorem Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_start
    (N : ℕ)
    (ρ : ℝ) :
    Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ 0 = 0 := by
  rfl

/-- The finite Abel-Plana horizontal chain ends at the right endpoint. -/
theorem Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_end
    (N : ℕ)
    (ρ : ℝ) :
    Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (2 * N + 3) =
      ((N + 1 : ℕ) : ℝ) := by
  have hne : 2 * N + 3 ≠ 0 := by
    exact Nat.succ_ne_zero (2 * N + 2)
  exact
    Eq.trans
      (Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_unfold N ρ (2 * N + 3))
      (Eq.trans (if_neg hne) (if_pos rfl))

/-- Odd subdivision nodes are exactly the left endpoints of the safe vertical
strips. -/
theorem Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_safe_left
    (N k : ℕ)
    (ρ : ℝ)
    (hk : k ≤ N) :
    Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (2 * k + 1) =
      (k : ℝ) + ρ := by
  have hzero : 2 * k + 1 ≠ 0 :=
    Nat.succ_ne_zero (2 * k)
  have hlast : 2 * k + 1 ≠ 2 * N + 3 :=
    ne_of_lt (Nat.finiteAbelPlana_odd_node_lt_last hk)
  have hsub : 2 * k + 1 - 1 = 2 * k :=
    Nat.add_sub_cancel (2 * k) 1
  have hmod : (2 * k) % 2 = 0 := by
    exact Nat.mul_mod_right 2 k
  have hdiv : (2 * k) / 2 = k := by
    exact
      Eq.trans
        (congrArg (fun m : ℕ => m / 2) (Nat.mul_comm 2 k))
        (Nat.mul_div_cancel k Nat.two_pos)
  exact
    Eq.trans
      (Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_unfold N ρ (2 * k + 1))
      (by
  calc
    (if 2 * k + 1 = 0 then (0 : ℝ)
      else if 2 * k + 1 = 2 * N + 3 then ((N + 1 : ℕ) : ℝ)
      else
        let j : ℕ := 2 * k + 1 - 1
        if j % 2 = 0 then ((j / 2 : ℕ) : ℝ) + ρ
        else (((j + 1) / 2 : ℕ) : ℝ) - ρ) =
        (if 2 * k + 1 = 2 * N + 3 then ((N + 1 : ℕ) : ℝ)
        else
          let j : ℕ := 2 * k + 1 - 1
          if j % 2 = 0 then ((j / 2 : ℕ) : ℝ) + ρ
          else (((j + 1) / 2 : ℕ) : ℝ) - ρ) :=
      if_neg hzero
    _ =
        (let j : ℕ := 2 * k + 1 - 1
          if j % 2 = 0 then ((j / 2 : ℕ) : ℝ) + ρ
          else (((j + 1) / 2 : ℕ) : ℝ) - ρ) :=
      if_neg hlast
    _ =
        (let j : ℕ := 2 * k
          if j % 2 = 0 then ((j / 2 : ℕ) : ℝ) + ρ
          else (((j + 1) / 2 : ℕ) : ℝ) - ρ) :=
      congrArg
        (fun j : ℕ =>
          if j % 2 = 0 then ((j / 2 : ℕ) : ℝ) + ρ
          else (((j + 1) / 2 : ℕ) : ℝ) - ρ)
        hsub
    _ = (((2 * k) / 2 : ℕ) : ℝ) + ρ :=
      if_pos hmod
    _ = (k : ℝ) + ρ :=
      congrArg (fun q : ℕ => ((q : ℕ) : ℝ) + ρ) hdiv)

/-- The first nonzero subdivision node is the left endpoint of the first
safe vertical strip. -/
theorem Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_first_safe_left
    (N : ℕ)
    (ρ : ℝ) :
    Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (0 + 1) =
      ρ := by
  have hindex :
      0 + 1 = 2 * 0 + 1 := by
    rfl
  have hsafe_cast :
      Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (2 * 0 + 1) =
        ((0 : ℕ) : ℝ) + ρ :=
    Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_safe_left
      N 0 ρ (Nat.zero_le N)
  have hsafe :
      Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (2 * 0 + 1) =
        (0 : ℝ) + ρ :=
    Eq.trans hsafe_cast
      (congrArg (fun z : ℝ => z + ρ) Nat.cast_zero)
  calc
    Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (0 + 1) =
        Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (2 * 0 + 1) := by
      exact congrArg
        (fun i : ℕ =>
          Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i)
        hindex
    _ = (0 : ℝ) + ρ :=
      hsafe
    _ = ρ :=
      zero_add ρ

/-- Even successor subdivision nodes are exactly the right endpoints of the
safe vertical strips. -/
theorem Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_safe_right
    (N k : ℕ)
    (ρ : ℝ)
    (hk : k ≤ N) :
    Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (2 * k + 2) =
      ((k + 1 : ℕ) : ℝ) - ρ := by
  have hzero : 2 * k + 2 ≠ 0 :=
    Nat.succ_ne_zero (2 * k + 1)
  have hlast : 2 * k + 2 ≠ 2 * N + 3 :=
    ne_of_lt (Nat.finiteAbelPlana_even_succ_node_lt_last hk)
  have hsub : 2 * k + 2 - 1 = 2 * k + 1 :=
    Nat.add_sub_cancel (2 * k + 1) 1
  have hmod : (2 * k + 1) % 2 = 1 := by
    exact
      Eq.trans
        (congrArg
          (fun m : ℕ => m % 2)
          (Nat.finiteAbelPlana_two_mul_add_one_comm k))
        (Nat.mul_add_mod_of_lt one_lt_two)
  have hdiv : (2 * k + 1 + 1) / 2 = k + 1 := by
    exact
      Eq.trans
        (congrArg
          (fun m : ℕ => m / 2)
          (Nat.finiteAbelPlana_two_mul_add_one_add_one_eq_succ_mul_two k))
        (Nat.mul_div_cancel (k + 1) Nat.two_pos)
  exact
    Eq.trans
      (Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_unfold N ρ (2 * k + 2))
      (by
  calc
    (if 2 * k + 2 = 0 then (0 : ℝ)
      else if 2 * k + 2 = 2 * N + 3 then ((N + 1 : ℕ) : ℝ)
      else
        let j : ℕ := 2 * k + 2 - 1
        if j % 2 = 0 then ((j / 2 : ℕ) : ℝ) + ρ
        else (((j + 1) / 2 : ℕ) : ℝ) - ρ) =
        (if 2 * k + 2 = 2 * N + 3 then ((N + 1 : ℕ) : ℝ)
        else
          let j : ℕ := 2 * k + 2 - 1
          if j % 2 = 0 then ((j / 2 : ℕ) : ℝ) + ρ
          else (((j + 1) / 2 : ℕ) : ℝ) - ρ) :=
      if_neg hzero
    _ =
        (let j : ℕ := 2 * k + 2 - 1
          if j % 2 = 0 then ((j / 2 : ℕ) : ℝ) + ρ
          else (((j + 1) / 2 : ℕ) : ℝ) - ρ) :=
      if_neg hlast
    _ =
        (let j : ℕ := 2 * k + 1
          if j % 2 = 0 then ((j / 2 : ℕ) : ℝ) + ρ
          else (((j + 1) / 2 : ℕ) : ℝ) - ρ) :=
      congrArg
        (fun j : ℕ =>
          if j % 2 = 0 then ((j / 2 : ℕ) : ℝ) + ρ
          else (((j + 1) / 2 : ℕ) : ℝ) - ρ)
        hsub
    _ =
        (((2 * k + 1 + 1) / 2 : ℕ) : ℝ) - ρ :=
      if_neg (by
        intro hzero_mod
        have hmod_contradiction : (1 : ℕ) = 0 :=
          Eq.trans hmod.symm hzero_mod
        exact Nat.one_ne_zero hmod_contradiction)
    _ = ((k + 1 : ℕ) : ℝ) - ρ :=
      congrArg (fun q : ℕ => ((q : ℕ) : ℝ) - ρ) hdiv)

/-- The left endpoint of the collar around the interior pole `n + 1`. -/
theorem Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_interior_left
    (N n : ℕ)
    (ρ : ℝ)
    (hn : n ∈ Finset.range N) :
    Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (2 * (n + 1)) =
      ((n + 1 : ℕ) : ℝ) - ρ := by
  exact
    Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_safe_right
      N n ρ (Nat.le_of_lt (Finset.mem_range.mp hn))

/-- The right endpoint of the collar around the interior pole `n + 1`. -/
theorem Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_interior_right
    (N n : ℕ)
    (ρ : ℝ)
    (hn : n ∈ Finset.range N) :
    Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (2 * (n + 1) + 1) =
      ((n + 1 : ℕ) : ℝ) + ρ := by
  have hnlt : n < N := Finset.mem_range.mp hn
  have hsucc_le : n + 1 ≤ N := Nat.succ_le_iff.mpr hnlt
  exact
    Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_safe_left
      N (n + 1) ρ hsucc_le

/-- Algebraic reindexing of the corrected adjacent interval chain into odd
safe intervals, the two endpoint collars, and the positive even interior
collars. -/
theorem Complex.sum_range_horizontalSubdivision_adjacent_reindex
    (N : ℕ)
    (G : ℕ → ℂ) :
    (∑ i in Finset.range (2 * N + 3), G i) =
      (∑ k in Finset.range (N + 1), G (2 * k + 1)) +
        (G 0 + G (2 * N + 2) +
          ∑ n in Finset.range N, G (2 * (n + 1))) := by
  induction N with
  | zero =>
      have hleft :
          (∑ i in Finset.range 3, G i) = G 0 + G 1 + G 2 := by
        have hthree :
            (∑ i in Finset.range 3, G i) =
              (∑ i in Finset.range 2, G i) + G 2 :=
          Finset.sum_range_succ (f := G) (n := 2)
        have htwo :
            (∑ i in Finset.range 2, G i) =
              (∑ i in Finset.range 1, G i) + G 1 :=
          Finset.sum_range_succ (f := G) (n := 1)
        have hone :
            (∑ i in Finset.range 1, G i) = G 0 :=
          Finset.sum_range_one G
        exact
          Eq.trans hthree
            (congrArg
              (fun z : ℂ => z + G 2)
              (Eq.trans htwo
                (congrArg (fun z : ℂ => z + G 1) hone)))
      have hodd :
          (∑ k in Finset.range 1, G (2 * k + 1)) = G 1 :=
        Finset.sum_range_one (fun k => G (2 * k + 1))
      have hinterior :
          (∑ n in Finset.range 0, G (2 * (n + 1))) = 0 :=
        Finset.sum_range_zero (fun n => G (2 * (n + 1)))
      have hodd_zero :
          (∑ k in Finset.range (0 + 1), G (2 * k + 1)) = G 1 :=
        hodd
      have hright_zero :
          G (2 * 0 + 2) = G 2 :=
        rfl
      have hright_tail :
          G 0 + G (2 * 0 + 2) +
              (∑ n in Finset.range 0, G (2 * (n + 1))) =
            G 0 + G 2 + 0 := by
        exact
          congrArg₂
            HAdd.hAdd
            (congrArg₂ HAdd.hAdd rfl hright_zero)
            hinterior
      have hright :
          (∑ k in Finset.range (0 + 1), G (2 * k + 1)) +
              (G 0 + G (2 * 0 + 2) +
                ∑ n in Finset.range 0, G (2 * (n + 1))) =
            G 1 + (G 0 + G 2 + 0) := by
        exact congrArg₂ HAdd.hAdd hodd_zero hright_tail
      calc
        (∑ i in Finset.range 3, G i) =
            G 0 + G 1 + G 2 := hleft
        _ = G 1 + (G 0 + G 2 + 0) :=
          Complex.finiteAbelPlana_horizontalSubdivision_base_algebra
            (G 0) (G 1) (G 2)
        _ =
            (∑ k in Finset.range (0 + 1), G (2 * k + 1)) +
              (G 0 + G (2 * 0 + 2) +
                ∑ n in Finset.range 0, G (2 * (n + 1))) :=
          hright.symm
  | succ N ih =>
      have hlast :
          2 * (N + 1) + 3 = (2 * N + 3) + 2 :=
        Nat.finiteAbelPlana_last_index_succ_succ N
      have hleft_expand :
          (∑ i in Finset.range ((2 * N + 3) + 2), G i) =
            (∑ i in Finset.range (2 * N + 3), G i) +
              G (2 * N + 3) + G (2 * N + 4) := by
        calc
          (∑ i in Finset.range ((2 * N + 3) + 2), G i) =
              (∑ i in Finset.range (2 * N + 3), G i) +
                G (2 * N + 3) + G ((2 * N + 3) + 1) :=
            Finset.sum_range_add_two_complex G (2 * N + 3)
          _ =
              (∑ i in Finset.range (2 * N + 3), G i) +
                G (2 * N + 3) + G (2 * N + 4) :=
            rfl
      have hodd_expand :
          (∑ k in Finset.range (N + 1 + 1), G (2 * k + 1)) =
            (∑ k in Finset.range (N + 1), G (2 * k + 1)) +
              G (2 * (N + 1) + 1) :=
        Finset.sum_range_succ
          (f := fun k => G (2 * k + 1))
          (n := N + 1)
      have hinterior_expand :
          (∑ n in Finset.range (N + 1), G (2 * (n + 1))) =
            (∑ n in Finset.range N, G (2 * (n + 1))) +
              G (2 * (N + 1)) :=
        Finset.sum_range_succ
          (f := fun n => G (2 * (n + 1)))
          (n := N)
      have hnew_interior : 2 * (N + 1) = 2 * N + 2 := by
        calc
          2 * (N + 1) = 2 * N + 2 * 1 :=
            Nat.mul_add 2 N 1
          _ = 2 * N + 2 := rfl
      have hnew_odd : 2 * (N + 1) + 1 = 2 * N + 3 := by
        calc
          2 * (N + 1) + 1 = (2 * N + 2) + 1 := by
            exact congrArg (fun m : ℕ => m + 1) hnew_interior
          _ = 2 * N + 3 :=
            Nat.finiteAbelPlana_last_predecessor_add_one N
      have hnew_right : 2 * (N + 1) + 2 = 2 * N + 4 := by
        calc
          2 * (N + 1) + 2 = (2 * N + 2) + 2 := by
            exact congrArg (fun m : ℕ => m + 2) hnew_interior
          _ = 2 * N + (2 + 2) :=
            Nat.add_assoc (2 * N) 2 2
          _ = 2 * N + 4 := rfl
      exact
        hlast ▸ hleft_expand ▸ ih ▸ hodd_expand ▸ hinterior_expand ▸
          hnew_odd.symm ▸ hnew_right.symm ▸ hnew_interior.symm ▸
          Complex.finiteAbelPlana_horizontalSubdivision_succ_algebra
            (∑ k in Finset.range (N + 1), G (2 * k + 1))
            (G 0)
            (G (2 * N + 2))
            (∑ n in Finset.range N, G (2 * (n + 1)))
            (G (2 * N + 3))
            (G (2 * N + 4))

/-- Lower-horizontal adjacent intervals for the corrected endpoint chain
reindex to the safe strips plus endpoint and interior collars. -/
theorem Complex.finiteAbelPlana_log_lowerHorizontalSubdivision_sum_eq_verticalStrips_add_capCollars
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    (∑ i in Finset.range (2 * N + 3),
      ∫ x : ℝ in
        (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i)..
          (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)),
        Complex.finiteAbelPlanaLogRectangleIntegrand w
          ((x : ℂ) - Complex.I * (T : ℂ))) =
      (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
        Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ) +
        (Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ +
          Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ +
            ∑ n in Finset.range N,
              Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ) := by
  let G : ℕ → ℂ := fun i =>
    ∫ x : ℝ in
      (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i)..
        (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)),
      Complex.finiteAbelPlanaLogRectangleIntegrand w
        ((x : ℂ) - Complex.I * (T : ℂ))
  have hsafe :
      (∑ k in Finset.range (N + 1), G (2 * k + 1)) =
        ∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
          Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ := by
    calc
      (∑ k in Finset.range (N + 1), G (2 * k + 1)) =
          ∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
            G (2 * k + 1) :=
        congrArg
          (fun s : Finset ℕ => ∑ k in s, G (2 * k + 1))
          (Complex.finiteAbelPlana_verticalStripIndexSet_unfold N).symm
      _ =
          ∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
            Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ :=
        Finset.sum_congr rfl
          (fun k hk => by
            have hk_le : k ≤ N :=
              Nat.lt_succ_iff.mp
                (Complex.mem_finiteAbelPlanaVerticalStripIndexSet_iff.mp hk)
            have hleft :
                Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (2 * k + 1) =
                  (k : ℝ) + ρ :=
              Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_safe_left
                N k ρ hk_le
            have hright :
                Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (2 * k + 1 + 1) =
                  ((k + 1 : ℕ) : ℝ) - ρ := by
              exact
                Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_safe_right
                  N k ρ hk_le
            exact
              congrArg₂
                (fun a b : ℝ =>
                  ∫ x : ℝ in a..b,
                    Complex.finiteAbelPlanaLogRectangleIntegrand w
                      ((x : ℂ) - Complex.I * (T : ℂ)))
                hleft
                hright)
  have hleft :
      G 0 = Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ := by
    have hstart :
        Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ 0 = 0 :=
      Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_start N ρ
    have hright :
        Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (0 + 1) =
          ρ := by
      calc
        Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (0 + 1) =
            Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (2 * 0 + 1) := rfl
        _ = ((0 : ℕ) : ℝ) + ρ :=
          Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_safe_left
            N 0 ρ (Nat.zero_le N)
        _ = (0 : ℝ) + ρ := by
          exact congrArg (fun z : ℝ => z + ρ) Nat.cast_zero
        _ = ρ :=
          zero_add ρ
    exact
      congrArg₂
        (fun a b : ℝ =>
          ∫ x : ℝ in a..b,
            Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((x : ℂ) - Complex.I * (T : ℂ)))
        hstart
        hright
  have hright :
      G (2 * N + 2) =
        Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ := by
    have hleft :
        Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (2 * N + 2) =
          ((N + 1 : ℕ) : ℝ) - ρ :=
      Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_safe_right
        N N ρ le_rfl
    have hsucc :
        2 * N + 2 + 1 = 2 * N + 3 :=
      Nat.finiteAbelPlana_last_predecessor_add_one N
    have hend :
        Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (2 * N + 3) =
          ((N + 1 : ℕ) : ℝ) :=
      Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_end N ρ
    have hright_endpoint :
        Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (2 * N + 2 + 1) =
          ((N + 1 : ℕ) : ℝ) :=
      Eq.trans
        (congrArg
          (fun i : ℕ => Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i)
          hsucc)
        hend
    exact
      congrArg₂
        (fun a b : ℝ =>
          ∫ x : ℝ in a..b,
            Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((x : ℂ) - Complex.I * (T : ℂ)))
        hleft
        hright_endpoint
  have hinterior :
      (∑ n in Finset.range N, G (2 * (n + 1))) =
        ∑ n in Finset.range N,
          Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ := by
    exact Finset.sum_congr rfl
      (fun n hn => by
        have hleft :
            Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (2 * (n + 1)) =
              ((n + 1 : ℕ) : ℝ) - ρ :=
          Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_interior_left
            N n ρ hn
        have hright :
            Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (2 * (n + 1) + 1) =
              ((n + 1 : ℕ) : ℝ) + ρ :=
          Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_interior_right
            N n ρ hn
        exact
          congrArg₂
            (fun a b : ℝ =>
              ∫ x : ℝ in a..b,
                Complex.finiteAbelPlanaLogRectangleIntegrand w
                  ((x : ℂ) - Complex.I * (T : ℂ)))
            hleft
            hright)
  calc
    (∑ i in Finset.range (2 * N + 3), G i) =
        (∑ k in Finset.range (N + 1), G (2 * k + 1)) +
          (G 0 + G (2 * N + 2) +
            ∑ n in Finset.range N, G (2 * (n + 1))) := by
      exact Complex.sum_range_horizontalSubdivision_adjacent_reindex N G
    _ =
        (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
          Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ) +
          (Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ +
            Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ +
              ∑ n in Finset.range N,
                Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ) := by
      exact Complex.add_triple_congr hsafe hleft hright hinterior

/-- Upper-horizontal adjacent intervals for the corrected endpoint chain
reindex to the safe strips plus endpoint and interior collars. -/
theorem Complex.finiteAbelPlana_log_upperHorizontalSubdivision_sum_eq_verticalStrips_add_capCollars
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    (∑ i in Finset.range (2 * N + 3),
      ∫ x : ℝ in
        (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i)..
          (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)),
        Complex.finiteAbelPlanaLogRectangleIntegrand w
          ((x : ℂ) + Complex.I * (T : ℂ))) =
      (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
        Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ) +
        (Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
          Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
            ∑ n in Finset.range N,
              Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ) := by
  let G : ℕ → ℂ := fun i =>
    ∫ x : ℝ in
      (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i)..
        (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)),
      Complex.finiteAbelPlanaLogRectangleIntegrand w
        ((x : ℂ) + Complex.I * (T : ℂ))
  have hsafe :
      (∑ k in Finset.range (N + 1), G (2 * k + 1)) =
        ∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
          Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ := by
    calc
      (∑ k in Finset.range (N + 1), G (2 * k + 1)) =
          ∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
            G (2 * k + 1) :=
        congrArg
          (fun s : Finset ℕ => ∑ k in s, G (2 * k + 1))
          (Complex.finiteAbelPlana_verticalStripIndexSet_unfold N).symm
      _ =
          ∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
            Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ :=
        Finset.sum_congr rfl
          (fun k hk => by
            have hk_le : k ≤ N :=
              Nat.lt_succ_iff.mp
                (Complex.mem_finiteAbelPlanaVerticalStripIndexSet_iff.mp hk)
            have hleft :
                Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (2 * k + 1) =
                  (k : ℝ) + ρ :=
              Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_safe_left
                N k ρ hk_le
            have hright :
                Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (2 * k + 1 + 1) =
                  ((k + 1 : ℕ) : ℝ) - ρ := by
              exact
                Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_safe_right
                  N k ρ hk_le
            exact
              congrArg₂
                (fun a b : ℝ =>
                  ∫ x : ℝ in a..b,
                    Complex.finiteAbelPlanaLogRectangleIntegrand w
                      ((x : ℂ) + Complex.I * (T : ℂ)))
                hleft
                hright)
  have hleft :
      G 0 = Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ := by
    have hstart :
        Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ 0 = 0 :=
      Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_start N ρ
    have hright :
        Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (0 + 1) =
          ρ := by
      calc
        Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (0 + 1) =
            Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (2 * 0 + 1) := rfl
        _ = ((0 : ℕ) : ℝ) + ρ :=
          Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_safe_left
            N 0 ρ (Nat.zero_le N)
        _ = (0 : ℝ) + ρ := by
          exact congrArg (fun z : ℝ => z + ρ) Nat.cast_zero
        _ = ρ :=
          zero_add ρ
    exact
      congrArg₂
        (fun a b : ℝ =>
          ∫ x : ℝ in a..b,
            Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((x : ℂ) + Complex.I * (T : ℂ)))
        hstart
        hright
  have hright :
      G (2 * N + 2) =
        Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ := by
    have hleft :
        Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (2 * N + 2) =
          ((N + 1 : ℕ) : ℝ) - ρ :=
      Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_safe_right
        N N ρ le_rfl
    have hsucc :
        2 * N + 2 + 1 = 2 * N + 3 :=
      Nat.finiteAbelPlana_last_predecessor_add_one N
    have hend :
        Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (2 * N + 3) =
          ((N + 1 : ℕ) : ℝ) :=
      Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_end N ρ
    have hright_endpoint :
        Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (2 * N + 2 + 1) =
          ((N + 1 : ℕ) : ℝ) :=
      Eq.trans
        (congrArg
          (fun i : ℕ => Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i)
          hsucc)
        hend
    exact
      congrArg₂
        (fun a b : ℝ =>
          ∫ x : ℝ in a..b,
            Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((x : ℂ) + Complex.I * (T : ℂ)))
        hleft
        hright_endpoint
  have hinterior :
      (∑ n in Finset.range N, G (2 * (n + 1))) =
        ∑ n in Finset.range N,
          Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ := by
    exact Finset.sum_congr rfl
      (fun n hn => by
        have hleft :
            Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (2 * (n + 1)) =
              ((n + 1 : ℕ) : ℝ) - ρ :=
          Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_interior_left
            N n ρ hn
        have hright :
            Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (2 * (n + 1) + 1) =
              ((n + 1 : ℕ) : ℝ) + ρ :=
          Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_interior_right
            N n ρ hn
        exact
          congrArg₂
            (fun a b : ℝ =>
              ∫ x : ℝ in a..b,
                Complex.finiteAbelPlanaLogRectangleIntegrand w
                  ((x : ℂ) + Complex.I * (T : ℂ)))
            hleft
            hright)
  calc
    (∑ i in Finset.range (2 * N + 3), G i) =
        (∑ k in Finset.range (N + 1), G (2 * k + 1)) +
          (G 0 + G (2 * N + 2) +
            ∑ n in Finset.range N, G (2 * (n + 1))) := by
      exact Complex.sum_range_horizontalSubdivision_adjacent_reindex N G
    _ =
        (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
          Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ) +
          (Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
            Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
              ∑ n in Finset.range N,
                Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ) := by
      exact Complex.add_triple_congr hsafe hleft hright hinterior

/-- Every endpoint of the finite horizontal subdivision lies on the real
projection of the closed Abel-Plana rectangle. -/
theorem Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_mem_closedInterval
    (N : ℕ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hρquarter : ρ < (1 : ℝ) / 4)
    {i : ℕ}
    (hi : i ≤ 2 * N + 3) :
    Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i ∈
      [[(0 : ℝ), ((N + 1 : ℕ) : ℝ)]] := by
  have hρ_lt_one : ρ < 1 :=
    Real.lt_one_of_lt_one_div_four hρquarter
  have hzero_le_right : (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
    exact Nat.cast_nonneg (N + 1)
  match (inferInstance : Decidable (i = 0)) with
  | isTrue hzero =>
    have hendpoint :
        Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i = 0 := by
      exact hzero ▸ Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_start N ρ
    exact
      Eq.mp
        (congrArg
          (fun x : ℝ => x ∈ [[(0 : ℝ), ((N + 1 : ℕ) : ℝ)]])
          hendpoint.symm)
        (Set.left_mem_uIcc : (0 : ℝ) ∈ [[(0 : ℝ), ((N + 1 : ℕ) : ℝ)]])
  | isFalse hzero_ne =>
    match (inferInstance : Decidable (i = 2 * N + 3)) with
    | isTrue hlast =>
      have hendpoint :
          Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i =
            ((N + 1 : ℕ) : ℝ) := by
        exact hlast ▸ Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_end N ρ
      exact
        Eq.mp
          (congrArg
            (fun x : ℝ => x ∈ [[(0 : ℝ), ((N + 1 : ℕ) : ℝ)]])
            hendpoint.symm)
          (Set.right_mem_uIcc :
            ((N + 1 : ℕ) : ℝ) ∈ [[(0 : ℝ), ((N + 1 : ℕ) : ℝ)]])
    | isFalse hlast_ne =>
      have hilt : i < 2 * N + 3 :=
        lt_of_le_of_ne hi hlast_ne
      let j : ℕ := i - 1
      have hj_le : j ≤ 2 * N + 1 := by
        show i - 1 ≤ 2 * N + 1
        exact Nat.finiteAbelPlana_pred_le_last_interior_of_lt_last hilt
      have hendpoint_body :
          Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i =
            (if j % 2 = 0 then ((j / 2 : ℕ) : ℝ) + ρ
            else (((j + 1) / 2 : ℕ) : ℝ) - ρ) := by
        exact
          Eq.trans
            (Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_unfold N ρ i)
            (Eq.trans (if_neg hzero_ne) (if_neg hlast_ne))
      match (inferInstance : Decidable (j % 2 = 0)) with
      | isTrue hmod =>
        have hendpoint :
            Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i =
              ((j / 2 : ℕ) : ℝ) + ρ :=
          Eq.trans hendpoint_body (if_pos hmod)
        have hjdiv_le : j / 2 ≤ N := by
          exact Nat.finiteAbelPlana_div_two_le_of_le_last_interior hj_le
        have hmem_icc :
            ((j / 2 : ℕ) : ℝ) + ρ ∈
              Set.Icc (0 : ℝ) ((N + 1 : ℕ) : ℝ) := by
          constructor
          · have hnonneg : (0 : ℝ) ≤ ((j / 2 : ℕ) : ℝ) := by
              exact Nat.cast_nonneg (j / 2)
            exact add_nonneg hnonneg (le_of_lt hρ)
          · have hjdiv_real : (((j / 2 : ℕ) : ℝ) : ℝ) ≤ (N : ℝ) := by
              exact Nat.cast_le.mpr hjdiv_le
            have hN_le : (N : ℝ) + 1 = ((N + 1 : ℕ) : ℝ) := by
              exact Eq.symm (Nat.cast_add_one N)
            calc
              ((j / 2 : ℕ) : ℝ) + ρ ≤ (N : ℝ) + ρ := by
                exact add_le_add_right hjdiv_real ρ
              _ ≤ (N : ℝ) + 1 := by
                exact add_le_add_left (le_of_lt hρ_lt_one) (N : ℝ)
              _ = ((N + 1 : ℕ) : ℝ) := hN_le
        have hmem :
            ((j / 2 : ℕ) : ℝ) + ρ ∈
              [[(0 : ℝ), ((N + 1 : ℕ) : ℝ)]] :=
          Eq.mp
            (congrArg
              (fun S : Set ℝ => ((j / 2 : ℕ) : ℝ) + ρ ∈ S)
              (Set.uIcc_of_le hzero_le_right).symm)
            hmem_icc
        exact
          Eq.mp
            (congrArg
              (fun x : ℝ => x ∈ [[(0 : ℝ), ((N + 1 : ℕ) : ℝ)]])
              hendpoint.symm)
            hmem
      | isFalse hmod_ne =>
        have hendpoint :
            Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i =
              (((j + 1) / 2 : ℕ) : ℝ) - ρ :=
          Eq.trans hendpoint_body (if_neg hmod_ne)
        have hj_nonzero : j ≠ 0 := by
          intro hj_zero
          exact
            hmod_ne
              (congrArg (fun q : ℕ => q % 2) hj_zero)
        have hj_pos : 0 < j :=
          Nat.pos_of_ne_zero hj_nonzero
        have hjdiv_pos : 1 ≤ (j + 1) / 2 := by
          exact Nat.finiteAbelPlana_one_le_succ_div_two_of_pos hj_pos
        have hjdiv_le : (j + 1) / 2 ≤ N + 1 := by
          exact
            Nat.finiteAbelPlana_succ_div_two_le_succ_of_le_last_interior
              hj_le
        have hmem_icc :
            (((j + 1) / 2 : ℕ) : ℝ) - ρ ∈
              Set.Icc (0 : ℝ) ((N + 1 : ℕ) : ℝ) := by
          constructor
          · have hleft : ρ ≤ (((j + 1) / 2 : ℕ) : ℝ) := by
              have hleft_lt : ρ < (((j + 1) / 2 : ℕ) : ℝ) := by
                calc
                  ρ < 1 := hρ_lt_one
                  _ = ((1 : ℕ) : ℝ) := Eq.symm Nat.cast_one
                  _ ≤ (((j + 1) / 2 : ℕ) : ℝ) := by
                    exact Nat.cast_le.mpr hjdiv_pos
              exact le_of_lt hleft_lt
            exact sub_nonneg.mpr hleft
          · have hright : (((j + 1) / 2 : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
              exact Nat.cast_le.mpr hjdiv_le
            exact (sub_le_self _ (le_of_lt hρ)).trans hright
        have hmem :
            (((j + 1) / 2 : ℕ) : ℝ) - ρ ∈
              [[(0 : ℝ), ((N + 1 : ℕ) : ℝ)]] :=
          Eq.mp
            (congrArg
              (fun S : Set ℝ => (((j + 1) / 2 : ℕ) : ℝ) - ρ ∈ S)
              (Set.uIcc_of_le hzero_le_right).symm)
            hmem_icc
        exact
          Eq.mp
            (congrArg
              (fun x : ℝ => x ∈ [[(0 : ℝ), ((N + 1 : ℕ) : ℝ)]])
              hendpoint.symm)
            hmem

/-- Membership in the horizontal endpoint interval gives the real-coordinate
membership used by the rectangular product definition. -/
theorem Complex.finiteAbelPlana_horizontalClosedInterval_mem_rectangle_re
    (N : ℕ)
    {x : ℝ}
    (hx : x ∈ [[(0 : ℝ), ((N + 1 : ℕ) : ℝ)]]) :
    x ∈ Set.Icc (0 : ℝ) ((N : ℝ) + 1) := by
  have hzero_le_right : (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
    exact Nat.cast_nonneg (N + 1)
  have hx_icc :
      x ∈ Set.Icc (0 : ℝ) ((N + 1 : ℕ) : ℝ) :=
    Eq.mp
      (congrArg
        (fun S : Set ℝ => x ∈ S)
        (Set.uIcc_of_le hzero_le_right))
      hx
  exact
    Eq.mp
      (congrArg
        (fun b : ℝ => x ∈ Set.Icc (0 : ℝ) b)
        (Nat.cast_add_one N))
      hx_icc

/-- The upper horizontal edge has real coordinate `x`. -/
theorem Complex.finiteAbelPlana_upperHorizontalPoint_re
    (x T : ℝ) :
    (((x : ℂ) + Complex.I * (T : ℂ)).re) = x := by
  calc
    (((x : ℂ) + Complex.I * (T : ℂ)).re) =
        (x : ℂ).re + (Complex.I * (T : ℂ)).re :=
      Complex.add_re (x : ℂ) (Complex.I * (T : ℂ))
    _ = x + -((T : ℂ).im) := by
      exact
        congrArg₂
          HAdd.hAdd
          (Complex.ofReal_re x)
          (Complex.I_mul_re (T : ℂ))
    _ = x + -0 := by
      exact congrArg (fun y : ℝ => x + -y) (Complex.ofReal_im T)
    _ = x + 0 := by
      exact congrArg (fun y : ℝ => x + y) (neg_zero : -(0 : ℝ) = 0)
    _ = x := add_zero x

/-- The upper horizontal edge has imaginary coordinate `T`. -/
theorem Complex.finiteAbelPlana_upperHorizontalPoint_im
    (x T : ℝ) :
    (((x : ℂ) + Complex.I * (T : ℂ)).im) = T := by
  calc
    (((x : ℂ) + Complex.I * (T : ℂ)).im) =
        (x : ℂ).im + (Complex.I * (T : ℂ)).im :=
      Complex.add_im (x : ℂ) (Complex.I * (T : ℂ))
    _ = 0 + (T : ℂ).re := by
      exact
        congrArg₂
          HAdd.hAdd
          (Complex.ofReal_im x)
          (Complex.I_mul_im (T : ℂ))
    _ = 0 + T := by
      exact congrArg (fun y : ℝ => 0 + y) (Complex.ofReal_re T)
    _ = T := zero_add T

/-- The lower horizontal edge has real coordinate `x`. -/
theorem Complex.finiteAbelPlana_lowerHorizontalPoint_re
    (x T : ℝ) :
    (((x : ℂ) - Complex.I * (T : ℂ)).re) = x := by
  calc
    (((x : ℂ) - Complex.I * (T : ℂ)).re) =
        (x : ℂ).re - (Complex.I * (T : ℂ)).re :=
      Complex.sub_re (x : ℂ) (Complex.I * (T : ℂ))
    _ = x - -((T : ℂ).im) := by
      exact
        congrArg₂
          HSub.hSub
          (Complex.ofReal_re x)
          (Complex.I_mul_re (T : ℂ))
    _ = x - -0 := by
      exact congrArg (fun y : ℝ => x - -y) (Complex.ofReal_im T)
    _ = x - 0 := by
      exact congrArg (fun y : ℝ => x - y) (neg_zero : -(0 : ℝ) = 0)
    _ = x := sub_zero x

/-- The lower horizontal edge has imaginary coordinate `-T`. -/
theorem Complex.finiteAbelPlana_lowerHorizontalPoint_im
    (x T : ℝ) :
    (((x : ℂ) - Complex.I * (T : ℂ)).im) = -T := by
  calc
    (((x : ℂ) - Complex.I * (T : ℂ)).im) =
        (x : ℂ).im - (Complex.I * (T : ℂ)).im :=
      Complex.sub_im (x : ℂ) (Complex.I * (T : ℂ))
    _ = 0 - (T : ℂ).re := by
      exact
        congrArg₂
          HSub.hSub
          (Complex.ofReal_im x)
          (Complex.I_mul_im (T : ℂ))
    _ = 0 - T := by
      exact congrArg (fun y : ℝ => 0 - y) (Complex.ofReal_re T)
    _ = -T := zero_sub T

/-- Subtracting an integer center from the upper horizontal edge preserves
imaginary coordinate `T`. -/
theorem Complex.finiteAbelPlana_upperHorizontalPoint_sub_nat_im
    (x T : ℝ)
    (m : ℕ) :
    ((((x : ℂ) + Complex.I * (T : ℂ)) - (m : ℂ)).im) = T := by
  calc
    ((((x : ℂ) + Complex.I * (T : ℂ)) - (m : ℂ)).im) =
        (((x : ℂ) + Complex.I * (T : ℂ)).im) - (m : ℂ).im :=
      Complex.sub_im ((x : ℂ) + Complex.I * (T : ℂ)) (m : ℂ)
    _ = T - 0 := by
      exact
        congrArg₂
          HSub.hSub
          (Complex.finiteAbelPlana_upperHorizontalPoint_im x T)
          rfl
    _ = T := sub_zero T

/-- Subtracting an integer center from the lower horizontal edge preserves
imaginary coordinate `-T`. -/
theorem Complex.finiteAbelPlana_lowerHorizontalPoint_sub_nat_im
    (x T : ℝ)
    (m : ℕ) :
    ((((x : ℂ) - Complex.I * (T : ℂ)) - (m : ℂ)).im) = -T := by
  calc
    ((((x : ℂ) - Complex.I * (T : ℂ)) - (m : ℂ)).im) =
        (((x : ℂ) - Complex.I * (T : ℂ)).im) - (m : ℂ).im :=
      Complex.sub_im ((x : ℂ) - Complex.I * (T : ℂ)) (m : ℂ)
    _ = -T - 0 := by
      exact
        congrArg₂
          HSub.hSub
          (Complex.finiteAbelPlana_lowerHorizontalPoint_im x T)
          rfl
    _ = -T := sub_zero (-T)

/-- A horizontal top or bottom edge point of the finite Abel-Plana rectangle
avoids every deleted integer disk under the deleted-geometry hypotheses. -/
theorem Complex.finiteAbelPlana_horizontalEdgePoint_not_mem_deletedDisk
    {N m : ℕ}
    {T ρ x : ℝ}
    (hx : x ∈ [[(0 : ℝ), ((N + 1 : ℕ) : ℝ)]])
    (hρ : 0 < ρ)
    (hTρ : ρ < |T| / 2)
    (hm : m ∈ Finset.range (N + 2)) :
    ((x : ℂ) + Complex.I * (T : ℂ)) ∉ Metric.ball (m : ℂ) ρ ∧
      ((x : ℂ) - Complex.I * (T : ℂ)) ∉ Metric.ball (m : ℂ) ρ := by
  have hTpos : 0 < |T| := by
    have hhalf_pos : 0 < |T| / 2 := lt_trans hρ hTρ
    exact lt_of_lt_of_le hhalf_pos (half_le_self (abs_nonneg T))
  have hρ_lt_absT : ρ < |T| := by
    have hhalf_lt_abs : |T| / 2 < |T| :=
      half_lt_self hTpos
    exact lt_trans hTρ hhalf_lt_abs
  constructor
  · intro hball
    have hdist_lt :
        dist ((x : ℂ) + Complex.I * (T : ℂ)) (m : ℂ) < ρ :=
      Metric.mem_ball.mp hball
    have him_le_norm :
        |T| ≤ ‖((x : ℂ) + Complex.I * (T : ℂ)) - (m : ℂ)‖ := by
      have him :
          (((x : ℂ) + Complex.I * (T : ℂ)) - (m : ℂ)).im = T := by
        exact Complex.finiteAbelPlana_upperHorizontalPoint_sub_nat_im x T m
      calc
        |T| = |(((x : ℂ) + Complex.I * (T : ℂ)) - (m : ℂ)).im| := by
          exact congrArg abs him.symm
        _ ≤ ‖((x : ℂ) + Complex.I * (T : ℂ)) - (m : ℂ)‖ :=
          Complex.abs_im_le_abs _
    have hnorm_lt :
        ‖((x : ℂ) + Complex.I * (T : ℂ)) - (m : ℂ)‖ < ρ := by
      exact
        Eq.mp
          (congrArg
            (fun r : ℝ => r < ρ)
            (dist_eq_norm ((x : ℂ) + Complex.I * (T : ℂ)) (m : ℂ)))
          hdist_lt
    exact (not_lt_of_ge (le_of_lt hρ_lt_absT)) (him_le_norm.trans_lt hnorm_lt)
  · intro hball
    have hdist_lt :
        dist ((x : ℂ) - Complex.I * (T : ℂ)) (m : ℂ) < ρ :=
      Metric.mem_ball.mp hball
    have him_le_norm :
        |T| ≤ ‖((x : ℂ) - Complex.I * (T : ℂ)) - (m : ℂ)‖ := by
      have him :
          (((x : ℂ) - Complex.I * (T : ℂ)) - (m : ℂ)).im = -T := by
        exact Complex.finiteAbelPlana_lowerHorizontalPoint_sub_nat_im x T m
      calc
        |T| = |(((x : ℂ) - Complex.I * (T : ℂ)) - (m : ℂ)).im| := by
          exact
            Eq.trans
              (abs_neg T).symm
              (congrArg abs him.symm)
        _ ≤ ‖((x : ℂ) - Complex.I * (T : ℂ)) - (m : ℂ)‖ :=
          Complex.abs_im_le_abs _
    have hnorm_lt :
        ‖((x : ℂ) - Complex.I * (T : ℂ)) - (m : ℂ)‖ < ρ := by
      exact
        Eq.mp
          (congrArg
            (fun r : ℝ => r < ρ)
            (dist_eq_norm ((x : ℂ) - Complex.I * (T : ℂ)) (m : ℂ)))
          hdist_lt
    exact (not_lt_of_ge (le_of_lt hρ_lt_absT)) (him_le_norm.trans_lt hnorm_lt)

/-- Horizontal edge segments in the finite subdivision are contained in the
punctured Abel-Plana rectangle. -/
theorem Complex.finiteAbelPlana_horizontalSubdivision_segment_subset_puncturedRectangle
    {w : ℂ}
    {N : ℕ}
    {T ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    {i : ℕ}
    (hi : i < 2 * N + 3) :
    (∀ x ∈ [[Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i,
        Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)]],
      ((x : ℂ) + Complex.I * (T : ℂ)) ∈
        Complex.finiteAbelPlanaPuncturedRectangle N T ρ) ∧
    (∀ x ∈ [[Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i,
        Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)]],
      ((x : ℂ) - Complex.I * (T : ℂ)) ∈
        Complex.finiteAbelPlanaPuncturedRectangle N T ρ) := by
  have hi_le : i ≤ 2 * N + 3 := le_of_lt hi
  have hisucc_le : i + 1 ≤ 2 * N + 3 :=
    Nat.succ_le_of_lt hi
  have hend₀ :
      Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i ∈
        [[(0 : ℝ), ((N + 1 : ℕ) : ℝ)]] :=
    Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_mem_closedInterval
      N hρ hdeleted_geometry.1 hi_le
  have hend₁ :
      Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1) ∈
        [[(0 : ℝ), ((N + 1 : ℕ) : ℝ)]] :=
    Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_mem_closedInterval
      N hρ hdeleted_geometry.1 hisucc_le
  have hsegment_subset :
      [[Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i,
        Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)]] ⊆
        [[(0 : ℝ), ((N + 1 : ℕ) : ℝ)]] :=
    Set.uIcc_subset_uIcc hend₀ hend₁
  constructor
  · intro x hx
    have hxglobal :
        x ∈ [[(0 : ℝ), ((N + 1 : ℕ) : ℝ)]] :=
      hsegment_subset hx
    have him : (((x : ℂ) + Complex.I * (T : ℂ)).im) ∈ [[-T, T]] := by
      exact
        Eq.mp
          (congrArg
            (fun y : ℝ => y ∈ [[-T, T]])
            (Complex.finiteAbelPlana_upperHorizontalPoint_im x T).symm)
          (Set.right_mem_uIcc : T ∈ [[-T, T]])
    have him_rect : (((x : ℂ) + Complex.I * (T : ℂ)).im) ∈ Set.Icc (-T) T := by
      have hneg_le : -T ≤ T :=
        neg_le_self hT.le
      exact
        Eq.mp
          (congrArg
            (fun y : ℝ => y ∈ Set.Icc (-T) T)
            (Complex.finiteAbelPlana_upperHorizontalPoint_im x T).symm)
          (Set.right_mem_Icc.mpr hneg_le)
    have havoid :
        ∀ m ∈ Finset.range (N + 2),
          ((x : ℂ) + Complex.I * (T : ℂ)) ∉ Metric.ball (m : ℂ) ρ := by
      intro m hm
      exact
        (Complex.finiteAbelPlana_horizontalEdgePoint_not_mem_deletedDisk
          hxglobal hρ hdeleted_geometry.2.1 hm).1
    exact
      Complex.mem_finiteAbelPlanaPuncturedRectangle_iff.mpr
        ⟨Complex.mem_reProdIm.mpr
          ⟨Eq.mp
            (congrArg
              (fun y : ℝ => y ∈ Set.Icc (0 : ℝ) ((N : ℝ) + 1))
              (Complex.finiteAbelPlana_upperHorizontalPoint_re x T).symm)
            (Complex.finiteAbelPlana_horizontalClosedInterval_mem_rectangle_re
              N hxglobal),
            him_rect⟩,
          havoid⟩
  · intro x hx
    have hxglobal :
        x ∈ [[(0 : ℝ), ((N + 1 : ℕ) : ℝ)]] :=
      hsegment_subset hx
    have him : (((x : ℂ) - Complex.I * (T : ℂ)).im) ∈ [[-T, T]] := by
      exact
        Eq.mp
          (congrArg
            (fun y : ℝ => y ∈ [[-T, T]])
            (Complex.finiteAbelPlana_lowerHorizontalPoint_im x T).symm)
          (Set.left_mem_uIcc : (-T) ∈ [[-T, T]])
    have him_rect : (((x : ℂ) - Complex.I * (T : ℂ)).im) ∈ Set.Icc (-T) T := by
      have hneg_le : -T ≤ T :=
        neg_le_self hT.le
      exact
        Eq.mp
          (congrArg
            (fun y : ℝ => y ∈ Set.Icc (-T) T)
            (Complex.finiteAbelPlana_lowerHorizontalPoint_im x T).symm)
          (Set.left_mem_Icc.mpr hneg_le)
    have havoid :
        ∀ m ∈ Finset.range (N + 2),
          ((x : ℂ) - Complex.I * (T : ℂ)) ∉ Metric.ball (m : ℂ) ρ := by
      intro m hm
      exact
        (Complex.finiteAbelPlana_horizontalEdgePoint_not_mem_deletedDisk
          hxglobal hρ hdeleted_geometry.2.1 hm).2
    exact
      Complex.mem_finiteAbelPlanaPuncturedRectangle_iff.mpr
        ⟨Complex.mem_reProdIm.mpr
          ⟨Eq.mp
            (congrArg
              (fun y : ℝ => y ∈ Set.Icc (0 : ℝ) ((N : ℝ) + 1))
              (Complex.finiteAbelPlana_lowerHorizontalPoint_re x T).symm)
            (Complex.finiteAbelPlana_horizontalClosedInterval_mem_rectangle_re
              N hxglobal),
            him_rect⟩,
          havoid⟩

/-- Interval-integrability of every adjacent interval in a horizontal
subdivision chain.

This is the only analytic hygiene input needed by the finite real-line
partition theorem: each closed horizontal subinterval lies in the punctured
rectangle, so regularity of the contour integrand there gives interval
integrability. -/
theorem Complex.finiteAbelPlana_log_horizontalSubdivision_intervalIntegrable
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    (∀ i < 2 * N + 3,
      IntervalIntegrable
        (fun x : ℝ =>
          Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((x : ℂ) - Complex.I * (T : ℂ)))
        volume
        (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i)
        (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1))) ∧
    (∀ i < 2 * N + 3,
      IntervalIntegrable
        (fun x : ℝ =>
          Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((x : ℂ) + Complex.I * (T : ℂ)))
        volume
        (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i)
        (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1))) := by
  constructor
  · intro i hi
    have hseg :
        ∀ x ∈ [[Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i,
            Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)]],
          ((x : ℂ) - Complex.I * (T : ℂ)) ∈
            Complex.finiteAbelPlanaPuncturedRectangle N T ρ :=
      (Complex.finiteAbelPlana_horizontalSubdivision_segment_subset_puncturedRectangle
        hT hρ hdeleted_geometry hi).2
    have hparam_cont :
        ContinuousOn
          (fun x : ℝ => ((x : ℂ) - Complex.I * (T : ℂ)))
          [[Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i,
            Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)]] :=
      (Complex.continuous_ofReal.sub continuous_const).continuousOn
    have hcont_segment :
        ContinuousOn
          (fun x : ℝ =>
            Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((x : ℂ) - Complex.I * (T : ℂ)))
          [[Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i,
            Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)]] :=
      ContinuousOn.comp'
        hcont
        hparam_cont
        hseg
    exact hcont_segment.intervalIntegrable
  · intro i hi
    have hseg :
        ∀ x ∈ [[Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i,
            Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)]],
          ((x : ℂ) + Complex.I * (T : ℂ)) ∈
            Complex.finiteAbelPlanaPuncturedRectangle N T ρ :=
      (Complex.finiteAbelPlana_horizontalSubdivision_segment_subset_puncturedRectangle
        hT hρ hdeleted_geometry hi).1
    have hparam_cont :
        ContinuousOn
          (fun x : ℝ => ((x : ℂ) + Complex.I * (T : ℂ)))
          [[Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i,
            Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)]] :=
      (Complex.continuous_ofReal.add continuous_const).continuousOn
    have hcont_segment :
        ContinuousOn
          (fun x : ℝ =>
            Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((x : ℂ) + Complex.I * (T : ℂ)))
          [[Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i,
            Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)]] :=
      ContinuousOn.comp'
        hcont
        hparam_cont
        hseg
    exact hcont_segment.intervalIntegrable

/-- Lower horizontal accounting for the finite-hole subdivision.

The full lower horizontal side is the sum of the safe vertical-strip lower
edges plus the endpoint and interior lower collars around the deleted disks. -/
theorem Complex.finiteAbelPlana_log_lowerHorizontalSide_eq_verticalStrips_add_capCollars
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogFiniteHeightLowerSide N w T =
      (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
        Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ) +
        (Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ +
          Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ +
            ∑ n in Finset.range N,
              Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ) := by
  let F : ℝ → ℂ := fun x : ℝ =>
    Complex.finiteAbelPlanaLogRectangleIntegrand w
      ((x : ℂ) - Complex.I * (T : ℂ))
  have hchain :
      (∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ), F x) =
        ∑ i in Finset.range (2 * N + 3),
          ∫ x : ℝ in
            (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i)..
              (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)),
            F x := by
    exact
      Complex.integral_eq_sum_adjacent_intervals_of_endpoint_chain
        F
        (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ)
        (2 * N + 3)
        0
        ((N + 1 : ℕ) : ℝ)
        (Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_start N ρ)
        (Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_end N ρ)
        (Complex.finiteAbelPlana_log_horizontalSubdivision_intervalIntegrable
          N T hT hρ hdeleted_geometry hcont).1
  have hreindex :
      (∑ i in Finset.range (2 * N + 3),
        ∫ x : ℝ in
          (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i)..
            (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)),
          F x) =
        (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
          Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ) +
          (Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ +
            Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ +
              ∑ n in Finset.range N,
                Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ) := by
    exact
      Complex.finiteAbelPlana_log_lowerHorizontalSubdivision_sum_eq_verticalStrips_add_capCollars
        N w T ρ
  calc
    Complex.finiteAbelPlanaLogFiniteHeightLowerSide N w T =
        ∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ), F x := by
      rfl
    _ =
        ∑ i in Finset.range (2 * N + 3),
          ∫ x : ℝ in
            (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i)..
              (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)),
            F x := hchain
    _ =
        (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
          Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ) +
          (Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ +
            Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ +
              ∑ n in Finset.range N,
                Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ) := hreindex

/-- Upper horizontal accounting for the finite-hole subdivision.

The full upper horizontal side is the sum of the safe vertical-strip upper
edges plus the endpoint and interior upper collars around the deleted disks. -/
theorem Complex.finiteAbelPlana_log_upperHorizontalSide_eq_verticalStrips_add_capCollars
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogFiniteHeightUpperSide N w T =
      (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
        Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ) +
        (Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
          Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
            ∑ n in Finset.range N,
              Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ) := by
  let F : ℝ → ℂ := fun x : ℝ =>
    Complex.finiteAbelPlanaLogRectangleIntegrand w
      ((x : ℂ) + Complex.I * (T : ℂ))
  have hchain :
      (∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ), F x) =
        ∑ i in Finset.range (2 * N + 3),
          ∫ x : ℝ in
            (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i)..
              (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)),
            F x := by
    exact
      Complex.integral_eq_sum_adjacent_intervals_of_endpoint_chain
        F
        (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ)
        (2 * N + 3)
        0
        ((N + 1 : ℕ) : ℝ)
        (Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_start N ρ)
        (Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_end N ρ)
        (Complex.finiteAbelPlana_log_horizontalSubdivision_intervalIntegrable
          N T hT hρ hdeleted_geometry hcont).2
  have hreindex :
      (∑ i in Finset.range (2 * N + 3),
        ∫ x : ℝ in
          (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i)..
            (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)),
          F x) =
        (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
          Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ) +
          (Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
            Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
              ∑ n in Finset.range N,
                Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ) := by
    exact
      Complex.finiteAbelPlana_log_upperHorizontalSubdivision_sum_eq_verticalStrips_add_capCollars
        N w T ρ
  calc
    Complex.finiteAbelPlanaLogFiniteHeightUpperSide N w T =
        ∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ), F x := by
      rfl
    _ =
        ∑ i in Finset.range (2 * N + 3),
          ∫ x : ℝ in
            (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i)..
              (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)),
            F x := hchain
    _ =
        (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,

          Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ) +
          (Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
            Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
              ∑ n in Finset.range N,
                Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ) := hreindex

end

end LFunctions
end Boundary

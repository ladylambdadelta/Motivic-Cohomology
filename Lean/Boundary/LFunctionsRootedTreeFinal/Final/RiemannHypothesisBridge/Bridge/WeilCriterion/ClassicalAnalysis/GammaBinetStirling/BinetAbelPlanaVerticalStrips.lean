import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaPuncturedRectangle

/-!
# Vertical strip decomposition for finite-height Abel-Plana

This file owns the finite-hole vertical strip decomposition, internal
vertical-edge cancellation, and rectangle Cauchy wrappers used by the
downstream collar layer.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Finite index set for the vertical safe strips between neighboring
deleted integer-pole disks in the finite Abel-Plana rectangle.

The strip with index `k` runs between the tangent lines
`Re z = k + ρ` and `Re z = k + 1 - ρ`; hence `k = 0, ..., N` gives the
`N + 1` pole-free vertical slabs between the deleted disks centered at
`0, ..., N + 1`. -/
def Complex.finiteAbelPlanaLogFiniteHoleVerticalStripIndexSet
    (N : ℕ) : Finset ℕ :=
  Finset.range (N + 1)

/-- Left real boundary of the `k`th finite-hole vertical strip. -/
def Complex.finiteAbelPlanaLogFiniteHoleVerticalStripLeft
    (ρ : ℝ)
    (k : ℕ) : ℝ :=
  (k : ℝ) + ρ

/-- Unfolding of the left real boundary of a finite-hole vertical strip. -/
theorem Complex.finiteAbelPlanaLogFiniteHoleVerticalStripLeft_unfold
    (ρ : ℝ)
    (k : ℕ) :
    Complex.finiteAbelPlanaLogFiniteHoleVerticalStripLeft ρ k =
      (k : ℝ) + ρ :=
  rfl

/-- Right real boundary of the `k`th finite-hole vertical strip. -/
def Complex.finiteAbelPlanaLogFiniteHoleVerticalStripRight
    (ρ : ℝ)
    (k : ℕ) : ℝ :=
  (k + 1 : ℝ) - ρ

/-- Unfolding of the right real boundary of a finite-hole vertical strip. -/
theorem Complex.finiteAbelPlanaLogFiniteHoleVerticalStripRight_unfold
    (ρ : ℝ)
    (k : ℕ) :
    Complex.finiteAbelPlanaLogFiniteHoleVerticalStripRight ρ k =
      (k + 1 : ℝ) - ρ :=
  rfl

/-- The `k`th vertical subrectangle between neighboring deleted pole disks. -/
def Complex.finiteAbelPlanaLogFiniteHoleVerticalStrip
    (N : ℕ)
    (T ρ : ℝ)
    (k : ℕ) : Set ℂ :=
  Set.Icc
      (Complex.finiteAbelPlanaLogFiniteHoleVerticalStripLeft ρ k)
      (Complex.finiteAbelPlanaLogFiniteHoleVerticalStripRight ρ k) ×ℂ
    Set.Icc (-T) T

/-- Union of all finite-hole vertical strips. -/
def Complex.finiteAbelPlanaLogFiniteHoleVerticalStripUnion
    (N : ℕ)
    (T ρ : ℝ) : Set ℂ :=
  ⋃ k ∈ Complex.finiteAbelPlanaLogFiniteHoleVerticalStripIndexSet N,
    Complex.finiteAbelPlanaLogFiniteHoleVerticalStrip N T ρ k

/-- Unfolding of the finite-hole vertical strip union. -/
theorem Complex.finiteAbelPlanaLogFiniteHoleVerticalStripUnion_unfold
    (N : ℕ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogFiniteHoleVerticalStripUnion N T ρ =
      ⋃ k ∈ Complex.finiteAbelPlanaLogFiniteHoleVerticalStripIndexSet N,
        Complex.finiteAbelPlanaLogFiniteHoleVerticalStrip N T ρ k :=
  rfl

/-- Concrete finite list of the vertical safe-strip subrectangles.

This is the object intended for the finite strip-by-strip Cauchy-Goursat pass:
each list entry is an honest closed rectangle between consecutive deleted pole
disks.  The cap regions adjacent to the deleted disks are owned separately by
the deleted-circle/semicircle API, not by this list. -/
def Complex.finiteAbelPlanaLogFiniteHoleVerticalStripList
    (N : ℕ)
    (T ρ : ℝ) : List (Set ℂ) :=
  (List.range (N + 1)).map
    (fun k => Complex.finiteAbelPlanaLogFiniteHoleVerticalStrip N T ρ k)

/-- Unfolding of the finite-hole vertical strip list. -/
theorem Complex.finiteAbelPlanaLogFiniteHoleVerticalStripList_unfold
    (N : ℕ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogFiniteHoleVerticalStripList N T ρ =
      (List.range (N + 1)).map
        (fun k => Complex.finiteAbelPlanaLogFiniteHoleVerticalStrip N T ρ k) :=
  rfl

/-- Membership in a finite-hole vertical strip is coordinatewise membership in
the corresponding real interval and in the rectangle height interval. -/
theorem Complex.mem_finiteAbelPlanaLogFiniteHoleVerticalStrip_iff
    {N k : ℕ}
    {T ρ : ℝ}
    {z : ℂ} :
    z ∈ Complex.finiteAbelPlanaLogFiniteHoleVerticalStrip N T ρ k ↔
      z.re ∈ Set.Icc
        (Complex.finiteAbelPlanaLogFiniteHoleVerticalStripLeft ρ k)
        (Complex.finiteAbelPlanaLogFiniteHoleVerticalStripRight ρ k) ∧
      z.im ∈ Set.Icc (-T) T := by
  exact Complex.mem_reProdIm

/-- Membership in the finite strip union is membership in one indexed strip. -/
theorem Complex.mem_finiteAbelPlanaLogFiniteHoleVerticalStripUnion_iff
    {N : ℕ}
    {T ρ : ℝ}
    {z : ℂ} :
    z ∈ Complex.finiteAbelPlanaLogFiniteHoleVerticalStripUnion N T ρ ↔
      ∃ k ∈ Complex.finiteAbelPlanaLogFiniteHoleVerticalStripIndexSet N,
        z ∈ Complex.finiteAbelPlanaLogFiniteHoleVerticalStrip N T ρ k := by
  constructor
  · intro hz
    have hz_unfold :
        z ∈ ⋃ k ∈ Complex.finiteAbelPlanaLogFiniteHoleVerticalStripIndexSet N,
          Complex.finiteAbelPlanaLogFiniteHoleVerticalStrip N T ρ k :=
      (Complex.finiteAbelPlanaLogFiniteHoleVerticalStripUnion_unfold N T ρ) ▸
        hz
    match Set.mem_iUnion.1 hz_unfold with
    | Exists.intro k hkz =>
        match Set.mem_iUnion.1 hkz with
        | Exists.intro hk hzstrip =>
            exact Exists.intro k (And.intro hk hzstrip)
  · intro hz
    match hz with
    | Exists.intro k hkdata =>
        have hk : k ∈ Complex.finiteAbelPlanaLogFiniteHoleVerticalStripIndexSet N :=
          hkdata.1
        have hzstrip : z ∈ Complex.finiteAbelPlanaLogFiniteHoleVerticalStrip N T ρ k :=
          hkdata.2
        have hz_unfold :
            z ∈ ⋃ k ∈ Complex.finiteAbelPlanaLogFiniteHoleVerticalStripIndexSet N,
              Complex.finiteAbelPlanaLogFiniteHoleVerticalStrip N T ρ k :=
          Set.mem_iUnion.2
            (Exists.intro k
              (Set.mem_iUnion.2
                (Exists.intro hk hzstrip)))
        exact
          (Complex.finiteAbelPlanaLogFiniteHoleVerticalStripUnion_unfold N T ρ).symm ▸
            hz_unfold

/-- The finite strip list has exactly the strip count `N + 1`. -/
theorem Complex.length_finiteAbelPlanaLogFiniteHoleVerticalStripList
    (N : ℕ)
    (T ρ : ℝ) :
    (Complex.finiteAbelPlanaLogFiniteHoleVerticalStripList N T ρ).length =
      N + 1 := by
  exact
    Eq.trans
      (congrArg List.length
        (Complex.finiteAbelPlanaLogFiniteHoleVerticalStripList_unfold N T ρ))
      (Eq.trans
        (List.length_map
          (List.range (N + 1))
          (fun k => Complex.finiteAbelPlanaLogFiniteHoleVerticalStrip N T ρ k))
        (List.length_range (N + 1)))

/-- Every indexed vertical strip appears in the concrete finite strip list. -/
theorem Complex.finiteAbelPlanaLogFiniteHoleVerticalStrip_mem_list
    {N k : ℕ}
    {T ρ : ℝ}
    (hk : k ∈ Complex.finiteAbelPlanaLogFiniteHoleVerticalStripIndexSet N) :
    Complex.finiteAbelPlanaLogFiniteHoleVerticalStrip N T ρ k ∈
      Complex.finiteAbelPlanaLogFiniteHoleVerticalStripList N T ρ := by
  exact
    (Complex.finiteAbelPlanaLogFiniteHoleVerticalStripList_unfold N T ρ).symm ▸
      List.mem_map.2
        ⟨k, by exact List.mem_range.mpr (Finset.mem_range.mp hk), rfl⟩

/-- A strip index is bounded by the last strip index. -/
theorem Complex.finiteAbelPlanaLogFiniteHoleVerticalStripIndex_le
    {N k : ℕ}
    (hk : k ∈ Complex.finiteAbelPlanaLogFiniteHoleVerticalStripIndexSet N) :
    k ≤ N := by
  have hklt : k < N + 1 := by
    exact Finset.mem_range.mp hk
  exact Nat.lt_succ_iff.mp hklt

/-- The quarter-radius bound is stronger than the half-radius bound. -/
theorem real_one_fourth_le_one_half :
    (1 : ℝ) / 4 ≤ (1 : ℝ) / 2 := by
  have htwo_pos : (0 : ℝ) < 2 := by
    exact zero_lt_two
  have htwo_le_four_nat : (2 : ℕ) ≤ 4 := by
    exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le 2))
  have htwo_le_four : (2 : ℝ) ≤ 4 := by
    exact Nat.cast_le.mpr htwo_le_four_nat
  exact one_div_le_one_div_of_le htwo_pos htwo_le_four

/-- If `ρ ≤ 1/2`, then deleting `ρ` from both sides of a unit interval
leaves a nonempty middle interval. -/
theorem real_add_radius_le_add_one_sub_radius
    (k : ℝ)
    {ρ : ℝ}
    (hρhalf : ρ ≤ (1 : ℝ) / 2) :
    k + ρ ≤ k + 1 - ρ := by
  have htwoρ_le_one : ρ + ρ ≤ (1 : ℝ) := by
    calc
      ρ + ρ ≤ (1 : ℝ) / 2 + (1 : ℝ) / 2 := by
        exact add_le_add hρhalf hρhalf
      _ = 1 := add_halves 1
  have hρ_le_one_sub : ρ ≤ (1 : ℝ) - ρ := by
    exact le_sub_iff_add_le.mpr htwoρ_le_one
  calc
    k + ρ ≤ k + ((1 : ℝ) - ρ) := by
      exact add_le_add_left hρ_le_one_sub k
    _ = k + 1 - ρ := by
      exact add_sub k 1 ρ

/-- The strip interval is ordered when the deletion radius is below `1/4`. -/
theorem Complex.finiteAbelPlanaLogFiniteHoleVerticalStrip_left_le_right
    {ρ : ℝ}
    (hρquarter : ρ < (1 : ℝ) / 4)
    (k : ℕ) :
      Complex.finiteAbelPlanaLogFiniteHoleVerticalStripLeft ρ k ≤
      Complex.finiteAbelPlanaLogFiniteHoleVerticalStripRight ρ k := by
  have hρhalf : ρ ≤ (1 : ℝ) / 2 := by
    exact (le_of_lt hρquarter).trans real_one_fourth_le_one_half
  exact
    (Complex.finiteAbelPlanaLogFiniteHoleVerticalStripLeft_unfold ρ k).symm ▸
      ((Complex.finiteAbelPlanaLogFiniteHoleVerticalStripRight_unfold ρ k).symm ▸
        real_add_radius_le_add_one_sub_radius k hρhalf)

/-- A finite-hole vertical strip lies in the closed Abel-Plana rectangle. -/
theorem Complex.finiteAbelPlanaLogFiniteHoleVerticalStrip_subset_closedRectangle
    {N k : ℕ}
    {T ρ : ℝ}
    (hk : k ∈ Complex.finiteAbelPlanaLogFiniteHoleVerticalStripIndexSet N)
    (hρnonneg : 0 ≤ ρ)
    (hρquarter : ρ < (1 : ℝ) / 4) :
    Complex.finiteAbelPlanaLogFiniteHoleVerticalStrip N T ρ k ⊆
      Complex.finiteAbelPlanaClosedRectangle N T := by
  intro z hz
  have hzdata :
      z.re ∈ Set.Icc
        (Complex.finiteAbelPlanaLogFiniteHoleVerticalStripLeft ρ k)
        (Complex.finiteAbelPlanaLogFiniteHoleVerticalStripRight ρ k) ∧
      z.im ∈ Set.Icc (-T) T :=
    Complex.mem_finiteAbelPlanaLogFiniteHoleVerticalStrip_iff.mp hz
  have hk_le : k ≤ N :=
    Complex.finiteAbelPlanaLogFiniteHoleVerticalStripIndex_le hk
  have hzre_nonneg : 0 ≤ z.re := by
    have hleft : (k : ℝ) + ρ ≤ z.re := hzdata.1.1
    have hk_nonneg : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hleft_nonneg : 0 ≤ (k : ℝ) + ρ := by
      exact add_nonneg hk_nonneg hρnonneg
    exact hleft_nonneg.trans hleft
  have hzre_le : z.re ≤ (N + 1 : ℝ) := by
    have hright : z.re ≤ (k + 1 : ℝ) - ρ := hzdata.1.2
    have hk_right : (k + 1 : ℝ) ≤ (N + 1 : ℝ) := by
      exact add_le_add_right (Nat.cast_le.mpr hk_le : (k : ℝ) ≤ (N : ℝ)) 1
    have hright_le_k_succ : (k + 1 : ℝ) - ρ ≤ (k + 1 : ℝ) := by
      exact sub_le_self (k + 1 : ℝ) hρnonneg
    exact hright.trans (hright_le_k_succ.trans hk_right)
  have hright_nonneg : (0 : ℝ) ≤ (N + 1 : ℝ) := by
    exact add_nonneg (Nat.cast_nonneg N) zero_le_one
  have hzre_Icc : z.re ∈ Set.Icc (0 : ℝ) (N + 1 : ℝ) :=
    ⟨hzre_nonneg, hzre_le⟩
  exact Complex.mem_reProdIm.mpr ⟨hzre_Icc, hzdata.2⟩

/-- Every finite-hole vertical strip in the index set is one of the pieces of
the closed Abel-Plana rectangle. -/
theorem Complex.finiteAbelPlanaLogFiniteHoleVerticalStripUnion_subset_closedRectangle
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hρnonneg : 0 ≤ ρ)
    (hρquarter : ρ < (1 : ℝ) / 4) :
    Complex.finiteAbelPlanaLogFiniteHoleVerticalStripUnion N T ρ ⊆
      Complex.finiteAbelPlanaClosedRectangle N T := by
  intro z hz
  match Complex.mem_finiteAbelPlanaLogFiniteHoleVerticalStripUnion_iff.mp hz with
  | Exists.intro k hkdata =>
      exact
        Complex.finiteAbelPlanaLogFiniteHoleVerticalStrip_subset_closedRectangle
          hkdata.1 hρnonneg hρquarter hkdata.2

/-- A point in one of the vertical safe strips is at real distance at least
`ρ` from every listed integer pole.  This is the set-theoretic reason those
strips are the pole-free Cauchy-Goursat pieces. -/
theorem Complex.finiteAbelPlanaLogFiniteHoleVerticalStrip_not_mem_deletedDisk
    {N k n : ℕ}
    {T ρ : ℝ}
    (hk : k ∈ Complex.finiteAbelPlanaLogFiniteHoleVerticalStripIndexSet N)
    (hn : n ∈ Finset.range (N + 2))
    (hρnonneg : 0 ≤ ρ)
    (hρquarter : ρ < (1 : ℝ) / 4)
    {z : ℂ}
    (hz : z ∈ Complex.finiteAbelPlanaLogFiniteHoleVerticalStrip N T ρ k) :
    z ∉ Metric.ball (n : ℂ) ρ := by
  intro hzball
  have hzdata :
      z.re ∈ Set.Icc
        (Complex.finiteAbelPlanaLogFiniteHoleVerticalStripLeft ρ k)
        (Complex.finiteAbelPlanaLogFiniteHoleVerticalStripRight ρ k) ∧
      z.im ∈ Set.Icc (-T) T :=
    Complex.mem_finiteAbelPlanaLogFiniteHoleVerticalStrip_iff.mp hz
  have hdist_lt : ‖z - (n : ℂ)‖ < ρ := by
    exact (dist_eq_norm z (n : ℂ)) ▸ Metric.mem_ball.mp hzball
  have hre_norm :
      |(z - (n : ℂ)).re| ≤ ‖z - (n : ℂ)‖ := by
    calc
      |(z - (n : ℂ)).re| ≤ Complex.abs (z - (n : ℂ)) :=
        Complex.abs_re_le_abs (z - (n : ℂ))
      _ = ‖z - (n : ℂ)‖ :=
        (Complex.norm_eq_abs (z - (n : ℂ))).symm
  have hsub_re :
      (z - (n : ℂ)).re = z.re - (n : ℝ) := by
    calc
      (z - (n : ℂ)).re = z.re - ((n : ℂ).re) :=
        Complex.sub_re z (n : ℂ)
      _ = z.re - (n : ℝ) := by
        exact congrArg (fun r : ℝ => z.re - r)
          (Complex.ofReal_re (n : ℝ))
  match le_or_gt n k with
  | Or.inl hnk =>
    have hn_le_k_real : (n : ℝ) ≤ (k : ℝ) := by
      exact Nat.cast_le.mpr hnk
    have hleft : (k : ℝ) + ρ ≤ z.re := hzdata.1.1
    have hre_ge : ρ ≤ (z - (n : ℂ)).re := by
      have hn_add_ρ_le_z : (n : ℝ) + ρ ≤ z.re := by
        exact (add_le_add_right hn_le_k_real ρ).trans hleft
      have hρ_le_sub : ρ ≤ z.re - (n : ℝ) := by
        exact le_sub_iff_add_le.mpr ((add_comm ρ (n : ℝ)) ▸ hn_add_ρ_le_z)
      exact hsub_re.symm ▸ hρ_le_sub
    have hρ_le_abs : ρ ≤ |(z - (n : ℂ)).re| :=
      hre_ge.trans (le_abs_self _)
    exact not_lt_of_ge (hρ_le_abs.trans hre_norm) hdist_lt
  | Or.inr hk_lt_n =>
    have hk_succ_le_n : k + 1 ≤ n := Nat.succ_le_iff.mpr hk_lt_n
    have hk_succ_le_n_real : (k + 1 : ℝ) ≤ (n : ℝ) := by
      have hk_succ_cast_le : ((k + 1 : ℕ) : ℝ) ≤ (n : ℝ) :=
        Nat.cast_le.mpr hk_succ_le_n
      exact (Nat.cast_add_one (R := ℝ) k) ▸ hk_succ_cast_le
    have hright : z.re ≤ (k + 1 : ℝ) - ρ := hzdata.1.2
    have hre_le_neg : (z - (n : ℂ)).re ≤ -ρ := by
      have hz_le_n_sub_ρ : z.re ≤ (n : ℝ) - ρ := by
        exact hright.trans (sub_le_sub_right hk_succ_le_n_real ρ)
      have hz_sub_n_le_negρ : z.re - (n : ℝ) ≤ -ρ := by
        have hz_le_negρ_add_n : z.re ≤ -ρ + (n : ℝ) := by
          calc
            z.re ≤ (n : ℝ) - ρ := hz_le_n_sub_ρ
            _ = -ρ + (n : ℝ) := by
              calc
                (n : ℝ) - ρ = (n : ℝ) + -ρ :=
                  sub_eq_add_neg (n : ℝ) ρ
                _ = -ρ + (n : ℝ) :=
                  add_comm (n : ℝ) (-ρ)
        exact sub_le_iff_le_add.mpr hz_le_negρ_add_n
      exact hsub_re.symm ▸ hz_sub_n_le_negρ
    have hρ_le_abs : ρ ≤ |(z - (n : ℂ)).re| := by
      have hneg : ρ ≤ -((z - (n : ℂ)).re) := by
        have h := neg_le_neg hre_le_neg
        calc
          ρ = -(-ρ) := (neg_neg ρ).symm
          _ ≤ -((z - (n : ℂ)).re) := h
      exact hneg.trans (neg_le_abs _)
    exact not_lt_of_ge (hρ_le_abs.trans hre_norm) hdist_lt

/-- Each finite-hole vertical strip is contained in the punctured Abel-Plana
rectangle. -/
theorem Complex.finiteAbelPlanaLogFiniteHoleVerticalStrip_subset_puncturedRectangle
    {N k : ℕ}
    {T ρ : ℝ}
    (hk : k ∈ Complex.finiteAbelPlanaLogFiniteHoleVerticalStripIndexSet N)
    (hρnonneg : 0 ≤ ρ)
    (hρquarter : ρ < (1 : ℝ) / 4) :
    Complex.finiteAbelPlanaLogFiniteHoleVerticalStrip N T ρ k ⊆
      Complex.finiteAbelPlanaPuncturedRectangle N T ρ := by
  intro z hz
  exact
    Complex.mem_finiteAbelPlanaPuncturedRectangle_iff.mpr
      ⟨Complex.finiteAbelPlanaLogFiniteHoleVerticalStrip_subset_closedRectangle
          hk hρnonneg hρquarter hz,
        fun n hn =>
          Complex.finiteAbelPlanaLogFiniteHoleVerticalStrip_not_mem_deletedDisk
            hk hn hρnonneg hρquarter hz⟩

/-- The union of all finite-hole vertical strips lies in the punctured
Abel-Plana rectangle. -/
theorem Complex.finiteAbelPlanaLogFiniteHoleVerticalStripUnion_subset_puncturedRectangle
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hρnonneg : 0 ≤ ρ)
    (hρquarter : ρ < (1 : ℝ) / 4) :
    Complex.finiteAbelPlanaLogFiniteHoleVerticalStripUnion N T ρ ⊆
      Complex.finiteAbelPlanaPuncturedRectangle N T ρ := by
  intro z hz
  match Complex.mem_finiteAbelPlanaLogFiniteHoleVerticalStripUnion_iff.mp hz with
  | Exists.intro k hkdata =>
      exact
        Complex.finiteAbelPlanaLogFiniteHoleVerticalStrip_subset_puncturedRectangle
          hkdata.1 hρnonneg hρquarter hkdata.2

/-- A vertical subdivision edge in the finite Abel-Plana rectangle.

The edge is oriented upward, matching the side convention used by
`finiteAbelPlanaLogFiniteHeightRectangleSideExpression`. -/
noncomputable def Complex.finiteAbelPlanaLogVerticalSubdivisionEdge
    (w : ℂ)
    (x y₀ y₁ : ℝ) : ℂ :=
  ∫ y : ℝ in y₀..y₁,
    Complex.finiteAbelPlanaLogRectangleIntegrand w
      ((x : ℂ) + Complex.I * (y : ℂ))

/-- The same vertical subdivision edge with the opposite interval orientation. -/
noncomputable def Complex.finiteAbelPlanaLogVerticalSubdivisionEdgeReverse
    (w : ℂ)
    (x y₀ y₁ : ℝ) : ℂ :=
  ∫ y : ℝ in y₁..y₀,
    Complex.finiteAbelPlanaLogRectangleIntegrand w
      ((x : ℂ) + Complex.I * (y : ℂ))

/-- The right-side contribution of a vertical subdivision edge. -/
noncomputable def Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution
    (w : ℂ)
    (x y₀ y₁ : ℝ) : ℂ :=
  Complex.I *
    Complex.finiteAbelPlanaLogVerticalSubdivisionEdge w x y₀ y₁

/-- Unfolding of the right-side contribution of a vertical subdivision edge. -/
theorem Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution_unfold
    (w : ℂ)
    (x y₀ y₁ : ℝ) :
    Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution w x y₀ y₁ =
      Complex.I *
        Complex.finiteAbelPlanaLogVerticalSubdivisionEdge w x y₀ y₁ :=
  rfl

/-- The left-side contribution of a vertical subdivision edge. -/
noncomputable def Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution
    (w : ℂ)
    (x y₀ y₁ : ℝ) : ℂ :=
  -Complex.I *
    Complex.finiteAbelPlanaLogVerticalSubdivisionEdge w x y₀ y₁

/-- Unfolding of the left-side contribution of a vertical subdivision edge. -/
theorem Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution_unfold
    (w : ℂ)
    (x y₀ y₁ : ℝ) :
    Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution w x y₀ y₁ =
      -Complex.I *
        Complex.finiteAbelPlanaLogVerticalSubdivisionEdge w x y₀ y₁ :=
  rfl

/-- Unfolding of the upward vertical subdivision edge. -/
theorem Complex.finiteAbelPlana_log_verticalSubdivisionEdge_unfold
    (w : ℂ)
    (x y₀ y₁ : ℝ) :
    Complex.finiteAbelPlanaLogVerticalSubdivisionEdge w x y₀ y₁ =
      ∫ y : ℝ in y₀..y₁,
        Complex.finiteAbelPlanaLogRectangleIntegrand w
          ((x : ℂ) + Complex.I * (y : ℂ)) := by
  rfl

/-- Reversing the interval orientation negates a vertical subdivision edge. -/
theorem Complex.finiteAbelPlana_log_verticalSubdivisionEdge_reverse_eq_neg
    (w : ℂ)
    (x y₀ y₁ : ℝ) :
    Complex.finiteAbelPlanaLogVerticalSubdivisionEdgeReverse w x y₀ y₁ =
      -Complex.finiteAbelPlanaLogVerticalSubdivisionEdge w x y₀ y₁ := by
  exact
    intervalIntegral.integral_symm
      (f := fun y : ℝ =>
        Complex.finiteAbelPlanaLogRectangleIntegrand w
          ((x : ℂ) + Complex.I * (y : ℂ)))
      y₀ y₁

/-- The right contribution of an internal vertical edge cancels the adjacent
left contribution with the same parametrization. -/
theorem Complex.finiteAbelPlana_log_internalVerticalEdge_right_add_left_cancel
    (w : ℂ)
    (x y₀ y₁ : ℝ) :
    Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution w x y₀ y₁ +
      Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution w x y₀ y₁ =
        0 := by
  calc
    Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution w x y₀ y₁ +
        Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution w x y₀ y₁
        =
      Complex.I * Complex.finiteAbelPlanaLogVerticalSubdivisionEdge w x y₀ y₁ +
        (-Complex.I * Complex.finiteAbelPlanaLogVerticalSubdivisionEdge w x y₀ y₁) := by
      exact congrArg₂ HAdd.hAdd
        (Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution_unfold
          w x y₀ y₁)
        (Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution_unfold
          w x y₀ y₁)
    _ =
      Complex.I * Complex.finiteAbelPlanaLogVerticalSubdivisionEdge w x y₀ y₁ +
        -(Complex.I * Complex.finiteAbelPlanaLogVerticalSubdivisionEdge w x y₀ y₁) := by
      exact congrArg
        (fun z : ℂ =>
          Complex.I * Complex.finiteAbelPlanaLogVerticalSubdivisionEdge w x y₀ y₁ +
            z)
        (neg_mul Complex.I
          (Complex.finiteAbelPlanaLogVerticalSubdivisionEdge w x y₀ y₁))
    _ = 0 :=
      add_neg_cancel
        (Complex.I * Complex.finiteAbelPlanaLogVerticalSubdivisionEdge w x y₀ y₁)

/-- The left contribution of an internal vertical edge cancels the adjacent
right contribution with the same parametrization. -/
theorem Complex.finiteAbelPlana_log_internalVerticalEdge_left_add_right_cancel
    (w : ℂ)
    (x y₀ y₁ : ℝ) :
    Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution w x y₀ y₁ +
      Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution w x y₀ y₁ =
        0 := by
  calc
    Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution w x y₀ y₁ +
        Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution w x y₀ y₁
        =
      (-Complex.I * Complex.finiteAbelPlanaLogVerticalSubdivisionEdge w x y₀ y₁) +
        Complex.I * Complex.finiteAbelPlanaLogVerticalSubdivisionEdge w x y₀ y₁
        := by
      exact congrArg₂ HAdd.hAdd
        (Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution_unfold
          w x y₀ y₁)
        (Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution_unfold
          w x y₀ y₁)
    _ =
      -(Complex.I * Complex.finiteAbelPlanaLogVerticalSubdivisionEdge w x y₀ y₁) +
        Complex.I * Complex.finiteAbelPlanaLogVerticalSubdivisionEdge w x y₀ y₁ := by
      exact congrArg
        (fun z : ℂ =>
          z + Complex.I *
            Complex.finiteAbelPlanaLogVerticalSubdivisionEdge w x y₀ y₁)
        (neg_mul Complex.I
          (Complex.finiteAbelPlanaLogVerticalSubdivisionEdge w x y₀ y₁))
    _ = 0 :=
      neg_add_cancel
        (Complex.I * Complex.finiteAbelPlanaLogVerticalSubdivisionEdge w x y₀ y₁)

/-- A finite list of paired internal vertical edges cancels term by term. -/
theorem Complex.finiteAbelPlana_log_internalVerticalEdges_sum_cancel
    (w : ℂ)
    (x : ℕ → ℝ)
    (m : ℕ)
    (y₀ y₁ : ℝ) :
    (∑ n in Finset.range m,
        (Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution
            w (x n) y₀ y₁ +
          Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution
            w (x n) y₀ y₁)) = 0 := by
  exact
    Finset.sum_eq_zero
      (fun n _hn =>
        Complex.finiteAbelPlana_log_internalVerticalEdge_right_add_left_cancel
          w (x n) y₀ y₁)

/-- The lower horizontal edge of a vertical strip. -/
noncomputable def Complex.finiteAbelPlanaLogVerticalStripLowerEdge
    (w : ℂ)
    (x₀ x₁ y₀ : ℝ) : ℂ :=
  ∫ x : ℝ in x₀..x₁,
    Complex.finiteAbelPlanaLogRectangleIntegrand w
      ((x : ℂ) + Complex.I * (y₀ : ℂ))

/-- The upper horizontal edge of a vertical strip, with the upward rectangle
orientation still applied later by subtraction. -/
noncomputable def Complex.finiteAbelPlanaLogVerticalStripUpperEdge
    (w : ℂ)
    (x₀ x₁ y₁ : ℝ) : ℂ :=
  ∫ x : ℝ in x₀..x₁,
    Complex.finiteAbelPlanaLogRectangleIntegrand w
      ((x : ℂ) + Complex.I * (y₁ : ℂ))

/-- Oriented boundary contribution of a vertical strip in the rectangle side
convention `bottom - top + I * right - I * left`. -/
noncomputable def Complex.finiteAbelPlanaLogVerticalStripSideExpression
    (w : ℂ)
    (x₀ x₁ y₀ y₁ : ℝ) : ℂ :=
  Complex.finiteAbelPlanaLogVerticalStripLowerEdge w x₀ x₁ y₀ -
    Complex.finiteAbelPlanaLogVerticalStripUpperEdge w x₀ x₁ y₁ +
      Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution w x₁ y₀ y₁ +
        Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution w x₀ y₀ y₁

/-- Unfolding of the oriented vertical-strip boundary expression. -/
theorem Complex.finiteAbelPlana_log_verticalStripSideExpression_unfold
    (w : ℂ)
    (x₀ x₁ y₀ y₁ : ℝ) :
    Complex.finiteAbelPlanaLogVerticalStripSideExpression w x₀ x₁ y₀ y₁ =
      Complex.finiteAbelPlanaLogVerticalStripLowerEdge w x₀ x₁ y₀ -
        Complex.finiteAbelPlanaLogVerticalStripUpperEdge w x₀ x₁ y₁ +
          Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution w x₁ y₀ y₁ +
            Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution w x₀ y₀ y₁ := by
  rfl

/-- Core order normalization for a single vertical strip boundary. -/
theorem Complex.finiteAbelPlana_log_singleVerticalStripBoundary_eq_horizontal_add_outer_core
    (w : ℂ)
    (x₀ x₁ y₀ y₁ : ℝ) :
    Complex.finiteAbelPlanaLogVerticalStripSideExpression w x₀ x₁ y₀ y₁ =
      (Complex.finiteAbelPlanaLogVerticalStripLowerEdge w x₀ x₁ y₀ -
        Complex.finiteAbelPlanaLogVerticalStripUpperEdge w x₀ x₁ y₁) +
        (Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution w x₀ y₀ y₁ +
          Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution w x₁ y₀ y₁) := by
  calc
    Complex.finiteAbelPlanaLogVerticalStripSideExpression w x₀ x₁ y₀ y₁ =
      Complex.finiteAbelPlanaLogVerticalStripLowerEdge w x₀ x₁ y₀ -
        Complex.finiteAbelPlanaLogVerticalStripUpperEdge w x₀ x₁ y₁ +
          Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution w x₁ y₀ y₁ +
            Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution w x₀ y₀ y₁ :=
      Complex.finiteAbelPlana_log_verticalStripSideExpression_unfold
        w x₀ x₁ y₀ y₁
    _ =
      (Complex.finiteAbelPlanaLogVerticalStripLowerEdge w x₀ x₁ y₀ -
        Complex.finiteAbelPlanaLogVerticalStripUpperEdge w x₀ x₁ y₁) +
        (Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution w x₁ y₀ y₁ +
          Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution w x₀ y₀ y₁) :=
      add_assoc
        (Complex.finiteAbelPlanaLogVerticalStripLowerEdge w x₀ x₁ y₀ -
          Complex.finiteAbelPlanaLogVerticalStripUpperEdge w x₀ x₁ y₁)
        (Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution w x₁ y₀ y₁)
        (Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution w x₀ y₀ y₁)
    _ =
      (Complex.finiteAbelPlanaLogVerticalStripLowerEdge w x₀ x₁ y₀ -
        Complex.finiteAbelPlanaLogVerticalStripUpperEdge w x₀ x₁ y₁) +
        (Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution w x₀ y₀ y₁ +
          Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution w x₁ y₀ y₁) := by
      exact
        congrArg
          (fun z =>
            (Complex.finiteAbelPlanaLogVerticalStripLowerEdge w x₀ x₁ y₀ -
              Complex.finiteAbelPlanaLogVerticalStripUpperEdge w x₀ x₁ y₁) + z)
          (add_comm
            (Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution w x₁ y₀ y₁)
            (Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution w x₀ y₀ y₁))

/-- Additive algebra for cancelling the shared internal edge of two adjacent
vertical strips. -/
theorem adjacent_vertical_strip_boundary_cancel_algebra
    {H₀ H₁ L₀ R₀ L₁ R₁ : ℂ}
    (hcancel : R₀ + L₁ = 0) :
    (H₀ + (L₀ + R₀)) + (H₁ + (L₁ + R₁)) =
      H₀ + H₁ + R₁ + L₀ := by
  calc
    (H₀ + (L₀ + R₀)) + (H₁ + (L₁ + R₁))
        = (H₀ + H₁) + ((L₀ + R₀) + (L₁ + R₁)) := by
      exact add_add_add_comm H₀ (L₀ + R₀) H₁ (L₁ + R₁)
    _ = (H₀ + H₁) + ((L₀ + R₀) + (R₁ + L₁)) := by
      exact
        congrArg
          (fun z => (H₀ + H₁) + ((L₀ + R₀) + z))
          (add_comm L₁ R₁)
    _ = (H₀ + H₁) + ((L₀ + R₁) + (R₀ + L₁)) := by
      exact
        congrArg (fun z => (H₀ + H₁) + z)
          (add_add_add_comm L₀ R₀ R₁ L₁)
    _ = (H₀ + H₁) + ((L₀ + R₁) + 0) := by
      exact
        congrArg
          (fun z => (H₀ + H₁) + ((L₀ + R₁) + z))
          hcancel
    _ = (H₀ + H₁) + (L₀ + R₁) := by
      exact congrArg (fun z : ℂ => (H₀ + H₁) + z)
        (add_zero (L₀ + R₁))
    _ = (H₀ + H₁) + (R₁ + L₀) := by
      exact congrArg (fun z => (H₀ + H₁) + z) (add_comm L₀ R₁)
    _ = H₀ + H₁ + R₁ + L₀ := by
      exact (add_assoc (H₀ + H₁) R₁ L₀).symm

/-- Two adjacent vertical strips cancel their shared internal vertical edge.

The result deliberately leaves the two lower pieces and two upper pieces
unmerged; horizontal concatenation is a separate interval-integral theorem.
This lemma owns only the internal vertical-edge cancellation. -/
theorem Complex.finiteAbelPlana_log_adjacentVerticalStripBoundaries_cancel_internalEdge
    (w : ℂ)
    (x₀ x₁ x₂ y₀ y₁ : ℝ) :
    Complex.finiteAbelPlanaLogVerticalStripSideExpression w x₀ x₁ y₀ y₁ +
        Complex.finiteAbelPlanaLogVerticalStripSideExpression w x₁ x₂ y₀ y₁ =
      (Complex.finiteAbelPlanaLogVerticalStripLowerEdge w x₀ x₁ y₀ -
        Complex.finiteAbelPlanaLogVerticalStripUpperEdge w x₀ x₁ y₁) +
          (Complex.finiteAbelPlanaLogVerticalStripLowerEdge w x₁ x₂ y₀ -
            Complex.finiteAbelPlanaLogVerticalStripUpperEdge w x₁ x₂ y₁) +
              Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution w x₂ y₀ y₁ +
                Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution w x₀ y₀ y₁ := by
  calc
    Complex.finiteAbelPlanaLogVerticalStripSideExpression w x₀ x₁ y₀ y₁ +
        Complex.finiteAbelPlanaLogVerticalStripSideExpression w x₁ x₂ y₀ y₁
        =
      ((Complex.finiteAbelPlanaLogVerticalStripLowerEdge w x₀ x₁ y₀ -
        Complex.finiteAbelPlanaLogVerticalStripUpperEdge w x₀ x₁ y₁) +
        (Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution w x₀ y₀ y₁ +
          Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution w x₁ y₀ y₁)) +
      ((Complex.finiteAbelPlanaLogVerticalStripLowerEdge w x₁ x₂ y₀ -
        Complex.finiteAbelPlanaLogVerticalStripUpperEdge w x₁ x₂ y₁) +
        (Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution w x₁ y₀ y₁ +
          Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution w x₂ y₀ y₁)) := by
      exact congrArg₂ HAdd.hAdd
        (Complex.finiteAbelPlana_log_singleVerticalStripBoundary_eq_horizontal_add_outer_core
          w x₀ x₁ y₀ y₁)
        (Complex.finiteAbelPlana_log_singleVerticalStripBoundary_eq_horizontal_add_outer_core
          w x₁ x₂ y₀ y₁)
    _ =
      (Complex.finiteAbelPlanaLogVerticalStripLowerEdge w x₀ x₁ y₀ -
        Complex.finiteAbelPlanaLogVerticalStripUpperEdge w x₀ x₁ y₁) +
          (Complex.finiteAbelPlanaLogVerticalStripLowerEdge w x₁ x₂ y₀ -
            Complex.finiteAbelPlanaLogVerticalStripUpperEdge w x₁ x₂ y₁) +
              Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution w x₂ y₀ y₁ +
                Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution w x₀ y₀ y₁ := by
      exact adjacent_vertical_strip_boundary_cancel_algebra
        (H₀ := Complex.finiteAbelPlanaLogVerticalStripLowerEdge w x₀ x₁ y₀ -
          Complex.finiteAbelPlanaLogVerticalStripUpperEdge w x₀ x₁ y₁)
        (H₁ := Complex.finiteAbelPlanaLogVerticalStripLowerEdge w x₁ x₂ y₀ -
          Complex.finiteAbelPlanaLogVerticalStripUpperEdge w x₁ x₂ y₁)
        (L₀ := Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution w x₀ y₀ y₁)
        (R₀ := Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution w x₁ y₀ y₁)
        (L₁ := Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution w x₁ y₀ y₁)
        (R₁ := Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution w x₂ y₀ y₁)
        (Complex.finiteAbelPlana_log_internalVerticalEdge_right_add_left_cancel
          w x₁ y₀ y₁)

/-- Boundary sum of a chain of vertical strips.  The nodes `x n` are the
successive vertical subdivision lines. -/
noncomputable def Complex.finiteAbelPlanaLogVerticalStripChainBoundarySum
    (w : ℂ)
    (x : ℕ → ℝ)
    (m : ℕ)
    (y₀ y₁ : ℝ) : ℂ :=
  ∑ n in Finset.range (m + 1),
    Complex.finiteAbelPlanaLogVerticalStripSideExpression
      w (x n) (x (n + 1)) y₀ y₁

/-- Unfolding of the boundary sum of a chain of vertical strips. -/
theorem Complex.finiteAbelPlana_log_verticalStripChainBoundarySum_unfold
    (w : ℂ)
    (x : ℕ → ℝ)
    (m : ℕ)
    (y₀ y₁ : ℝ) :
    Complex.finiteAbelPlanaLogVerticalStripChainBoundarySum w x m y₀ y₁ =
      ∑ n in Finset.range (m + 1),
        Complex.finiteAbelPlanaLogVerticalStripSideExpression
          w (x n) (x (n + 1)) y₀ y₁ :=
  rfl

/-- The horizontal part of the boundary sum of a chain of vertical strips. -/
noncomputable def Complex.finiteAbelPlanaLogVerticalStripChainHorizontalBoundary
    (w : ℂ)
    (x : ℕ → ℝ)
    (m : ℕ)
    (y₀ y₁ : ℝ) : ℂ :=
  (∑ n in Finset.range (m + 1),
      Complex.finiteAbelPlanaLogVerticalStripLowerEdge
        w (x n) (x (n + 1)) y₀) -
    ∑ n in Finset.range (m + 1),
      Complex.finiteAbelPlanaLogVerticalStripUpperEdge
        w (x n) (x (n + 1)) y₁

/-- Unfolding of the horizontal boundary of a vertical-strip chain. -/
theorem Complex.finiteAbelPlana_log_verticalStripChainHorizontalBoundary_unfold
    (w : ℂ)
    (x : ℕ → ℝ)
    (m : ℕ)
    (y₀ y₁ : ℝ) :
    Complex.finiteAbelPlanaLogVerticalStripChainHorizontalBoundary
        w x m y₀ y₁ =
      (∑ n in Finset.range (m + 1),
          Complex.finiteAbelPlanaLogVerticalStripLowerEdge
            w (x n) (x (n + 1)) y₀) -
        ∑ n in Finset.range (m + 1),
          Complex.finiteAbelPlanaLogVerticalStripUpperEdge
            w (x n) (x (n + 1)) y₁ :=
  rfl

/-- The surviving outer vertical edges after summing a chain of vertical
strips and cancelling all shared internal vertical sides. -/
noncomputable def Complex.finiteAbelPlanaLogVerticalStripChainOuterVerticalBoundary
    (w : ℂ)
    (x : ℕ → ℝ)
    (m : ℕ)
    (y₀ y₁ : ℝ) : ℂ :=
  Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution
      w (x 0) y₀ y₁ +
    Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution
      w (x (m + 1)) y₀ y₁

/-- Unfolding of the outer vertical boundary of a vertical-strip chain. -/
theorem Complex.finiteAbelPlana_log_verticalStripChainOuterVerticalBoundary_unfold
    (w : ℂ)
    (x : ℕ → ℝ)
    (m : ℕ)
    (y₀ y₁ : ℝ) :
    Complex.finiteAbelPlanaLogVerticalStripChainOuterVerticalBoundary
        w x m y₀ y₁ =
      Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution
          w (x 0) y₀ y₁ +
        Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution
          w (x (m + 1)) y₀ y₁ :=
  rfl

/-- Horizontal chain boundary for the one-strip chain. -/
theorem Complex.finiteAbelPlana_log_verticalStripChainHorizontalBoundary_zero
    (w : ℂ)
    (x : ℕ → ℝ)
    (y₀ y₁ : ℝ) :
    Complex.finiteAbelPlanaLogVerticalStripChainHorizontalBoundary
        w x 0 y₀ y₁ =
      Complex.finiteAbelPlanaLogVerticalStripLowerEdge
          w (x 0) (x 1) y₀ -
        Complex.finiteAbelPlanaLogVerticalStripUpperEdge
          w (x 0) (x 1) y₁ := by
  calc
    Complex.finiteAbelPlanaLogVerticalStripChainHorizontalBoundary
        w x 0 y₀ y₁ =
      (∑ n in Finset.range (0 + 1),
          Complex.finiteAbelPlanaLogVerticalStripLowerEdge
            w (x n) (x (n + 1)) y₀) -
        ∑ n in Finset.range (0 + 1),
          Complex.finiteAbelPlanaLogVerticalStripUpperEdge
            w (x n) (x (n + 1)) y₁ :=
      Complex.finiteAbelPlana_log_verticalStripChainHorizontalBoundary_unfold
        w x 0 y₀ y₁
    _ =
      Complex.finiteAbelPlanaLogVerticalStripLowerEdge
          w (x 0) (x (0 + 1)) y₀ -
        Complex.finiteAbelPlanaLogVerticalStripUpperEdge
          w (x 0) (x (0 + 1)) y₁ := by
      exact congrArg₂ HSub.hSub
        (Finset.sum_range_one
          (fun n =>
            Complex.finiteAbelPlanaLogVerticalStripLowerEdge
              w (x n) (x (n + 1)) y₀))
        (Finset.sum_range_one
          (fun n =>
            Complex.finiteAbelPlanaLogVerticalStripUpperEdge
              w (x n) (x (n + 1)) y₁))
    _ =
      Complex.finiteAbelPlanaLogVerticalStripLowerEdge
          w (x 0) (x 1) y₀ -
        Complex.finiteAbelPlanaLogVerticalStripUpperEdge
          w (x 0) (x 1) y₁ := by
      exact rfl

/-- Outer vertical boundary for the one-strip chain. -/
theorem Complex.finiteAbelPlana_log_verticalStripChainOuterVerticalBoundary_zero
    (w : ℂ)
    (x : ℕ → ℝ)
    (y₀ y₁ : ℝ) :
    Complex.finiteAbelPlanaLogVerticalStripChainOuterVerticalBoundary
        w x 0 y₀ y₁ =
      Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution
          w (x 0) y₀ y₁ +
        Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution
          w (x 1) y₀ y₁ := by
  calc
    Complex.finiteAbelPlanaLogVerticalStripChainOuterVerticalBoundary
        w x 0 y₀ y₁ =
      Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution
          w (x 0) y₀ y₁ +
        Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution
          w (x (0 + 1)) y₀ y₁ :=
      Complex.finiteAbelPlana_log_verticalStripChainOuterVerticalBoundary_unfold
        w x 0 y₀ y₁
    _ =
      Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution
          w (x 0) y₀ y₁ +
        Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution
          w (x 1) y₀ y₁ := by
      exact rfl

/-- Successor decomposition of the finite sum of vertical-strip boundaries. -/
theorem Complex.finiteAbelPlana_log_verticalStripChainBoundarySum_succ
    (w : ℂ)
    (x : ℕ → ℝ)
    (m : ℕ)
    (y₀ y₁ : ℝ) :
    Complex.finiteAbelPlanaLogVerticalStripChainBoundarySum
        w x (m + 1) y₀ y₁ =
      Complex.finiteAbelPlanaLogVerticalStripChainBoundarySum
          w x m y₀ y₁ +
        Complex.finiteAbelPlanaLogVerticalStripSideExpression
          w (x (m + 1)) (x (m + 2)) y₀ y₁ := by
  calc
    Complex.finiteAbelPlanaLogVerticalStripChainBoundarySum
        w x (m + 1) y₀ y₁ =
      ∑ n in Finset.range (m + 1 + 1),
        Complex.finiteAbelPlanaLogVerticalStripSideExpression
          w (x n) (x (n + 1)) y₀ y₁ :=
      Complex.finiteAbelPlana_log_verticalStripChainBoundarySum_unfold
        w x (m + 1) y₀ y₁
    _ =
      (∑ n in Finset.range (m + 1),
        Complex.finiteAbelPlanaLogVerticalStripSideExpression
          w (x n) (x (n + 1)) y₀ y₁) +
        Complex.finiteAbelPlanaLogVerticalStripSideExpression
          w (x (m + 1)) (x (m + 1 + 1)) y₀ y₁ := by
      exact Finset.sum_range_succ
        (fun n =>
          Complex.finiteAbelPlanaLogVerticalStripSideExpression
            w (x n) (x (n + 1)) y₀ y₁)
        (m + 1)
    _ =
      Complex.finiteAbelPlanaLogVerticalStripChainBoundarySum
          w x m y₀ y₁ +
        Complex.finiteAbelPlanaLogVerticalStripSideExpression
          w (x (m + 1)) (x (m + 2)) y₀ y₁ := by
      exact
        congrArg₂ HAdd.hAdd
          (Complex.finiteAbelPlana_log_verticalStripChainBoundarySum_unfold
            w x m y₀ y₁).symm
          (congrArg
            (fun z =>
              Complex.finiteAbelPlanaLogVerticalStripSideExpression
                w (x (m + 1)) (x z) y₀ y₁)
            (Nat.add_assoc m 1 1))

/-- The horizontal boundary of a vertical-strip chain grows by adjoining the
next lower-minus-upper horizontal edge. -/
theorem Complex.finiteAbelPlana_log_verticalStripChainHorizontalBoundary_succ
    (w : ℂ)
    (x : ℕ → ℝ)
    (m : ℕ)
    (y₀ y₁ : ℝ) :
    Complex.finiteAbelPlanaLogVerticalStripChainHorizontalBoundary
        w x (m + 1) y₀ y₁ =
      Complex.finiteAbelPlanaLogVerticalStripChainHorizontalBoundary
          w x m y₀ y₁ +
        (Complex.finiteAbelPlanaLogVerticalStripLowerEdge
            w (x (m + 1)) (x (m + 2)) y₀ -
          Complex.finiteAbelPlanaLogVerticalStripUpperEdge
            w (x (m + 1)) (x (m + 2)) y₁) := by
  calc
    Complex.finiteAbelPlanaLogVerticalStripChainHorizontalBoundary
        w x (m + 1) y₀ y₁ =
      (∑ n in Finset.range (m + 1 + 1),
        Complex.finiteAbelPlanaLogVerticalStripLowerEdge
          w (x n) (x (n + 1)) y₀) -
      ∑ n in Finset.range (m + 1 + 1),
        Complex.finiteAbelPlanaLogVerticalStripUpperEdge
          w (x n) (x (n + 1)) y₁ :=
      Complex.finiteAbelPlana_log_verticalStripChainHorizontalBoundary_unfold
        w x (m + 1) y₀ y₁
    _ =
      ((∑ n in Finset.range (m + 1),
          Complex.finiteAbelPlanaLogVerticalStripLowerEdge
            w (x n) (x (n + 1)) y₀) +
        Complex.finiteAbelPlanaLogVerticalStripLowerEdge
          w (x (m + 1)) (x (m + 1 + 1)) y₀) -
      ((∑ n in Finset.range (m + 1),
          Complex.finiteAbelPlanaLogVerticalStripUpperEdge
            w (x n) (x (n + 1)) y₁) +
        Complex.finiteAbelPlanaLogVerticalStripUpperEdge
          w (x (m + 1)) (x (m + 1 + 1)) y₁) := by
      exact
        congrArg₂ HSub.hSub
          (Finset.sum_range_succ
            (fun n =>
              Complex.finiteAbelPlanaLogVerticalStripLowerEdge
                w (x n) (x (n + 1)) y₀)
            (m + 1))
          (Finset.sum_range_succ
            (fun n =>
              Complex.finiteAbelPlanaLogVerticalStripUpperEdge
                w (x n) (x (n + 1)) y₁)
            (m + 1))
    _ =
      ((∑ n in Finset.range (m + 1),
          Complex.finiteAbelPlanaLogVerticalStripLowerEdge
            w (x n) (x (n + 1)) y₀) -
        ∑ n in Finset.range (m + 1),
          Complex.finiteAbelPlanaLogVerticalStripUpperEdge
            w (x n) (x (n + 1)) y₁) +
      (Complex.finiteAbelPlanaLogVerticalStripLowerEdge
          w (x (m + 1)) (x (m + 1 + 1)) y₀ -
        Complex.finiteAbelPlanaLogVerticalStripUpperEdge
          w (x (m + 1)) (x (m + 1 + 1)) y₁) := by
      exact add_sub_add_comm
        (∑ n in Finset.range (m + 1),
          Complex.finiteAbelPlanaLogVerticalStripLowerEdge
            w (x n) (x (n + 1)) y₀)
        (Complex.finiteAbelPlanaLogVerticalStripLowerEdge
          w (x (m + 1)) (x (m + 1 + 1)) y₀)
        (∑ n in Finset.range (m + 1),
          Complex.finiteAbelPlanaLogVerticalStripUpperEdge
            w (x n) (x (n + 1)) y₁)
        (Complex.finiteAbelPlanaLogVerticalStripUpperEdge
          w (x (m + 1)) (x (m + 1 + 1)) y₁)
    _ =
      Complex.finiteAbelPlanaLogVerticalStripChainHorizontalBoundary
          w x m y₀ y₁ +
        (Complex.finiteAbelPlanaLogVerticalStripLowerEdge
            w (x (m + 1)) (x (m + 2)) y₀ -
          Complex.finiteAbelPlanaLogVerticalStripUpperEdge
            w (x (m + 1)) (x (m + 2)) y₁) := by
      exact
        congrArg₂ HAdd.hAdd
          (Complex.finiteAbelPlana_log_verticalStripChainHorizontalBoundary_unfold
            w x m y₀ y₁).symm
          (congrArg₂ HSub.hSub
            (congrArg
              (fun z =>
                Complex.finiteAbelPlanaLogVerticalStripLowerEdge
                  w (x (m + 1)) (x z) y₀)
              (Nat.add_assoc m 1 1))
            (congrArg
              (fun z =>
                Complex.finiteAbelPlanaLogVerticalStripUpperEdge
                  w (x (m + 1)) (x z) y₁)
              (Nat.add_assoc m 1 1)))

/-- Algebra for the successor step in the vertical-strip chain cancellation. -/
theorem vertical_strip_chain_successor_cancel_algebra
    {H Hnew L₀ Rold Lold Rnew : ℂ}
    (hcancel : Rold + Lold = 0) :
    (H + (L₀ + Rold)) + (Hnew + (Lold + Rnew)) =
      (H + Hnew) + (L₀ + Rnew) := by
  calc
    (H + (L₀ + Rold)) + (Hnew + (Lold + Rnew))
        = H + Hnew + Rnew + L₀ := by
      exact adjacent_vertical_strip_boundary_cancel_algebra
        (H₀ := H) (H₁ := Hnew) (L₀ := L₀) (R₀ := Rold)
        (L₁ := Lold) (R₁ := Rnew) hcancel
    _ = (H + Hnew) + (Rnew + L₀) := by
      exact add_assoc (H + Hnew) Rnew L₀
    _ = (H + Hnew) + (L₀ + Rnew) := by
      exact congrArg (fun z => (H + Hnew) + z) (add_comm Rnew L₀)

/-- A single vertical strip has the horizontal boundary plus the two outer
vertical sides; this is only the order normalization of those two sides. -/
theorem Complex.finiteAbelPlana_log_singleVerticalStripBoundary_eq_horizontal_add_outer
    (w : ℂ)
    (x₀ x₁ y₀ y₁ : ℝ) :
    Complex.finiteAbelPlanaLogVerticalStripSideExpression w x₀ x₁ y₀ y₁ =
      (Complex.finiteAbelPlanaLogVerticalStripLowerEdge w x₀ x₁ y₀ -
        Complex.finiteAbelPlanaLogVerticalStripUpperEdge w x₀ x₁ y₁) +
        (Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution w x₀ y₀ y₁ +
          Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution w x₁ y₀ y₁) := by
  exact
    Complex.finiteAbelPlana_log_singleVerticalStripBoundary_eq_horizontal_add_outer_core
      w x₀ x₁ y₀ y₁

/-- Summing the boundary expressions of a vertical strip chain cancels the
shared internal vertical sides.  The result keeps the horizontal pieces
unconcatenated; horizontal interval concatenation is a separate owner lemma. -/
theorem Complex.finiteAbelPlana_log_verticalStripChainBoundarySum_telescopes
    (w : ℂ)
    (x : ℕ → ℝ)
    (m : ℕ)
    (y₀ y₁ : ℝ) :
    Complex.finiteAbelPlanaLogVerticalStripChainBoundarySum w x m y₀ y₁ =
      Complex.finiteAbelPlanaLogVerticalStripChainHorizontalBoundary
          w x m y₀ y₁ +
        Complex.finiteAbelPlanaLogVerticalStripChainOuterVerticalBoundary
          w x m y₀ y₁ := by
  induction m with
  | zero =>
      calc
        Complex.finiteAbelPlanaLogVerticalStripChainBoundarySum
            w x 0 y₀ y₁ =
          ∑ n in Finset.range (0 + 1),
            Complex.finiteAbelPlanaLogVerticalStripSideExpression
              w (x n) (x (n + 1)) y₀ y₁ :=
          Complex.finiteAbelPlana_log_verticalStripChainBoundarySum_unfold
            w x 0 y₀ y₁
        _ =
          Complex.finiteAbelPlanaLogVerticalStripSideExpression
            w (x 0) (x (0 + 1)) y₀ y₁ := by
          exact Finset.sum_range_one
            (fun n =>
              Complex.finiteAbelPlanaLogVerticalStripSideExpression
                w (x n) (x (n + 1)) y₀ y₁)
        _ =
          (Complex.finiteAbelPlanaLogVerticalStripLowerEdge
              w (x 0) (x 1) y₀ -
            Complex.finiteAbelPlanaLogVerticalStripUpperEdge
              w (x 0) (x 1) y₁) +
            (Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution
                w (x 0) y₀ y₁ +
              Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution
                w (x 1) y₀ y₁) :=
          Complex.finiteAbelPlana_log_singleVerticalStripBoundary_eq_horizontal_add_outer
            w (x 0) (x 1) y₀ y₁
        _ =
          Complex.finiteAbelPlanaLogVerticalStripChainHorizontalBoundary
              w x 0 y₀ y₁ +
            Complex.finiteAbelPlanaLogVerticalStripChainOuterVerticalBoundary
              w x 0 y₀ y₁ := by
          exact
            congrArg₂ HAdd.hAdd
              (Complex.finiteAbelPlana_log_verticalStripChainHorizontalBoundary_zero
                w x y₀ y₁).symm
              (Complex.finiteAbelPlana_log_verticalStripChainOuterVerticalBoundary_zero
                w x y₀ y₁).symm
  | succ m hm =>
      calc
        Complex.finiteAbelPlanaLogVerticalStripChainBoundarySum
            w x (m + 1) y₀ y₁ =
          Complex.finiteAbelPlanaLogVerticalStripChainBoundarySum
              w x m y₀ y₁ +
            Complex.finiteAbelPlanaLogVerticalStripSideExpression
              w (x (m + 1)) (x (m + 2)) y₀ y₁ := by
            exact
              Complex.finiteAbelPlana_log_verticalStripChainBoundarySum_succ
                w x m y₀ y₁
        _ =
          (Complex.finiteAbelPlanaLogVerticalStripChainHorizontalBoundary
              w x m y₀ y₁ +
            Complex.finiteAbelPlanaLogVerticalStripChainOuterVerticalBoundary
              w x m y₀ y₁) +
            Complex.finiteAbelPlanaLogVerticalStripSideExpression
              w (x (m + 1)) (x (m + 2)) y₀ y₁ := by
            exact congrArg
              (fun z =>
                z +
                  Complex.finiteAbelPlanaLogVerticalStripSideExpression
                    w (x (m + 1)) (x (m + 2)) y₀ y₁)
              hm
        _ =
          Complex.finiteAbelPlanaLogVerticalStripChainHorizontalBoundary
              w x (m + 1) y₀ y₁ +
            Complex.finiteAbelPlanaLogVerticalStripChainOuterVerticalBoundary
              w x (m + 1) y₀ y₁ := by
            let H : ℂ :=
              Complex.finiteAbelPlanaLogVerticalStripChainHorizontalBoundary
                w x m y₀ y₁
            let Hnew : ℂ :=
              Complex.finiteAbelPlanaLogVerticalStripLowerEdge
                w (x (m + 1)) (x (m + 2)) y₀ -
              Complex.finiteAbelPlanaLogVerticalStripUpperEdge
                w (x (m + 1)) (x (m + 2)) y₁
            let L₀ : ℂ :=
              Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution
                w (x 0) y₀ y₁
            let Rold : ℂ :=
              Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution
                w (x (m + 1)) y₀ y₁
            let Lold : ℂ :=
              Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution
                w (x (m + 1)) y₀ y₁
            let Rnew : ℂ :=
              Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution
                w (x (m + 2)) y₀ y₁
            have hside :
                Complex.finiteAbelPlanaLogVerticalStripSideExpression
                    w (x (m + 1)) (x (m + 2)) y₀ y₁ =
                  Hnew + (Lold + Rnew) := by
              exact
                Complex.finiteAbelPlana_log_singleVerticalStripBoundary_eq_horizontal_add_outer
                  w (x (m + 1)) (x (m + 2)) y₀ y₁
            have houter_old :
                Complex.finiteAbelPlanaLogVerticalStripChainOuterVerticalBoundary
                    w x m y₀ y₁ =
                  L₀ + Rold := by
              rfl
            have houter_new :
                Complex.finiteAbelPlanaLogVerticalStripChainOuterVerticalBoundary
                    w x (m + 1) y₀ y₁ =
                  L₀ + Rnew := by
              rfl
            have hhorizontal :
                Complex.finiteAbelPlanaLogVerticalStripChainHorizontalBoundary
                    w x (m + 1) y₀ y₁ =
                  H + Hnew := by
              exact
                Complex.finiteAbelPlana_log_verticalStripChainHorizontalBoundary_succ
                  w x m y₀ y₁
            have hcancel : Rold + Lold = 0 := by
              exact
                Complex.finiteAbelPlana_log_internalVerticalEdge_right_add_left_cancel
                  w (x (m + 1)) y₀ y₁
            calc
              (Complex.finiteAbelPlanaLogVerticalStripChainHorizontalBoundary
                  w x m y₀ y₁ +
                Complex.finiteAbelPlanaLogVerticalStripChainOuterVerticalBoundary
                  w x m y₀ y₁) +
                Complex.finiteAbelPlanaLogVerticalStripSideExpression
                  w (x (m + 1)) (x (m + 2)) y₀ y₁
                  =
                (H + (L₀ + Rold)) + (Hnew + (Lold + Rnew)) := by
                exact
                  congrArg₂ HAdd.hAdd
                    (congrArg₂ HAdd.hAdd rfl houter_old)
                    hside
              _ = (H + Hnew) + (L₀ + Rnew) :=
                vertical_strip_chain_successor_cancel_algebra hcancel
              _ =
                Complex.finiteAbelPlanaLogVerticalStripChainHorizontalBoundary
                    w x (m + 1) y₀ y₁ +
                  Complex.finiteAbelPlanaLogVerticalStripChainOuterVerticalBoundary
                    w x (m + 1) y₀ y₁ := by
                exact
                  congrArg₂ HAdd.hAdd
                    hhorizontal.symm
                    houter_new.symm

/-- After internal vertical-edge cancellation, the remaining finite-radius
punctured boundary is the outer principal-value rectangle boundary minus the
two endpoint deleted arcs and the interior deleted circles. -/
theorem Complex.finiteAbelPlana_log_remainingBoundary_after_internalVerticalCancellation
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogFiniteRadiusPuncturedBoundaryIntegral N w T ρ =
      Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
        (Complex.finiteAbelPlanaLogLeftEndpointIndentationIntegral w ρ +
          Complex.finiteAbelPlanaLogRightEndpointIndentationIntegral N w ρ +
            ∑ n in Finset.range N,
              Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w (n + 1 : ℂ) ρ) := by
  calc
    Complex.finiteAbelPlanaLogFiniteRadiusPuncturedBoundaryIntegral N w T ρ =
        Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
          Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ := by
      exact
        Complex.finiteAbelPlana_log_finiteRadiusPuncturedBoundaryIntegral_eq_pvNormalized_sub_deleted
          N w T ρ
    _ =
        Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
          (Complex.finiteAbelPlanaLogLeftEndpointIndentationIntegral w ρ +
            Complex.finiteAbelPlanaLogRightEndpointIndentationIntegral N w ρ +
              ∑ n in Finset.range N,
                Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w (n + 1 : ℂ) ρ) := by
      exact
        congrArg
          (fun z =>
            Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
              z)
          (Complex.finiteAbelPlana_log_deletedBoundaryContribution_decomposition N w ρ)

/-- Oriented boundary integral of an ordinary axis-parallel rectangle for the
finite Abel-Plana logarithmic contour integrand.

This is the exact side convention used by mathlib's rectangle Cauchy theorem:
bottom minus top plus `I` times right minus `I` times left. -/
noncomputable def Complex.finiteAbelPlanaLogRectangleBoundaryIntegral
    (w : ℂ)
    (z₀ z₁ : ℂ) : ℂ :=
  (∫ x : ℝ in z₀.re..z₁.re,
      Complex.finiteAbelPlanaLogRectangleIntegrand w
        ((x : ℂ) + (z₀.im : ℂ) * Complex.I)) -
    (∫ x : ℝ in z₀.re..z₁.re,
      Complex.finiteAbelPlanaLogRectangleIntegrand w
        ((x : ℂ) + (z₁.im : ℂ) * Complex.I)) +
      Complex.I •
        (∫ y : ℝ in z₀.im..z₁.im,
          Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((z₁.re : ℂ) + (y : ℂ) * Complex.I)) -
        Complex.I •
          (∫ y : ℝ in z₀.im..z₁.im,
            Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((z₀.re : ℂ) + (y : ℂ) * Complex.I))

/-- Unfolding of the ordinary rectangle boundary integral convention. -/
theorem Complex.finiteAbelPlanaLogRectangleBoundaryIntegral_unfold
    (w : ℂ)
    (z₀ z₁ : ℂ) :
    Complex.finiteAbelPlanaLogRectangleBoundaryIntegral w z₀ z₁ =
      (∫ x : ℝ in z₀.re..z₁.re,
          Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((x : ℂ) + (z₀.im : ℂ) * Complex.I)) -
        (∫ x : ℝ in z₀.re..z₁.re,
          Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((x : ℂ) + (z₁.im : ℂ) * Complex.I)) +
          Complex.I •
            (∫ y : ℝ in z₀.im..z₁.im,
              Complex.finiteAbelPlanaLogRectangleIntegrand w
                ((z₁.re : ℂ) + (y : ℂ) * Complex.I)) -
            Complex.I •
              (∫ y : ℝ in z₀.im..z₁.im,
                Complex.finiteAbelPlanaLogRectangleIntegrand w
                  ((z₀.re : ℂ) + (y : ℂ) * Complex.I)) :=
  rfl

/-- Cauchy-Goursat for any ordinary rectangle contained in the finite
punctured Abel-Plana rectangle.

This is the reusable per-rectangle owner API for the finite-hole
decomposition.  The hypotheses are geometric inclusions only: the closed
rectangle gives continuity, and the open rectangle gives holomorphy. -/
theorem Complex.finiteAbelPlana_log_rectangleBoundaryIntegral_eq_zero_of_subset_puncturedRectangle_of_holomorphic
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (z₀ z₁ : ℂ)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hclosed :
      (Set.uIcc z₀.re z₁.re ×ℂ Set.uIcc z₀.im z₁.im) ⊆
        Complex.finiteAbelPlanaPuncturedRectangle N T ρ)
    (hopen :
      (Set.Ioo (min z₀.re z₁.re) (max z₀.re z₁.re) ×ℂ
          Set.Ioo (min z₀.im z₁.im) (max z₀.im z₁.im)) ⊆
        Complex.finiteAbelPlanaPuncturedRectangle N T ρ) :
    Complex.finiteAbelPlanaLogRectangleBoundaryIntegral w z₀ z₁ = 0 := by
  let f : ℂ → ℂ :=
    fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z
  have hcontinuous_punctured :
      ContinuousOn f
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ) :=
    hcont
  have hcontinuous_closed :
      ContinuousOn f (Set.uIcc z₀.re z₁.re ×ℂ Set.uIcc z₀.im z₁.im) :=
    hcontinuous_punctured.mono hclosed
  have hdifferentiable_punctured :
      DifferentiableOn ℂ f
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ) :=
    hdiff
  have hdifferentiable_open :
      DifferentiableOn ℂ f
        (Set.Ioo (min z₀.re z₁.re) (max z₀.re z₁.re) ×ℂ
          Set.Ioo (min z₀.im z₁.im) (max z₀.im z₁.im)) :=
    hdifferentiable_punctured.mono hopen
  have hcauchy :
      (∫ x : ℝ in z₀.re..z₁.re,
          f ((x : ℂ) + (z₀.im : ℂ) * Complex.I)) -
        (∫ x : ℝ in z₀.re..z₁.re,
          f ((x : ℂ) + (z₁.im : ℂ) * Complex.I)) +
          Complex.I •
            (∫ y : ℝ in z₀.im..z₁.im,
              f ((z₁.re : ℂ) + (y : ℂ) * Complex.I)) -
            Complex.I •
              (∫ y : ℝ in z₀.im..z₁.im,
                f ((z₀.re : ℂ) + (y : ℂ) * Complex.I)) = 0 :=
    Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
      f z₀ z₁ hcontinuous_closed hdifferentiable_open
  calc
    Complex.finiteAbelPlanaLogRectangleBoundaryIntegral w z₀ z₁ =
      (∫ x : ℝ in z₀.re..z₁.re,
          Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((x : ℂ) + (z₀.im : ℂ) * Complex.I)) -
        (∫ x : ℝ in z₀.re..z₁.re,
          Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((x : ℂ) + (z₁.im : ℂ) * Complex.I)) +
          Complex.I •
            (∫ y : ℝ in z₀.im..z₁.im,
              Complex.finiteAbelPlanaLogRectangleIntegrand w
                ((z₁.re : ℂ) + (y : ℂ) * Complex.I)) -
            Complex.I •
              (∫ y : ℝ in z₀.im..z₁.im,
                Complex.finiteAbelPlanaLogRectangleIntegrand w
                  ((z₀.re : ℂ) + (y : ℂ) * Complex.I)) :=
      Complex.finiteAbelPlanaLogRectangleBoundaryIntegral_unfold w z₀ z₁
    _ =
      (∫ x : ℝ in z₀.re..z₁.re,
          f ((x : ℂ) + (z₀.im : ℂ) * Complex.I)) -
        (∫ x : ℝ in z₀.re..z₁.re,
          f ((x : ℂ) + (z₁.im : ℂ) * Complex.I)) +
          Complex.I •
            (∫ y : ℝ in z₀.im..z₁.im,
              f ((z₁.re : ℂ) + (y : ℂ) * Complex.I)) -
            Complex.I •
              (∫ y : ℝ in z₀.im..z₁.im,
                f ((z₀.re : ℂ) + (y : ℂ) * Complex.I)) := by
      rfl
    _ = 0 :=
      hcauchy

/-- Cauchy-Goursat for any ordinary rectangle contained in the finite
punctured Abel-Plana rectangle, using the canonical regularity theorem for the
Abel-Plana rectangle integrand. -/
theorem Complex.finiteAbelPlana_log_rectangleBoundaryIntegral_eq_zero_of_subset_puncturedRectangle
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (z₀ z₁ : ℂ)
    (hclosed :
      (Set.uIcc z₀.re z₁.re ×ℂ Set.uIcc z₀.im z₁.im) ⊆
        Complex.finiteAbelPlanaPuncturedRectangle N T ρ)
    (hopen :
      (Set.Ioo (min z₀.re z₁.re) (max z₀.re z₁.re) ×ℂ
          Set.Ioo (min z₀.im z₁.im) (max z₀.im z₁.im)) ⊆
        Complex.finiteAbelPlanaPuncturedRectangle N T ρ) :
    Complex.finiteAbelPlanaLogRectangleBoundaryIntegral w z₀ z₁ = 0 := by
  have hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ) :=
    Complex.continuousOn_finiteAbelPlanaLogRectangleIntegrand_puncturedRectangle
      hw N T hρ
  have hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ) :=
    Complex.differentiableOn_finiteAbelPlanaLogRectangleIntegrand_puncturedRectangle
      hw N T hρ
  exact
    Complex.finiteAbelPlana_log_rectangleBoundaryIntegral_eq_zero_of_subset_puncturedRectangle_of_holomorphic
      N T z₀ z₁ hcont hdiff hclosed hopen

end

end LFunctions
end Boundary

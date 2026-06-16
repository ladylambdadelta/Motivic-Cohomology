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

/-- Right real boundary of the `k`th finite-hole vertical strip. -/
def Complex.finiteAbelPlanaLogFiniteHoleVerticalStripRight
    (ρ : ℝ)
    (k : ℕ) : ℝ :=
  (k + 1 : ℝ) - ρ

/-- The `k`th vertical subrectangle between neighboring deleted pole disks. -/
def Complex.finiteAbelPlanaLogFiniteHoleVerticalStrip
    (N : ℕ)
    (T ρ : ℝ)
    (k : ℕ) : Set ℂ :=
  Set.Icc
      (Complex.finiteAbelPlanaLogFiniteHoleVerticalStripLeft ρ k)
      (Complex.finiteAbelPlanaLogFiniteHoleVerticalStripRight ρ k) ×ℂ
    [[-T, T]]

/-- Union of all finite-hole vertical strips. -/
def Complex.finiteAbelPlanaLogFiniteHoleVerticalStripUnion
    (N : ℕ)
    (T ρ : ℝ) : Set ℂ :=
  ⋃ k ∈ Complex.finiteAbelPlanaLogFiniteHoleVerticalStripIndexSet N,
    Complex.finiteAbelPlanaLogFiniteHoleVerticalStrip N T ρ k

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
      z.im ∈ [[-T, T]] := by
  exact Complex.mem_reProdIm

/-- Membership in the finite strip union is membership in one indexed strip. -/
theorem Complex.mem_finiteAbelPlanaLogFiniteHoleVerticalStripUnion_iff
    {N : ℕ}
    {T ρ : ℝ}
    {z : ℂ} :
    z ∈ Complex.finiteAbelPlanaLogFiniteHoleVerticalStripUnion N T ρ ↔
      ∃ k ∈ Complex.finiteAbelPlanaLogFiniteHoleVerticalStripIndexSet N,
        z ∈ Complex.finiteAbelPlanaLogFiniteHoleVerticalStrip N T ρ k := by
  dsimp [Complex.finiteAbelPlanaLogFiniteHoleVerticalStripUnion]
  constructor
  · intro hz
    rcases Set.mem_iUnion.1 hz with ⟨k, hkz⟩
    rcases Set.mem_iUnion.1 hkz with ⟨hk, hzstrip⟩
    exact ⟨k, hk, hzstrip⟩
  · intro hz
    rcases hz with ⟨k, hk, hzstrip⟩
    exact Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hk, hzstrip⟩⟩

/-- The finite strip list has exactly the strip count `N + 1`. -/
theorem Complex.length_finiteAbelPlanaLogFiniteHoleVerticalStripList
    (N : ℕ)
    (T ρ : ℝ) :
    (Complex.finiteAbelPlanaLogFiniteHoleVerticalStripList N T ρ).length =
      N + 1 := by
  dsimp [Complex.finiteAbelPlanaLogFiniteHoleVerticalStripList]
  simpa using
    (List.length_map
      (fun k => Complex.finiteAbelPlanaLogFiniteHoleVerticalStrip N T ρ k)
      (List.range (N + 1)))

/-- Every indexed vertical strip appears in the concrete finite strip list. -/
theorem Complex.finiteAbelPlanaLogFiniteHoleVerticalStrip_mem_list
    {N k : ℕ}
    {T ρ : ℝ}
    (hk : k ∈ Complex.finiteAbelPlanaLogFiniteHoleVerticalStripIndexSet N) :
    Complex.finiteAbelPlanaLogFiniteHoleVerticalStrip N T ρ k ∈
      Complex.finiteAbelPlanaLogFiniteHoleVerticalStripList N T ρ := by
  dsimp [Complex.finiteAbelPlanaLogFiniteHoleVerticalStripList]
  exact List.mem_map.2
    ⟨k, by exact List.mem_range.mpr (Finset.mem_range.mp hk), rfl⟩

/-- A strip index is bounded by the last strip index. -/
theorem Complex.finiteAbelPlanaLogFiniteHoleVerticalStripIndex_le
    {N k : ℕ}
    (hk : k ∈ Complex.finiteAbelPlanaLogFiniteHoleVerticalStripIndexSet N) :
    k ≤ N := by
  have hklt : k < N + 1 := by
    exact Finset.mem_range.mp hk
  exact Nat.lt_succ_iff.mp hklt

/-- The strip interval is ordered when the deletion radius is below `1/4`. -/
theorem Complex.finiteAbelPlanaLogFiniteHoleVerticalStrip_left_le_right
    {ρ : ℝ}
    (hρquarter : ρ < (1 : ℝ) / 4)
    (k : ℕ) :
    Complex.finiteAbelPlanaLogFiniteHoleVerticalStripLeft ρ k ≤
      Complex.finiteAbelPlanaLogFiniteHoleVerticalStripRight ρ k := by
  have hρhalf : ρ ≤ (1 : ℝ) / 2 := by
    have hquarter_half : (1 : ℝ) / 4 ≤ (1 : ℝ) / 2 := by norm_num
    exact (le_of_lt hρquarter).trans hquarter_half
  dsimp [Complex.finiteAbelPlanaLogFiniteHoleVerticalStripLeft,
    Complex.finiteAbelPlanaLogFiniteHoleVerticalStripRight]
  linarith

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
      z.im ∈ [[-T, T]] :=
    Complex.mem_finiteAbelPlanaLogFiniteHoleVerticalStrip_iff.mp hz
  have hk_le : k ≤ N :=
    Complex.finiteAbelPlanaLogFiniteHoleVerticalStripIndex_le hk
  have hzre_nonneg : 0 ≤ z.re := by
    have hleft : (k : ℝ) + ρ ≤ z.re := hzdata.1.1
    have hk_nonneg : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hzre_le : z.re ≤ (N + 1 : ℝ) := by
    have hright : z.re ≤ (k + 1 : ℝ) - ρ := hzdata.1.2
    have hk_right : (k + 1 : ℝ) ≤ (N + 1 : ℝ) := by
      exact_mod_cast Nat.succ_le_succ hk_le
    linarith
  have hright_nonneg : (0 : ℝ) ≤ (N + 1 : ℝ) := by
    exact Nat.cast_nonneg (N + 1)
  have hzre_uIcc : z.re ∈ [[(0 : ℝ), (N + 1 : ℝ)]] := by
    have hzre_Icc : z.re ∈ Set.Icc (0 : ℝ) (N + 1 : ℝ) :=
      ⟨hzre_nonneg, hzre_le⟩
    have hset :
        [[(0 : ℝ), (N + 1 : ℝ)]] =
          Set.Icc (0 : ℝ) (N + 1 : ℝ) := by
      exact Set.uIcc_of_le hright_nonneg
    exact hset.symm ▸ hzre_Icc
  exact Complex.mem_reProdIm.mpr ⟨hzre_uIcc, hzdata.2⟩

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
  rcases
    Complex.mem_finiteAbelPlanaLogFiniteHoleVerticalStripUnion_iff.mp hz
      with ⟨k, hk, hzstrip⟩
  exact
    Complex.finiteAbelPlanaLogFiniteHoleVerticalStrip_subset_closedRectangle
      hk hρnonneg hρquarter hzstrip

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
      z.im ∈ [[-T, T]] :=
    Complex.mem_finiteAbelPlanaLogFiniteHoleVerticalStrip_iff.mp hz
  have hdist_lt : ‖z - (n : ℂ)‖ < ρ := by
    simpa [dist_eq_norm, sub_eq_add_neg] using Metric.mem_ball.mp hzball
  have hre_norm :
      |(z - (n : ℂ)).re| ≤ ‖z - (n : ℂ)‖ := by
    simpa [Complex.norm_eq_abs] using Complex.abs_re_le_abs (z - (n : ℂ))
  by_cases hnk : n ≤ k
  · have hn_le_k_real : (n : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast hnk
    have hleft : (k : ℝ) + ρ ≤ z.re := hzdata.1.1
    have hre_ge : ρ ≤ (z - (n : ℂ)).re := by
      simp [sub_re]
      linarith
    have hρ_le_abs : ρ ≤ |(z - (n : ℂ)).re| :=
      hre_ge.trans (le_abs_self _)
    exact not_lt_of_ge (hρ_le_abs.trans hre_norm) hdist_lt
  · have hk_lt_n : k < n := Nat.lt_of_not_ge hnk
    have hk_succ_le_n : k + 1 ≤ n := Nat.succ_le_iff.mpr hk_lt_n
    have hk_succ_le_n_real : (k + 1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hk_succ_le_n
    have hright : z.re ≤ (k + 1 : ℝ) - ρ := hzdata.1.2
    have hre_le_neg : (z - (n : ℂ)).re ≤ -ρ := by
      simp [sub_re]
      linarith
    have hρ_le_abs : ρ ≤ |(z - (n : ℂ)).re| := by
      have hneg : ρ ≤ -((z - (n : ℂ)).re) := by linarith
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
  rcases
    Complex.mem_finiteAbelPlanaLogFiniteHoleVerticalStripUnion_iff.mp hz
      with ⟨k, hk, hzstrip⟩
  exact
    Complex.finiteAbelPlanaLogFiniteHoleVerticalStrip_subset_puncturedRectangle
      hk hρnonneg hρquarter hzstrip

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

/-- The left-side contribution of a vertical subdivision edge. -/
noncomputable def Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution
    (w : ℂ)
    (x y₀ y₁ : ℝ) : ℂ :=
  -Complex.I *
    Complex.finiteAbelPlanaLogVerticalSubdivisionEdge w x y₀ y₁

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
    intervalIntegral.integral_symm y₁ y₀
      (fun y : ℝ =>
        Complex.finiteAbelPlanaLogRectangleIntegrand w
          ((x : ℂ) + Complex.I * (y : ℂ)))

/-- The right contribution of an internal vertical edge cancels the adjacent
left contribution with the same parametrization. -/
theorem Complex.finiteAbelPlana_log_internalVerticalEdge_right_add_left_cancel
    (w : ℂ)
    (x y₀ y₁ : ℝ) :
    Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution w x y₀ y₁ +
      Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution w x y₀ y₁ =
        0 := by
  dsimp [Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution,
    Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution]
  ring

/-- The left contribution of an internal vertical edge cancels the adjacent
right contribution with the same parametrization. -/
theorem Complex.finiteAbelPlana_log_internalVerticalEdge_left_add_right_cancel
    (w : ℂ)
    (x y₀ y₁ : ℝ) :
    Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution w x y₀ y₁ +
      Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution w x y₀ y₁ =
        0 := by
  dsimp [Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution,
    Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution]
  ring

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

/-- Two adjacent vertical strips cancel their shared internal vertical edge.

The result deliberately leaves the two lower pieces and two upper pieces
unmerged; horizontal concatenation is a separate interval-integral theorem.
This lemma owns only the internal vertical-edge cancellation. -/
theorem Complex.finiteAbelPlana_log_adjacentVerticalStripBoundaries_cancel_internalEdge
    (w : ℂ)
    (x₀ x₁ x₂ y₀ y₁ : ℝ) :
    Complex.finiteAbelPlanaLogVerticalStripSideExpression w x₀ x₁ y₀ y₁ +
        Complex.finiteAbelPlanaLogVerticalStripSideExpression w x₁ x₂ y₀ y₁ =
      Complex.finiteAbelPlanaLogVerticalStripLowerEdge w x₀ x₁ y₀ -
        Complex.finiteAbelPlanaLogVerticalStripUpperEdge w x₀ x₁ y₁ +
          Complex.finiteAbelPlanaLogVerticalStripLowerEdge w x₁ x₂ y₀ -
            Complex.finiteAbelPlanaLogVerticalStripUpperEdge w x₁ x₂ y₁ +
              Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution w x₂ y₀ y₁ +
                Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution w x₀ y₀ y₁ := by
  dsimp [Complex.finiteAbelPlanaLogVerticalStripSideExpression,
    Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution,
    Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution]
  ring

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
      dsimp [Complex.finiteAbelPlanaLogVerticalStripChainBoundarySum,
        Complex.finiteAbelPlanaLogVerticalStripChainHorizontalBoundary,
        Complex.finiteAbelPlanaLogVerticalStripChainOuterVerticalBoundary,
        Complex.finiteAbelPlanaLogVerticalStripSideExpression]
      ring
  | succ m hm =>
      calc
        Complex.finiteAbelPlanaLogVerticalStripChainBoundarySum
            w x (m + 1) y₀ y₁ =
          Complex.finiteAbelPlanaLogVerticalStripChainBoundarySum
              w x m y₀ y₁ +
            Complex.finiteAbelPlanaLogVerticalStripSideExpression
              w (x (m + 1)) (x (m + 2)) y₀ y₁ := by
            dsimp [Complex.finiteAbelPlanaLogVerticalStripChainBoundarySum]
            rw [Finset.sum_range_succ]
        _ =
          (Complex.finiteAbelPlanaLogVerticalStripChainHorizontalBoundary
              w x m y₀ y₁ +
            Complex.finiteAbelPlanaLogVerticalStripChainOuterVerticalBoundary
              w x m y₀ y₁) +
            Complex.finiteAbelPlanaLogVerticalStripSideExpression
              w (x (m + 1)) (x (m + 2)) y₀ y₁ := by
            rw [hm]
        _ =
          Complex.finiteAbelPlanaLogVerticalStripChainHorizontalBoundary
              w x (m + 1) y₀ y₁ +
            Complex.finiteAbelPlanaLogVerticalStripChainOuterVerticalBoundary
              w x (m + 1) y₀ y₁ := by
            dsimp [Complex.finiteAbelPlanaLogVerticalStripChainHorizontalBoundary,
              Complex.finiteAbelPlanaLogVerticalStripChainOuterVerticalBoundary,
              Complex.finiteAbelPlanaLogVerticalStripSideExpression,
              Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution,
              Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution]
            rw [Finset.sum_range_succ, Finset.sum_range_succ]
            ring

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
      rw [Complex.finiteAbelPlana_log_deletedBoundaryContribution_decomposition]

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
      ([[z₀.re, z₁.re]] ×ℂ [[z₀.im, z₁.im]]) ⊆
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
      ContinuousOn f ([[z₀.re, z₁.re]] ×ℂ [[z₀.im, z₁.im]]) :=
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
  simpa [Complex.finiteAbelPlanaLogRectangleBoundaryIntegral, f] using hcauchy

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
      ([[z₀.re, z₁.re]] ×ℂ [[z₀.im, z₁.im]]) ⊆
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

end

end LFunctions
end Boundary

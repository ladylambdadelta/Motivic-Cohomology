import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaFiniteHeightBoundaryPieces

/-!
# Punctured rectangle geometry for finite-height Abel-Plana

This file owns the punctured finite-height rectangle, integer-pole set,
deleted-disk geometry, slit/pole safety, and finite-radius boundary
accounting equivalences.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- The fixed quarter-radius used to separate neighboring integer poles is
positive. -/
theorem real_one_fourth_pos :
    0 < (1 : ℝ) / 4 := by
  have hfour_pos : (0 : ℝ) < 4 := by
    exact zero_lt_four
  exact div_pos zero_lt_one hfour_pos

/-- The finite Abel-Plana integer range is nonempty, with `0` as canonical
witness. -/
theorem Finset.zero_mem_range_nat_add_two
    (N : ℕ) :
    0 ∈ Finset.range (N + 2) := by
  exact Finset.mem_range.mpr (Nat.succ_pos (N + 1))

/-- Canonical nonempty witness for the finite Abel-Plana integer range. -/
theorem Finset.range_nat_add_two_nonempty
    (N : ℕ) :
    (Finset.range (N + 2)).Nonempty := by
  exact ⟨0, Finset.zero_mem_range_nat_add_two N⟩

noncomputable def Complex.finiteAbelPlanaLogPuncturedRectangleRadiusBound
    (w : ℂ)
    (N : ℕ)
    (T : ℝ) : ℝ :=
  min ((1 : ℝ) / 4)
    (min (|T| / 2)
      (Finset.inf' (Finset.range (N + 2))
        (Finset.range_nat_add_two_nonempty N)
        (fun n => Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)))

/-- The punctured-rectangle deletion radius bound unfolded in scalar form. -/
theorem Complex.finiteAbelPlanaLogPuncturedRectangleRadiusBound_unfold
    (w : ℂ)
    (N : ℕ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogPuncturedRectangleRadiusBound w N T =
      min ((1 : ℝ) / 4)
        (min (|T| / 2)
          (Finset.inf' (Finset.range (N + 2))
            (Finset.range_nat_add_two_nonempty N)
            (fun n =>
              Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n))) :=
  rfl

/-- The finite punctured-rectangle radius bound is positive when the height is
nonzero and `w` is in the right half-plane. -/
theorem Complex.finiteAbelPlana_log_puncturedRectangleRadiusBound_pos
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    {T : ℝ}
    (hT : 0 < T) :
    0 < Complex.finiteAbelPlanaLogPuncturedRectangleRadiusBound w N T := by
  have hquarter : 0 < (1 : ℝ) / 4 := real_one_fourth_pos
  have hheight : 0 < |T| / 2 := by
    have hT_abs : 0 < |T| := abs_pos.mpr (ne_of_gt hT)
    exact half_pos hT_abs
  have hnonempty : (Finset.range (N + 2)).Nonempty := by
    exact Finset.range_nat_add_two_nonempty N
  have hinf :
      0 <
        Finset.inf' (Finset.range (N + 2))
          (Finset.range_nat_add_two_nonempty N)
          (fun n => Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n) := by
    exact
      (Finset.lt_inf'_iff hnonempty).mpr
        (fun n _hn =>
          Complex.finiteAbelPlana_log_integerResidueIsolationRadius_pos
            hw n)
  have hpositive :
      0 <
        min ((1 : ℝ) / 4)
          (min (|T| / 2)
            (Finset.inf' (Finset.range (N + 2))
              (Finset.range_nat_add_two_nonempty N)
              (fun n =>
                Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n))) :=
    lt_min hquarter (lt_min hheight hinf)
  exact
    Eq.subst
      (motive := fun R : ℝ => 0 < R)
      (Complex.finiteAbelPlanaLogPuncturedRectangleRadiusBound_unfold w N T).symm
      hpositive

/-- Any deletion radius below the punctured-rectangle bound is below the
fixed quarter-radius used to separate neighboring integer pole disks. -/
theorem Complex.finiteAbelPlana_log_puncturedRectangle_radius_lt_quarter
    (w : ℂ)
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hρR : ρ <
      Complex.finiteAbelPlanaLogPuncturedRectangleRadiusBound w N T) :
    ρ < (1 : ℝ) / 4 := by
  have hρR_unfold :
      ρ <
        min ((1 : ℝ) / 4)
          (min (|T| / 2)
            (Finset.inf' (Finset.range (N + 2))
              (Finset.range_nat_add_two_nonempty N)
              (fun n =>
                Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n))) :=
    Eq.subst
      (motive := fun R : ℝ => ρ < R)
      (Complex.finiteAbelPlanaLogPuncturedRectangleRadiusBound_unfold w N T)
      hρR
  exact lt_of_lt_of_le hρR_unfold
    (min_le_left ((1 : ℝ) / 4)
      (min (|T| / 2)
        (Finset.inf' (Finset.range (N + 2))
          (Finset.range_nat_add_two_nonempty N)
          (fun n => Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n))))

/-- Any deletion radius below the punctured-rectangle bound is below half the
finite rectangle height.  This keeps the deleted disks away from the upper and
lower horizontal sides when `T` is positive. -/
theorem Complex.finiteAbelPlana_log_puncturedRectangle_radius_lt_height_half
    (w : ℂ)
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hρR : ρ <
      Complex.finiteAbelPlanaLogPuncturedRectangleRadiusBound w N T) :
    ρ < |T| / 2 := by
  have hρR_unfold :
      ρ <
        min ((1 : ℝ) / 4)
          (min (|T| / 2)
            (Finset.inf' (Finset.range (N + 2))
              (Finset.range_nat_add_two_nonempty N)
              (fun n =>
                Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n))) :=
    Eq.subst
      (motive := fun R : ℝ => ρ < R)
      (Complex.finiteAbelPlanaLogPuncturedRectangleRadiusBound_unfold w N T)
      hρR
  exact lt_of_lt_of_le hρR_unfold
    ((min_le_right ((1 : ℝ) / 4)
        (min (|T| / 2)
          (Finset.inf' (Finset.range (N + 2))
            (Finset.range_nat_add_two_nonempty N)
            (fun n => Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)))).trans
      (min_le_left (|T| / 2)
        (Finset.inf' (Finset.range (N + 2))
          (Finset.range_nat_add_two_nonempty N)
          (fun n => Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n))))

/-- Any deletion radius below the punctured-rectangle bound is below each local
residue-isolation radius for the integer poles in the finite rectangle. -/
theorem Complex.finiteAbelPlana_log_puncturedRectangle_radius_lt_integerResidueIsolationRadius
    (w : ℂ)
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hρR : ρ <
      Complex.finiteAbelPlanaLogPuncturedRectangleRadiusBound w N T)
    {n : ℕ}
    (hn : n ∈ Finset.range (N + 2)) :
    ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n := by
  have hρR_unfold :
      ρ <
        min ((1 : ℝ) / 4)
          (min (|T| / 2)
            (Finset.inf' (Finset.range (N + 2))
              (Finset.range_nat_add_two_nonempty N)
              (fun n =>
                Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n))) :=
    Eq.subst
      (motive := fun R : ℝ => ρ < R)
      (Complex.finiteAbelPlanaLogPuncturedRectangleRadiusBound_unfold w N T)
      hρR
  have hbound_le_inf :
      min ((1 : ℝ) / 4)
          (min (|T| / 2)
            (Finset.inf' (Finset.range (N + 2))
              (Finset.range_nat_add_two_nonempty N)
              (fun n => Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n))) ≤
        Finset.inf' (Finset.range (N + 2))
          (Finset.range_nat_add_two_nonempty N)
          (fun n => Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n) := by
    exact
      (min_le_right ((1 : ℝ) / 4)
        (min (|T| / 2)
          (Finset.inf' (Finset.range (N + 2))
            (Finset.range_nat_add_two_nonempty N)
            (fun n => Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)))).trans
        (min_le_right (|T| / 2)
          (Finset.inf' (Finset.range (N + 2))
            (Finset.range_nat_add_two_nonempty N)
            (fun n => Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)))
  have hρ_inf :
      ρ <
        Finset.inf' (Finset.range (N + 2))
          (Finset.range_nat_add_two_nonempty N)
          (fun n => Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n) :=
    lt_of_lt_of_le hρR_unfold hbound_le_inf
  exact ((Finset.lt_inf'_iff (Finset.range_nat_add_two_nonempty N)).mp hρ_inf) n hn

/-- Closed finite-height Abel-Plana rectangle in the coordinates used by
mathlib's rectangle Cauchy theorem. -/
def Complex.finiteAbelPlanaClosedRectangle
    (N : ℕ)
    (T : ℝ) : Set ℂ :=
  Set.Icc (0 : ℝ) (N + 1 : ℝ) ×ℂ Set.Icc (-T) T

/-- Open finite-height Abel-Plana rectangle. -/
def Complex.finiteAbelPlanaOpenRectangle
    (N : ℕ)
    (T : ℝ) : Set ℂ :=
  Set.Ioo (0 : ℝ) (N + 1 : ℝ) ×ℂ Set.Ioo (-T) T

/-- Finite set of integer cotangent poles in the Abel-Plana rectangle. -/
def Complex.finiteAbelPlanaIntegerPoleSet
    (N : ℕ) : Set ℂ :=
  {z : ℂ | ∃ n ∈ Finset.range (N + 2), z = (n : ℂ)}

/-- The finite Abel-Plana rectangle with small disks around all integer poles
removed. -/
def Complex.finiteAbelPlanaPuncturedRectangle
    (N : ℕ)
    (T ρ : ℝ) : Set ℂ :=
  Complex.finiteAbelPlanaClosedRectangle N T \
    ⋃ n ∈ Finset.range (N + 2), Metric.ball (n : ℂ) ρ

/-- The punctured finite Abel-Plana rectangle unfolded as the closed rectangle
minus all deleted integer-pole disks. -/
theorem Complex.finiteAbelPlanaPuncturedRectangle_unfold
    (N : ℕ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaPuncturedRectangle N T ρ =
      Complex.finiteAbelPlanaClosedRectangle N T \
        ⋃ n ∈ Finset.range (N + 2), Metric.ball (n : ℂ) ρ :=
  rfl

/-- Normalized oriented boundary integral of the finite-radius punctured
Abel-Plana rectangle.

This is the residue-free finite-radius contour object: the outer
principal-value rectangle boundary minus the true deleted-boundary
contribution from the two endpoint semicircles and the interior small circles. -/
noncomputable def Complex.finiteAbelPlanaLogFiniteRadiusPuncturedBoundaryIntegral
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
    Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ

/-- Integer poles are exactly the deleted centers used in the punctured
finite Abel-Plana rectangle. -/
theorem Complex.finiteAbelPlana_integerPoleSet_unfold
    (N : ℕ) :
    Complex.finiteAbelPlanaIntegerPoleSet N =
      {z : ℂ | ∃ n ∈ Finset.range (N + 2), z = (n : ℂ)} := by
  rfl

/-- Membership in the punctured finite Abel-Plana rectangle means membership
in the closed rectangle and avoidance of every deleted pole disk. -/
theorem Complex.mem_finiteAbelPlanaPuncturedRectangle_iff
    {N : ℕ}
    {T ρ : ℝ}
    {z : ℂ} :
    z ∈ Complex.finiteAbelPlanaPuncturedRectangle N T ρ ↔
      z ∈ Complex.finiteAbelPlanaClosedRectangle N T ∧
        ∀ n ∈ Finset.range (N + 2), z ∉ Metric.ball (n : ℂ) ρ := by
  have hunfold :
      Complex.finiteAbelPlanaPuncturedRectangle N T ρ =
        Complex.finiteAbelPlanaClosedRectangle N T \
          ⋃ n ∈ Finset.range (N + 2), Metric.ball (n : ℂ) ρ :=
    Complex.finiteAbelPlanaPuncturedRectangle_unfold N T ρ
  constructor
  · intro hz
    have hz_unfold :
        z ∈ Complex.finiteAbelPlanaClosedRectangle N T \
          ⋃ n ∈ Finset.range (N + 2), Metric.ball (n : ℂ) ρ :=
      Eq.subst
        (motive := fun S : Set ℂ => z ∈ S)
        hunfold
        hz
    exact
      And.intro
        hz_unfold.1
        (fun n hn hball =>
          hz_unfold.2
            (Set.mem_iUnion.2
              (Exists.intro n
                (Set.mem_iUnion.2
                  (Exists.intro hn hball)))))
  · intro hz
    have hz_unfold :
        z ∈ Complex.finiteAbelPlanaClosedRectangle N T \
          ⋃ n ∈ Finset.range (N + 2), Metric.ball (n : ℂ) ρ := by
      exact
        And.intro
          hz.1
          (fun hmem =>
            match Set.mem_iUnion.1 hmem with
            | Exists.intro n hnmem =>
                match Set.mem_iUnion.1 hnmem with
                | Exists.intro hn hball => hz.2 n hn hball)
    exact
      Eq.subst
        (motive := fun S : Set ℂ => z ∈ S)
        hunfold.symm
        hz_unfold

/-- A point of the punctured finite Abel-Plana rectangle still lies in the
underlying closed rectangle. -/
theorem Complex.finiteAbelPlanaPuncturedRectangle_subset_closedRectangle
    (N : ℕ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaPuncturedRectangle N T ρ ⊆
      Complex.finiteAbelPlanaClosedRectangle N T := by
  intro z hz
  exact (Complex.mem_finiteAbelPlanaPuncturedRectangle_iff.mp hz).1

/-- The center of every deleted integer-pole disk is absent from the punctured
finite Abel-Plana rectangle. -/
theorem Complex.finiteAbelPlana_integerPole_not_mem_puncturedRectangle
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    {n : ℕ}
    (hn : n ∈ Finset.range (N + 2)) :
    (n : ℂ) ∉ Complex.finiteAbelPlanaPuncturedRectangle N T ρ := by
  intro hz
  have havoid :
      ∀ m ∈ Finset.range (N + 2), (n : ℂ) ∉ Metric.ball (m : ℂ) ρ :=
    (Complex.mem_finiteAbelPlanaPuncturedRectangle_iff.mp hz).2
  exact havoid n hn (Metric.mem_ball_self hρ)

/-- Every named integer pole in the finite Abel-Plana pole set is excluded
from the punctured rectangle. -/
theorem Complex.finiteAbelPlana_integerPoleSet_disjoint_puncturedRectangle
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hρ : 0 < ρ) :
    Disjoint
      (Complex.finiteAbelPlanaIntegerPoleSet N)
      (Complex.finiteAbelPlanaPuncturedRectangle N T ρ) := by
  exact
    Set.disjoint_left.mpr
      (fun z hzpole hzrect =>
        match hzpole with
        | ⟨n, hn, hz_eq⟩ =>
            let hcenter_not :
                (n : ℂ) ∉ Complex.finiteAbelPlanaPuncturedRectangle N T ρ :=
              Complex.finiteAbelPlana_integerPole_not_mem_puncturedRectangle
                N T hρ hn
            hcenter_not (hz_eq ▸ hzrect))

/-- A punctured-rectangle point cannot be one of the integer cotangent poles
listed for the finite Abel-Plana rectangle. -/
theorem Complex.finiteAbelPlana_puncturedRectangle_not_mem_integerPoleSet
    {N : ℕ}
    {T ρ : ℝ}
    (hρ : 0 < ρ)
    {z : ℂ}
    (hzrect : z ∈ Complex.finiteAbelPlanaPuncturedRectangle N T ρ) :
    z ∉ Complex.finiteAbelPlanaIntegerPoleSet N := by
  intro hzpole
  have hdisjoint :
      Disjoint
        (Complex.finiteAbelPlanaIntegerPoleSet N)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ) :=
    Complex.finiteAbelPlana_integerPoleSet_disjoint_puncturedRectangle
      N T hρ
  exact Set.disjoint_left.mp hdisjoint hzpole hzrect

/-- A deleted disk whose radius is below the local residue-isolation radius is
contained in that isolation ball. -/
theorem Complex.finiteAbelPlana_deletedDisk_subset_integerResidueIsolationBall
    (w : ℂ)
    (n : ℕ)
    {ρ : ℝ}
    (hρR : ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n) :
    Metric.ball (n : ℂ) ρ ⊆
      Metric.ball (n : ℂ)
        (Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n) := by
  intro z hz
  exact Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hz) (le_of_lt hρR))

/-- Form of the deleted-disk isolation lemma matching the geometry package
used by the punctured rectangle theorem. -/
theorem Complex.finiteAbelPlana_deletedDisk_mem_integerResidueIsolationBall_of_geometry
    {w z : ℂ}
    {N n : ℕ}
    {T ρ : ℝ}
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ m ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w m)
    (hn : n ∈ Finset.range (N + 2))
    (hz : z ∈ Metric.ball (n : ℂ) ρ) :
    z ∈ Metric.ball (n : ℂ)
      (Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n) := by
  exact
    Complex.finiteAbelPlana_deletedDisk_subset_integerResidueIsolationBall
      w n (hdeleted_geometry.2.2 n hn) hz

/-- The logarithmic branch is safe on every deleted disk used by the punctured
rectangle construction. -/
theorem Complex.finiteAbelPlana_log_mem_slitPlane_of_mem_deletedDisk
    {w z : ℂ}
    (hw : 0 < w.re)
    {N n : ℕ}
    {T ρ : ℝ}
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ m ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w m)
    (hn : n ∈ Finset.range (N + 2))
    (hz : z ∈ Metric.ball (n : ℂ) ρ) :
    w + z ∈ Complex.slitPlane := by
  have hz_iso :
      z ∈ Metric.ball (n : ℂ)
        (Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n) :=
    Complex.finiteAbelPlana_deletedDisk_mem_integerResidueIsolationBall_of_geometry
      hdeleted_geometry hn hz
  exact
    Complex.finiteAbelPlana_log_mem_slitPlane_of_mem_integerResidueIsolationBall
      hw n hz_iso

/-- Away from the center of a deleted disk, the cotangent denominator is
nonzero.  This is the local puncture-free analytic input for each circular
indentation piece. -/
theorem Complex.finiteAbelPlana_log_sin_pi_mul_ne_zero_of_mem_deletedDisk_ne_center
    {w z : ℂ}
    (hw : 0 < w.re)
    {N n : ℕ}
    {T ρ : ℝ}
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ m ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w m)
    (hn : n ∈ Finset.range (N + 2))
    (hz : z ∈ Metric.ball (n : ℂ) ρ)
    (hzn : z ≠ (n : ℂ)) :
    Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
  have hz_iso :
      z ∈ Metric.ball (n : ℂ)
        (Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n) :=
    Complex.finiteAbelPlana_deletedDisk_mem_integerResidueIsolationBall_of_geometry
      hdeleted_geometry hn hz
  exact
    Complex.finiteAbelPlana_log_sin_pi_mul_ne_zero_of_mem_integerResidueIsolationBall
      hw n hz_iso hzn

/-- The punctured-rectangle radius bound supplies all geometric separation
facts needed by the finite-hole contour decomposition. -/
theorem Complex.finiteAbelPlana_log_puncturedRectangle_deletedDiskGeometry
    (w : ℂ)
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hρR : ρ <
      Complex.finiteAbelPlanaLogPuncturedRectangleRadiusBound w N T) :
    ρ < (1 : ℝ) / 4 ∧
      ρ < |T| / 2 ∧
        ∀ n ∈ Finset.range (N + 2),
          ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n := by
  exact
    And.intro
      (Complex.finiteAbelPlana_log_puncturedRectangle_radius_lt_quarter
        w N T hρR)
      (And.intro
        (Complex.finiteAbelPlana_log_puncturedRectangle_radius_lt_height_half
          w N T hρR)
        (fun n hn =>
          Complex.finiteAbelPlana_log_puncturedRectangle_radius_lt_integerResidueIsolationRadius
            w N T hρR hn))

/-- Points of the closed finite Abel-Plana rectangle have nonnegative real
part. -/
theorem Complex.finiteAbelPlana_closedRectangle_re_nonneg
    {N : ℕ}
    {T : ℝ}
    {z : ℂ}
    (hz : z ∈ Complex.finiteAbelPlanaClosedRectangle N T) :
    0 ≤ z.re := by
    have hzprod :
        z ∈ (Set.Icc (0 : ℝ) (N + 1 : ℝ) ×ℂ Set.Icc (-T) T) := by
      exact hz
    have hzre :
        z.re ∈ Set.Icc (0 : ℝ) (N + 1 : ℝ) := by
      exact (Complex.mem_reProdIm.mp hzprod).1
    exact hzre.1

/-- Points of the closed finite Abel-Plana rectangle have real part at most
`N + 1`. -/
theorem Complex.finiteAbelPlana_closedRectangle_re_le_right
    {N : ℕ}
    {T : ℝ}
    {z : ℂ}
    (hz : z ∈ Complex.finiteAbelPlanaClosedRectangle N T) :
    z.re ≤ (N + 1 : ℝ) := by
    have hzprod :
        z ∈ (Set.Icc (0 : ℝ) (N + 1 : ℝ) ×ℂ Set.Icc (-T) T) := by
      exact hz
    have hzre :
        z.re ∈ Set.Icc (0 : ℝ) (N + 1 : ℝ) := by
      exact (Complex.mem_reProdIm.mp hzprod).1
    exact hzre.2

/-- On the closed finite Abel-Plana rectangle, the logarithmic argument
`w + z` stays in the principal slit plane when `w` is in the right
half-plane. -/
theorem Complex.finiteAbelPlana_log_mem_slitPlane_of_mem_closedRectangle
    {w z : ℂ}
    (hw : 0 < w.re)
    {N : ℕ}
    {T : ℝ}
    (hz : z ∈ Complex.finiteAbelPlanaClosedRectangle N T) :
    w + z ∈ Complex.slitPlane := by
  have hzre_nonneg :
      0 ≤ z.re :=
    Complex.finiteAbelPlana_closedRectangle_re_nonneg hz
  have hsum_pos : 0 < (w + z).re := by
    calc
      0 < w.re + z.re := add_pos_of_pos_of_nonneg hw hzre_nonneg
      _ = (w + z).re := by
        exact (Complex.add_re w z).symm
  exact Complex.mem_slitPlane_iff_not_le_zero.2 <| by
    exact Complex.not_le_zero_iff.2 <| Or.inl hsum_pos

/-- If the cotangent denominator vanishes inside the closed finite
Abel-Plana rectangle, then the point is one of the integer pole centers
`0, ..., N + 1`. -/
theorem Complex.finiteAbelPlana_integerPole_of_sin_pi_mul_eq_zero_of_mem_closedRectangle
    {z : ℂ}
    {N : ℕ}
    {T : ℝ}
    (hzrect : z ∈ Complex.finiteAbelPlanaClosedRectangle N T)
    (hzero : Complex.sin ((Real.pi : ℂ) * z) = 0) :
    ∃ n ∈ Finset.range (N + 2), z = (n : ℂ) := by
  match Complex.sin_eq_zero_iff.mp hzero with
  | Exists.intro k hk =>
      have hpi_ne : (Real.pi : ℂ) ≠ 0 := by
        exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have hz_eq_int : z = (k : ℂ) := by
        have hmul :
            (Real.pi : ℂ) * z = (Real.pi : ℂ) * (k : ℂ) := by
          calc
            (Real.pi : ℂ) * z = (k : ℂ) * (Real.pi : ℂ) := hk
            _ = (Real.pi : ℂ) * (k : ℂ) := mul_comm (k : ℂ) (Real.pi : ℂ)
        exact mul_left_cancel₀ hpi_ne hmul
      have hk_nonneg_real : (0 : ℝ) ≤ (k : ℝ) := by
        have hzre_nonneg :
            0 ≤ z.re :=
          Complex.finiteAbelPlana_closedRectangle_re_nonneg hzrect
        have hzre_eq : z.re = (k : ℝ) := by
          exact congrArg Complex.re hz_eq_int
        exact hzre_eq ▸ hzre_nonneg
      have hk_le_right_real : (k : ℝ) ≤ (N + 1 : ℝ) := by
        have hzre_le :
            z.re ≤ (N + 1 : ℝ) :=
          Complex.finiteAbelPlana_closedRectangle_re_le_right hzrect
        have hzre_eq : z.re = (k : ℝ) := by
          exact congrArg Complex.re hz_eq_int
        exact hzre_eq ▸ hzre_le
      have hk_nonneg_int : 0 ≤ k := by
        exact Int.cast_nonneg.mp hk_nonneg_real
      let n : ℕ := k.toNat
      have hn_int : (n : ℤ) = k := by
        show ((Int.toNat k : ℕ) : ℤ) = k
        exact Int.toNat_of_nonneg hk_nonneg_int
      have hn_le : n ≤ N + 1 := by
        have hk_le_int : k ≤ (N + 1 : ℤ) := by
          have hright_cast :
              ((N + 1 : ℤ) : ℝ) = (N + 1 : ℝ) := by
            calc
              ((N + 1 : ℤ) : ℝ) =
                  ((N : ℤ) : ℝ) + ((1 : ℤ) : ℝ) :=
                Int.cast_add (N : ℤ) (1 : ℤ)
              _ = (N : ℝ) + ((1 : ℤ) : ℝ) :=
                congrArg
                  (fun x : ℝ => x + ((1 : ℤ) : ℝ))
                  (AddGroupWithOne.intCast_ofNat (R := ℝ) N)
              _ = (N : ℝ) + 1 :=
                congrArg
                  (fun x : ℝ => (N : ℝ) + x)
                  (Int.cast_one (R := ℝ))
          exact Int.cast_le.mp (hright_cast.symm ▸ hk_le_right_real)
        have hn_le_int : (n : ℤ) ≤ (N + 1 : ℤ) := by
          exact hn_int.trans_le hk_le_int
        exact Int.ofNat_le.mp hn_le_int
      have hn_range : n ∈ Finset.range (N + 2) := by
        exact Finset.mem_range.2 (Nat.lt_succ_iff.2 hn_le)
      have hcast : (n : ℂ) = (k : ℂ) := by
        exact congrArg (fun z : ℤ => (z : ℂ)) hn_int
      exact Exists.intro n (And.intro hn_range (hz_eq_int.trans hcast.symm))

/-- The punctured finite Abel-Plana rectangle avoids every cotangent pole. -/
theorem Complex.finiteAbelPlana_log_sin_pi_mul_ne_zero_of_mem_puncturedRectangle
    {z : ℂ}
    {N : ℕ}
    {T ρ : ℝ}
    (hρ : 0 < ρ)
    (hz : z ∈ Complex.finiteAbelPlanaPuncturedRectangle N T ρ) :
    Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
  intro hzero
  have hzdata :
      z ∈ Complex.finiteAbelPlanaClosedRectangle N T ∧
        ∀ n ∈ Finset.range (N + 2), z ∉ Metric.ball (n : ℂ) ρ :=
    Complex.mem_finiteAbelPlanaPuncturedRectangle_iff.mp hz
  match
    Complex.finiteAbelPlana_integerPole_of_sin_pi_mul_eq_zero_of_mem_closedRectangle
      hzdata.1 hzero with
  | Exists.intro n hndata =>
      have hn : n ∈ Finset.range (N + 2) := hndata.1
      have hz_eq : z = (n : ℂ) := hndata.2
      have hzball : z ∈ Metric.ball (n : ℂ) ρ := by
        exact hz_eq ▸ Metric.mem_ball_self hρ
      exact hzdata.2 n hn hzball

/-- On the punctured finite Abel-Plana rectangle, the logarithmic argument
stays in the principal slit plane. -/
theorem Complex.finiteAbelPlana_log_mem_slitPlane_of_mem_puncturedRectangle
    {w z : ℂ}
    (hw : 0 < w.re)
    {N : ℕ}
    {T ρ : ℝ}
    (hz : z ∈ Complex.finiteAbelPlanaPuncturedRectangle N T ρ) :
    w + z ∈ Complex.slitPlane := by
  have hzrect :
      z ∈ Complex.finiteAbelPlanaClosedRectangle N T :=
    (Complex.mem_finiteAbelPlanaPuncturedRectangle_iff.mp hz).1
  exact
    Complex.finiteAbelPlana_log_mem_slitPlane_of_mem_closedRectangle
      hw hzrect

/-- The finite Abel-Plana rectangle integrand is continuous on the punctured
finite-height rectangle. -/
theorem Complex.continuousOn_finiteAbelPlanaLogRectangleIntegrand_puncturedRectangle
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hρ : 0 < ρ) :
    ContinuousOn
      (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
      (Complex.finiteAbelPlanaPuncturedRectangle N T ρ) := by
  exact
    Complex.continuousOn_finiteAbelPlanaLogRectangleIntegrand
      (fun z hz =>
        Complex.finiteAbelPlana_log_mem_slitPlane_of_mem_puncturedRectangle
          hw hz)
      (fun z hz =>
        Complex.finiteAbelPlana_log_sin_pi_mul_ne_zero_of_mem_puncturedRectangle
          hρ hz)

/-- The finite Abel-Plana rectangle integrand is holomorphic on the punctured
finite-height rectangle. -/
theorem Complex.differentiableOn_finiteAbelPlanaLogRectangleIntegrand_puncturedRectangle
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hρ : 0 < ρ) :
    DifferentiableOn ℂ
      (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
      (Complex.finiteAbelPlanaPuncturedRectangle N T ρ) := by
  exact
    Complex.differentiableOn_finiteAbelPlanaLogRectangleIntegrand
      (fun z hz =>
        Complex.finiteAbelPlana_log_mem_slitPlane_of_mem_puncturedRectangle
          hw hz)
      (fun z hz =>
        Complex.finiteAbelPlana_log_sin_pi_mul_ne_zero_of_mem_puncturedRectangle
          hρ hz)

/-- The right-endpoint deleted-boundary arc is oriented as the left semicircle
around `N + 1`, traversed from `+iρ` to `-iρ`. -/
theorem Complex.finiteAbelPlana_log_rightEndpointSemicircle_orientation
    (N : ℕ)
    (w : ℂ)
    (ρ : ℝ) :
    Complex.finiteAbelPlanaLogRightEndpointIndentationIntegral N w ρ =
      let M : ℕ := N + 1
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  rfl

/-- The left-endpoint deleted-boundary arc is oriented as the right semicircle
around `0`, traversed from `-iρ` to `+iρ`. -/
theorem Complex.finiteAbelPlana_log_leftEndpointSemicircle_orientation
    (w : ℂ)
    (ρ : ℝ) :
    Complex.finiteAbelPlanaLogLeftEndpointIndentationIntegral w ρ =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  rfl

/-- The finite-radius deleted boundary is exactly the two endpoint
semicircles together with the positively parametrized interior deleted-circle
contributions appearing with the minus sign in the punctured-domain boundary. -/
theorem Complex.finiteAbelPlana_log_deletedBoundaryContribution_decomposition
    (N : ℕ)
    (w : ℂ)
    (ρ : ℝ) :
    Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ =
      Complex.finiteAbelPlanaLogLeftEndpointIndentationIntegral w ρ +
        Complex.finiteAbelPlanaLogRightEndpointIndentationIntegral N w ρ +
          ∑ n in Finset.range N,
            Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w (n + 1 : ℂ) ρ := by
  rfl

/-- Boundary decomposition for the finite-radius punctured Abel-Plana domain:
outer principal-value rectangle boundary minus the true deleted boundary. -/
theorem Complex.finiteAbelPlana_log_puncturedRectangle_boundaryDecomposition
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogFiniteRadiusPuncturedBoundaryIntegral N w T ρ =
      Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
        Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ := by
  rfl

/-- The punctured-boundary integral is definitionally the normalized outer
principal-value side expression minus the deleted-boundary contribution.  This
forward-oriented alias lets the Cauchy-Goursat theorem avoid unfolding the
boundary object. -/
theorem Complex.finiteAbelPlana_log_finiteRadiusPuncturedBoundaryIntegral_eq_pvNormalized_sub_deleted
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogFiniteRadiusPuncturedBoundaryIntegral N w T ρ =
      Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
        Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ := by
  exact
    Complex.finiteAbelPlana_log_puncturedRectangle_boundaryDecomposition
      N w T ρ

/-- Reverse orientation of the same definitional boundary accounting: the
normalized outer principal-value side expression minus the deleted boundary is
the named finite-radius punctured-boundary integral. -/
theorem Complex.finiteAbelPlana_log_pvNormalized_sub_deleted_eq_finiteRadiusPuncturedBoundaryIntegral
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
        Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ =
      Complex.finiteAbelPlanaLogFiniteRadiusPuncturedBoundaryIntegral N w T ρ := by
  exact
    (Complex.finiteAbelPlana_log_finiteRadiusPuncturedBoundaryIntegral_eq_pvNormalized_sub_deleted
      N w T ρ).symm

/-- The named punctured-boundary Cauchy-Goursat conclusion is equivalent to
zero cancellation of the normalized outer boundary against the deleted boundary.
This lemma isolates the orientation bookkeeping from the actual finite-hole
Cauchy-Goursat geometry. -/
theorem Complex.finiteAbelPlana_log_puncturedBoundary_zero_iff_pvNormalized_sub_deleted_zero
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogFiniteRadiusPuncturedBoundaryIntegral N w T ρ = 0 ↔
      Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
        Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ = 0 := by
  constructor
  · intro hboundary_zero
    exact
      Eq.trans
        (Complex.finiteAbelPlana_log_pvNormalized_sub_deleted_eq_finiteRadiusPuncturedBoundaryIntegral
          N w T ρ)
        hboundary_zero
  · intro hnormalized_zero
    exact
      Eq.trans
        (Complex.finiteAbelPlana_log_finiteRadiusPuncturedBoundaryIntegral_eq_pvNormalized_sub_deleted
          N w T ρ)
        hnormalized_zero

/-- If the finite-hole boundary-cancellation theorem has shown that the
normalized outer boundary and deleted boundary cancel, then the named
finite-radius punctured-boundary integral vanishes. -/
theorem Complex.finiteAbelPlana_log_finiteRadiusPuncturedBoundaryIntegral_eq_zero_of_pvNormalized_sub_deleted_eq_zero
    {N : ℕ}
    {w : ℂ}
    {T ρ : ℝ}
    (hnormalized_zero :
      Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
        Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ = 0) :
    Complex.finiteAbelPlanaLogFiniteRadiusPuncturedBoundaryIntegral N w T ρ = 0 := by
  exact
    (Complex.finiteAbelPlana_log_puncturedBoundary_zero_iff_pvNormalized_sub_deleted_zero
      N w T ρ).2 hnormalized_zero

/-- Conversely, Cauchy-Goursat vanishing of the named finite-radius
punctured-boundary integral is exactly the normalized outer-boundary/deleted
boundary cancellation statement. -/
theorem Complex.finiteAbelPlana_log_pvNormalized_sub_deleted_eq_zero_of_finiteRadiusPuncturedBoundaryIntegral_eq_zero
    {N : ℕ}
    {w : ℂ}
    {T ρ : ℝ}
    (hboundary_zero :
      Complex.finiteAbelPlanaLogFiniteRadiusPuncturedBoundaryIntegral N w T ρ = 0) :
    Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
      Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ = 0 := by
  exact
    (Complex.finiteAbelPlana_log_puncturedBoundary_zero_iff_pvNormalized_sub_deleted_zero
      N w T ρ).1 hboundary_zero

end

end LFunctions
end Boundary

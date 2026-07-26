import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ProbeInterface.ZetaAdmissibleFunction.Owner
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Boundary admissible bump functions

This file owns the first concrete bump-function machinery on the admissible
carrier. The direct goal is to provide honest compactly supported smooth probes
that can be used as local interpolation data later on.

At the moment we record the centered smooth bump on `ℝ`, its basic support and
value-at-center properties, and the resulting one-point interpolation lemma for
admissible complex-valued test functions.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped CompactlySupported ContDiff

namespace ZetaAdmissibleFunction

theorem le_of_lt_for_bump_radius {a b : ℝ} (h : a < b) : a ≤ b :=
  le_of_lt h

theorem half_dist_pos_of_ne {x y : ℝ} (hxy : x ≠ y) : 0 < dist x y / 2 :=
  half_pos (dist_pos.2 hxy)

theorem half_dist_lt_dist_of_ne {x y : ℝ} (hxy : x ≠ y) : dist x y / 2 < dist x y := by
  exact half_lt_self (dist_pos.2 hxy)

theorem half_half_dist_pos_of_ne {x y : ℝ} (hxy : x ≠ y) : 0 < dist x y / 2 / 2 :=
  half_pos (half_dist_pos_of_ne hxy)

theorem half_half_dist_lt_half_dist_of_ne {x y : ℝ} (hxy : x ≠ y) :
    dist x y / 2 / 2 < dist x y / 2 := by
  exact half_lt_self (half_dist_pos_of_ne hxy)

theorem complex_interpolation_left_value (a₁ a₂ b : ℂ) :
    a₁ * (1 : ℂ) + (a₂ - a₁ * b) * (0 : ℂ) = a₁ := by
  calc
    a₁ * (1 : ℂ) + (a₂ - a₁ * b) * (0 : ℂ) =
        a₁ + (a₂ - a₁ * b) * (0 : ℂ) := by
      exact congrArg (fun x : ℂ => x + (a₂ - a₁ * b) * (0 : ℂ)) (mul_one a₁)
    _ = a₁ + 0 := by
      exact congrArg (fun x : ℂ => a₁ + x) (mul_zero (a₂ - a₁ * b))
    _ = a₁ := add_zero a₁

theorem complex_interpolation_right_value (a₁ a₂ : ℂ) :
    a₁ * (0 : ℂ) + (a₂ - a₁ * (0 : ℂ)) * (1 : ℂ) = a₂ := by
  calc
    a₁ * (0 : ℂ) + (a₂ - a₁ * (0 : ℂ)) * (1 : ℂ) =
        0 + (a₂ - a₁ * (0 : ℂ)) * (1 : ℂ) := by
      exact congrArg (fun x : ℂ => x + (a₂ - a₁ * (0 : ℂ)) * (1 : ℂ)) (mul_zero a₁)
    _ = (a₂ - a₁ * (0 : ℂ)) * (1 : ℂ) := zero_add _
    _ = a₂ - a₁ * (0 : ℂ) := mul_one _
    _ = a₂ - 0 := by
      exact congrArg (fun x : ℂ => a₂ - x) (mul_zero a₁)
    _ = a₂ := sub_zero a₂

theorem complex_interpolation_right_value_of_zero (a₁ a₂ b : ℂ) (hb : b = 0) :
    a₁ * (0 : ℂ) + (a₂ - a₁ * b) * (1 : ℂ) = a₂ := by
  calc
    a₁ * (0 : ℂ) + (a₂ - a₁ * b) * (1 : ℂ) =
        a₁ * (0 : ℂ) + (a₂ - a₁ * (0 : ℂ)) * (1 : ℂ) := by
      exact congrArg
        (fun y : ℂ => a₁ * (0 : ℂ) + (a₂ - a₁ * y) * (1 : ℂ))
        hb
    _ = a₂ := complex_interpolation_right_value a₁ a₂

theorem half_positive_lt_self {r : ℝ} (hr : 0 < r) : r / 2 < r :=
  half_lt_self hr

theorem half_le_self_of_nonneg {r : ℝ} (hr : 0 ≤ r) : r / 2 ≤ r := by
  exact div_le_self hr one_le_two

theorem complex_ofReal_support_eq_real_support (f : ℝ → ℝ) :
    Function.support (fun x => ((f x : ℝ) : ℂ)) = Function.support f := by
  ext x
  constructor
  · intro hx
    intro hfx
    apply hx
    exact congrArg (fun y : ℝ => (y : ℂ)) hfx
  · intro hx
    intro hcx
    apply hx
    exact Complex.ofReal_eq_zero.mp hcx

theorem complex_ofReal_eq_one_of_real_eq_one {x : ℝ} (hx : x = 1) :
    ((x : ℝ) : ℂ) = (1 : ℂ) := by
  calc
    ((x : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := congrArg (fun y : ℝ => ((y : ℝ) : ℂ)) hx
    _ = (1 : ℂ) := Complex.ofReal_one

theorem complex_ofReal_eq_zero_of_real_eq_zero {x : ℝ} (hx : x = 0) :
    ((x : ℝ) : ℂ) = (0 : ℂ) := by
  calc
    ((x : ℝ) : ℂ) = ((0 : ℝ) : ℂ) := congrArg (fun y : ℝ => ((y : ℝ) : ℂ)) hx
    _ = (0 : ℂ) := Complex.ofReal_zero

theorem dist_gt_of_not_mem_closedBall {c r x : ℝ} (hx : x ∉ Metric.closedBall c r) :
    r < dist x c := by
  have hnot : ¬ dist x c ≤ r := fun hle => hx hle
  exact lt_of_not_ge hnot

/-- An explicit finite sample package for owner-level interpolation statements. -/
structure FiniteSample where
  n : ℕ
  x : Fin n → ℝ
  inj : Function.Injective x

/-- A centered smooth bump on the real line, packaged as an admissible function.

The function is the usual `ContDiffBump` profile on `ℝ`, viewed as a complex-valued
compactly supported smooth test function.
-/
def admissibleBump (c rIn rOut : ℝ) (hrIn : 0 < rIn) (hr : rIn < rOut) :
    ZetaAdmissibleFunction where
  toZetaTestFunction :=
    CompactlySupportedContinuousMap.mk
      (ContinuousMap.mk
        (fun x => (((⟨rIn, rOut, hrIn, hr⟩ : ContDiffBump c) x : ℝ) : ℂ))
        (Complex.continuous_ofReal.comp
          (ContDiffBump.continuous (f := (⟨rIn, rOut, hrIn, hr⟩ : ContDiffBump c)))))
      (by
        let b : ContDiffBump c := ⟨rIn, rOut, hrIn, hr⟩
        have hb : HasCompactSupport (fun x => b x) :=
          ContDiffBump.hasCompactSupport (f := b)
        have hsupport :
            Function.support (fun x => ((b x : ℝ) : ℂ)) = Function.support (fun x => b x) := by
          exact complex_ofReal_support_eq_real_support (fun x => b x)
        unfold HasCompactSupport at hb ⊢
        unfold tsupport at hb ⊢
        exact Eq.subst (motive := fun s : Set ℝ => IsCompact (closure s)) hsupport.symm hb)
  smooth := by
    have hreal := ContDiffBump.contDiff
      (f := (⟨rIn, rOut, hrIn, hr⟩ : ContDiffBump c))
      (n := ⊤)
    have hreal' :
        ContDiff ℝ ∞ (fun x : ℝ => ((⟨rIn, rOut, hrIn, hr⟩ : ContDiffBump c) x : ℝ)) := by
      exact hreal
    exact Complex.ofRealCLM.contDiff.comp hreal'

/-- The admissible bump evaluates to `1` at its center. -/
theorem admissibleBump_apply_center (c rIn rOut : ℝ) (hrIn : 0 < rIn) (hr : rIn < rOut) :
    admissibleBump (c := c) rIn rOut hrIn hr c = (1 : ℂ) := by
  change (((⟨rIn, rOut, hrIn, hr⟩ : ContDiffBump c) c : ℝ) : ℂ) = (1 : ℂ)
  exact complex_ofReal_eq_one_of_real_eq_one
    (ContDiffBump.one_of_mem_closedBall (f := (⟨rIn, rOut, hrIn, hr⟩ : ContDiffBump c))
      (Metric.mem_closedBall_self hrIn.le))

/-- The admissible bump has compact support. -/
theorem admissibleBump_hasCompactSupport (c rIn rOut : ℝ) (hrIn : 0 < rIn) (hr : rIn < rOut) :
    HasCompactSupport (admissibleBump (c := c) rIn rOut hrIn hr) := by
  exact (admissibleBump (c := c) rIn rOut hrIn hr).hasCompactSupport

/-- The admissible bump vanishes outside its outer radius. -/
theorem admissibleBump_zero_of_le_dist (c rIn rOut : ℝ) (hrIn : 0 < rIn) (hr : rIn < rOut)
    {x : ℝ} (hx : rOut ≤ dist x c) :
    admissibleBump (c := c) rIn rOut hrIn hr x = 0 := by
  change (((⟨rIn, rOut, hrIn, hr⟩ : ContDiffBump c) x : ℝ) : ℂ) = (0 : ℂ)
  exact complex_ofReal_eq_zero_of_real_eq_zero
    (ContDiffBump.zero_of_le_dist (f := (⟨rIn, rOut, hrIn, hr⟩ : ContDiffBump c)) hx)

/-- The admissible bump vanishes away from the closed `rOut`-ball around its center. -/
theorem admissibleBump_eq_zero_of_not_mem_closedBall (c rIn rOut : ℝ) (hrIn : 0 < rIn)
    (hr : rIn < rOut) {x : ℝ} (hx : x ∉ Metric.closedBall c rOut) :
    admissibleBump (c := c) rIn rOut hrIn hr x = 0 := by
  have hdist : rOut < dist x c := dist_gt_of_not_mem_closedBall hx
  exact admissibleBump_zero_of_le_dist (c := c) (rIn := rIn) (rOut := rOut) hrIn hr (by
    exact le_of_lt_for_bump_radius hdist)

/-- The admissible bump is smooth. -/
theorem admissibleBump_contDiff (c rIn rOut : ℝ) (hrIn : 0 < rIn) (hr : rIn < rOut) :
    ContDiff ℝ ∞ (admissibleBump (c := c) rIn rOut hrIn hr) := by
  exact (admissibleBump (c := c) rIn rOut hrIn hr).contDiff

/-- A one-point interpolation theorem for admissible functions.

Given a target complex value `a`, we can realize it as the value of an admissible
function at any prescribed real point.
-/
theorem exists_admissible_eval_eq (c : ℝ) (a : ℂ) :
    ∃ f : ZetaAdmissibleFunction, f c = a := by
  let b : ZetaAdmissibleFunction := admissibleBump (c := c) 1 2 zero_lt_one one_lt_two
  exact Exists.intro (a • b)
    (by
      change a * b c = a
      calc
        a * b c = a * (1 : ℂ) := by
          congr
          exact admissibleBump_apply_center (c := c) (rIn := 1) (rOut := 2)
            zero_lt_one one_lt_two
        _ = a := by
          exact mul_one a)

/-- Two prescribed values can be interpolated at two distinct real points. -/
theorem exists_admissible_eval_pair (c₁ c₂ : ℝ) (hc : c₁ ≠ c₂) (a₁ a₂ : ℂ) :
    ∃ f : ZetaAdmissibleFunction, f c₁ = a₁ ∧ f c₂ = a₂ := by
  have hdist : 0 < dist c₁ c₂ := dist_pos.2 hc
  let rOut : ℝ := dist c₁ c₂ / 2
  have hrOut_pos : 0 < rOut := by
    unfold rOut
    exact half_dist_pos_of_ne hc
  have hrOut_lt : rOut < dist c₁ c₂ := by
    unfold rOut
    exact half_dist_lt_dist_of_ne hc
  let b₁ : ZetaAdmissibleFunction := admissibleBump (c := c₁) (rOut / 2) rOut (by
    exact half_pos hrOut_pos) (by
    exact half_positive_lt_self hrOut_pos)
  let b₂ : ZetaAdmissibleFunction := admissibleBump (c := c₂) (rOut / 2) rOut (by
    exact half_pos hrOut_pos) (by
    exact half_positive_lt_self hrOut_pos)
  have hb₁₁ : b₁ c₁ = (1 : ℂ) := by
    exact admissibleBump_apply_center (c := c₁) (rIn := rOut / 2) (rOut := rOut)
      (half_pos hrOut_pos) (half_positive_lt_self hrOut_pos)
  have hb₁₂ : b₁ c₂ = 0 := by
    have hdist' : rOut ≤ dist c₂ c₁ := by
      have : rOut ≤ dist c₁ c₂ := le_of_lt_for_bump_radius hrOut_lt
      exact (dist_comm c₁ c₂) ▸ this
    exact admissibleBump_zero_of_le_dist (c := c₁) (rIn := rOut / 2) (rOut := rOut)
      (half_pos hrOut_pos) (half_positive_lt_self hrOut_pos) hdist'
  have hb₂₂ : b₂ c₂ = (1 : ℂ) := by
    exact admissibleBump_apply_center (c := c₂) (rIn := rOut / 2) (rOut := rOut)
      (half_pos hrOut_pos) (half_positive_lt_self hrOut_pos)
  have hb₂₁ : b₂ c₁ = 0 := by
    have hdist' : rOut ≤ dist c₁ c₂ := by
      exact le_of_lt_for_bump_radius hrOut_lt
    exact admissibleBump_zero_of_le_dist (c := c₂) (rIn := rOut / 2) (rOut := rOut)
      (half_pos hrOut_pos) (half_positive_lt_self hrOut_pos) hdist'
  exact Exists.intro (a₁ • b₁ + (a₂ - a₁ * b₁ c₂) • b₂)
    (And.intro
      (by
        calc
          (a₁ • b₁ + (a₂ - a₁ * b₁ c₂) • b₂) c₁ =
              a₁ * b₁ c₁ + (a₂ - a₁ * b₁ c₂) * b₂ c₁ := by
            rfl
          _ = a₁ := by
            calc
              a₁ * b₁ c₁ + (a₂ - a₁ * b₁ c₂) * b₂ c₁ =
                  a₁ * (1 : ℂ) + (a₂ - a₁ * b₁ c₂) * b₂ c₁ := by
                exact congrArg
                  (fun y : ℂ => a₁ * y + (a₂ - a₁ * b₁ c₂) * b₂ c₁)
                  hb₁₁
              _ = a₁ * (1 : ℂ) + (a₂ - a₁ * b₁ c₂) * (0 : ℂ) := by
                exact congrArg
                  (fun y : ℂ => a₁ * (1 : ℂ) + (a₂ - a₁ * b₁ c₂) * y)
                  hb₂₁
              _ = a₁ := complex_interpolation_left_value a₁ a₂ (b₁ c₂))
      (by
        calc
          (a₁ • b₁ + (a₂ - a₁ * b₁ c₂) • b₂) c₂ =
              a₁ * b₁ c₂ + (a₂ - a₁ * b₁ c₂) * b₂ c₂ := by
            rfl
          _ = a₂ := by
            calc
              a₁ * b₁ c₂ + (a₂ - a₁ * b₁ c₂) * b₂ c₂ =
                  a₁ * (0 : ℂ) + (a₂ - a₁ * b₁ c₂) * b₂ c₂ := by
                exact congrArg
                  (fun y : ℂ => a₁ * y + (a₂ - a₁ * b₁ c₂) * b₂ c₂)
                  hb₁₂
              _ = a₁ * (0 : ℂ) + (a₂ - a₁ * b₁ c₂) * (1 : ℂ) := by
                exact congrArg
                  (fun y : ℂ => a₁ * (0 : ℂ) + (a₂ - a₁ * b₁ c₂) * y)
                  hb₂₂
              _ = a₂ := complex_interpolation_right_value_of_zero a₁ a₂ (b₁ c₂) hb₁₂))

/-- The support of the admissible bump is contained in the closed outer ball. -/
theorem admissibleBump_support_subset_closedBall (c rIn rOut : ℝ) (hrIn : 0 < rIn)
    (hr : rIn < rOut) :
    Function.support (admissibleBump (c := c) rIn rOut hrIn hr) ⊆ Metric.closedBall c rOut := by
  intro x hx
  let b : ContDiffBump c := ⟨rIn, rOut, hrIn, hr⟩
  have hsupport :
      Function.support (fun x => ((b x : ℝ) : ℂ)) = Function.support (fun x => b x) :=
    complex_ofReal_support_eq_real_support (fun x => b x)
  change x ∈ Function.support (fun x => ((b x : ℝ) : ℂ)) at hx
  have hxReal : x ∈ Function.support (fun x => b x) :=
    Eq.subst (motive := fun s : Set ℝ => x ∈ s) hsupport hx
  have hbSupport : Function.support (fun x => b x) = Metric.ball c rOut :=
    ContDiffBump.support_eq (f := b)
  have hxBall : x ∈ Metric.ball c rOut :=
    Eq.subst (motive := fun s : Set ℝ => x ∈ s) hbSupport hxReal
  show dist x c ≤ rOut
  exact le_of_lt (show dist x c < rOut from hxBall)

theorem sampleDistanceImage_nonempty_of_ne_empty (S : FiniteSample) (i₀ : Fin S.n)
    {s : Finset (Fin S.n)} (hne : s ≠ ∅) :
    (s.image fun j => dist (S.x j) (S.x i₀)).Nonempty := by
  match Finset.nonempty_iff_ne_empty.mpr hne with
  | ⟨j, hj⟩ =>
      exact ⟨dist (S.x j) (S.x i₀), Finset.mem_image.2 ⟨j, hj, rfl⟩⟩

theorem sampleDistanceImage_min_pos_of_erase (S : FiniteSample) (i₀ : Fin S.n)
    (s : Finset (Fin S.n)) (hs : i₀ ∉ s) (ht : (s.image fun j => dist (S.x j) (S.x i₀)).Nonempty) :
    0 < (s.image fun j => dist (S.x j) (S.x i₀)).min' ht := by
  have hm : (s.image fun j => dist (S.x j) (S.x i₀)).min' ht ∈
      (s.image fun j => dist (S.x j) (S.x i₀)) := Finset.min'_mem _ _
  match Finset.mem_image.1 hm with
  | ⟨j, hj, hjdist⟩ =>
      have hneq : j ≠ i₀ := by
        intro hji
        exact hs (Eq.subst (motive := fun k : Fin S.n => k ∈ s) hji hj)
      exact hjdist.symm ▸ dist_pos.2 (S.inj.ne hneq)

/-- The explicit separation radius for one point of a finite sample. -/
def sampleSeparationRadius (S : FiniteSample) (i₀ : Fin S.n) : ℝ :=
  let s : Finset (Fin S.n) := Finset.univ.erase i₀
  if hne : s = ∅ then
    1
  else
    let t : Finset ℝ := s.image fun j => dist (S.x j) (S.x i₀)
    have ht : t.Nonempty := sampleDistanceImage_nonempty_of_ne_empty S i₀ hne
    t.min' ht / 2

/-- The explicit separation radius is positive and below every other sample-point distance. -/
theorem sampleSeparationRadius_pos_and_le (S : FiniteSample) (i₀ : Fin S.n) :
    0 < sampleSeparationRadius S i₀ ∧
      ∀ j ∈ (Finset.univ.erase i₀),
        sampleSeparationRadius S i₀ ≤ dist (S.x j) (S.x i₀) := by
  let s : Finset (Fin S.n) := Finset.univ.erase i₀
  have hs : i₀ ∉ s := by
    unfold s
    exact Finset.not_mem_erase i₀ (Finset.univ : Finset (Fin S.n))
  by_cases hne : s = ∅
  · constructor
    · have hrad : sampleSeparationRadius S i₀ = 1 := by
        unfold sampleSeparationRadius
        change (if h : s = ∅ then (1 : ℝ) else
          let t : Finset ℝ := Finset.image (fun j => dist (S.x j) (S.x i₀)) s
          let ht : t.Nonempty := sampleDistanceImage_nonempty_of_ne_empty S i₀ h
          t.min' ht / 2) = 1
        exact dif_pos hne
      exact Eq.subst (motive := fun r : ℝ => 0 < r) hrad.symm zero_lt_one
    intro j hj
    have hjs : j ∈ s := hj
    have hfalse : j ∈ (∅ : Finset (Fin S.n)) := by
      exact hne ▸ hjs
    exact False.elim (Finset.not_mem_empty j hfalse)
  · let t : Finset ℝ := s.image fun j => dist (S.x j) (S.x i₀)
    have ht : t.Nonempty := sampleDistanceImage_nonempty_of_ne_empty S i₀ hne
    have hpos : 0 < t.min' ht := sampleDistanceImage_min_pos_of_erase S i₀ s hs ht
    constructor
    · unfold sampleSeparationRadius
      change 0 <
        (if h : s = ∅ then (1 : ℝ) else
          let t : Finset ℝ := Finset.image (fun j => dist (S.x j) (S.x i₀)) s
          let ht : t.Nonempty := sampleDistanceImage_nonempty_of_ne_empty S i₀ h
          t.min' ht / 2)
      exact Eq.subst (motive := fun r : ℝ => 0 < r) (dif_neg hne).symm (half_pos hpos)
    intro j hj
    unfold sampleSeparationRadius
    change
      (if h : s = ∅ then (1 : ℝ) else
        let t : Finset ℝ := Finset.image (fun j => dist (S.x j) (S.x i₀)) s
        let ht : t.Nonempty := sampleDistanceImage_nonempty_of_ne_empty S i₀ h
        t.min' ht / 2) ≤ dist (S.x j) (S.x i₀)
    have hmem : dist (S.x j) (S.x i₀) ∈ t := by
      exact Finset.mem_image.2 ⟨j, hj, rfl⟩
    have hle : t.min' ht ≤ dist (S.x j) (S.x i₀) := Finset.min'_le _ _ hmem
    exact Eq.subst (motive := fun r : ℝ => r ≤ dist (S.x j) (S.x i₀))
      (dif_neg hne).symm
      (le_trans (half_le_self_of_nonneg (le_of_lt hpos)) hle)

/-- A finite sample can be separated from any one of its other indexed points by a positive radius. -/
theorem exists_radius_separating_sample (S : FiniteSample) (i₀ : Fin S.n) :
    ∃ rOut : ℝ, 0 < rOut ∧
      ∀ j ∈ (Finset.univ.erase i₀), rOut ≤ dist (S.x j) (S.x i₀) := by
  exact ⟨sampleSeparationRadius S i₀, (sampleSeparationRadius_pos_and_le S i₀).1,
    (sampleSeparationRadius_pos_and_le S i₀).2⟩

/-- A finite sample admits a Kronecker-delta family with closed-ball support control. -/
theorem exists_admissible_delta_sample_with_closedBall_support (S : FiniteSample) :
    ∃ F : ∀ _i, ZetaAdmissibleFunction,
      (∀ i, F i (S.x i) = (1 : ℂ)) ∧
      (∀ i j, j ≠ i → F i (S.x j) = 0) ∧
      (∀ i, ∃ rOut : ℝ, 0 < rOut ∧
        Function.support (F i) ⊆ Metric.closedBall (S.x i) rOut) := by
  let rOut : Fin S.n → ℝ := fun i => sampleSeparationRadius S i
  let F : ∀ i, ZetaAdmissibleFunction := fun i =>
    admissibleBump (c := S.x i) (rOut i / 2) (rOut i)
      (half_pos (sampleSeparationRadius_pos_and_le S i).1)
      (half_positive_lt_self (sampleSeparationRadius_pos_and_le S i).1)
  exact Exists.intro F
    (And.intro
      (fun i =>
        admissibleBump_apply_center (c := S.x i) (rIn := rOut i / 2)
          (rOut := rOut i) (half_pos (sampleSeparationRadius_pos_and_le S i).1)
          (half_positive_lt_self (sampleSeparationRadius_pos_and_le S i).1))
      (And.intro
        (fun i j hj =>
          have hj' : j ∈ Finset.univ.erase i :=
            Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩
          admissibleBump_zero_of_le_dist (c := S.x i) (rIn := rOut i / 2)
            (rOut := rOut i) (half_pos (sampleSeparationRadius_pos_and_le S i).1)
            (half_positive_lt_self (sampleSeparationRadius_pos_and_le S i).1)
            ((sampleSeparationRadius_pos_and_le S i).2 j hj'))
        (fun i =>
          Exists.intro (rOut i)
            (And.intro (sampleSeparationRadius_pos_and_le S i).1
              (admissibleBump_support_subset_closedBall (c := S.x i)
                (rIn := rOut i / 2) (rOut := rOut i)
                (half_pos (sampleSeparationRadius_pos_and_le S i).1)
                (half_positive_lt_self (sampleSeparationRadius_pos_and_le S i).1))))))

/-- A finite sample admits a Kronecker-delta family with compact support. -/
theorem exists_admissible_delta_sample_with_support (S : FiniteSample) :
    ∃ F : ∀ _i, ZetaAdmissibleFunction,
      (∀ i, F i (S.x i) = (1 : ℂ)) ∧
      (∀ i j, j ≠ i → F i (S.x j) = 0) ∧
      (∀ i, HasCompactSupport (F i)) := by
  exact
    match exists_admissible_delta_sample_with_closedBall_support S with
    | ⟨F, hF1, hF0, hFr⟩ =>
        Exists.intro F
          (And.intro hF1
            (And.intro hF0
              (fun i => (F i).hasCompactSupport)))

/-- The sample interpolant assembled from a delta family. -/
def sampleInterpolant (S : FiniteSample) (a : Fin S.n → ℂ)
    (F : (i : Fin S.n) → ZetaAdmissibleFunction) : ZetaAdmissibleFunction :=
  Finset.sum Finset.univ fun i => (a i) • F i

/-- The sample interpolant has the prescribed sample values. -/
theorem sampleInterpolant_apply (S : FiniteSample) (a : Fin S.n → ℂ)
    (F : (i : Fin S.n) → ZetaAdmissibleFunction)
    (hF1 : ∀ i, F i (S.x i) = (1 : ℂ))
    (hF0 : ∀ i j, j ≠ i → F i (S.x j) = 0) (i : Fin S.n) :
    sampleInterpolant S a F (S.x i) = a i := by
  have hsum :
      sampleInterpolant S a F (S.x i) =
        ∑ j : Fin S.n, a j * F j (S.x i) := by
    change (∑ j : Fin S.n, (a j • F j)) (S.x i) =
      ∑ j : Fin S.n, a j * F j (S.x i)
    calc
      (∑ j : Fin S.n, (a j • F j)) (S.x i) =
          ∑ j : Fin S.n, (a j • F j) (S.x i) := by
        exact ZetaAdmissibleFunction.sum_apply
          (s := Finset.univ)
          (f := fun j : Fin S.n => a j • F j)
          (S.x i)
      _ = ∑ j : Fin S.n, a j * F j (S.x i) := by
        exact Finset.sum_congr rfl
          (fun j hj =>
            (fun hmem : j ∈ (Finset.univ : Finset (Fin S.n)) =>
              ZetaAdmissibleFunction.smul_apply (a j) (F j) (S.x i)) hj)
  have hsum' := hsum
  have hsingle :
      (∑ j : Fin S.n, a j * F j (S.x i)) = a i * F i (S.x i) := by
    exact Finset.sum_eq_single i
      (fun j hj hji =>
        (fun hmem : j ∈ (Finset.univ : Finset (Fin S.n)) =>
          have hzero : F j (S.x i) = 0 := hF0 j i hji.symm
          calc
            a j * F j (S.x i) = a j * 0 := congrArg (fun x => a j * x) hzero
            _ = 0 := by exact mul_zero (a j)) hj)
      (fun hi => False.elim (hi (Finset.mem_univ i)))
  change sampleInterpolant S a F (S.x i) = a i
  calc
    sampleInterpolant S a F (S.x i) =
        ∑ j : Fin S.n, a j * F j (S.x i) := hsum
    _ = a i * F i (S.x i) := hsingle
    _ = a i := by
      have hone : F i (S.x i) = (1 : ℂ) := hF1 i
      calc
        a i * F i (S.x i) = a i * (1 : ℂ) := congrArg (fun x => a i * x) hone
        _ = a i := by exact mul_one (a i)

/-- The sample interpolant assembled from admissible probes has compact support. -/
theorem sampleInterpolant_hasCompactSupport (S : FiniteSample) (a : Fin S.n → ℂ)
    (F : (i : Fin S.n) → ZetaAdmissibleFunction) :
    HasCompactSupport (sampleInterpolant S a F) := by
  exact (sampleInterpolant S a F).hasCompactSupport

/-- The sample interpolant support is contained in the union of the delta-basis supports. -/
theorem sampleInterpolant_support_subset_iUnion (S : FiniteSample) (a : Fin S.n → ℂ)
    (F : (i : Fin S.n) → ZetaAdmissibleFunction) :
    Function.support (sampleInterpolant S a F) ⊆ Set.iUnion fun i => Function.support (F i) := by
  intro y hy
  unfold sampleInterpolant at hy
  have hsupport :
      Function.support ⇑(∑ i : Fin S.n, (a i) • F i).toZetaTestFunction =
        Function.support (fun x => ∑ i : Fin S.n, ((a i) • F i) x) :=
    ZetaAdmissibleFunction.support_sum_apply
      (s := Finset.univ)
      (f := fun i : Fin S.n => (a i) • F i)
  have hy' : y ∈ Function.support (fun x => ∑ i : Fin S.n, ((a i) • F i) x) := by
    exact hsupport ▸ hy
  have hyne : ∃ i ∈ (Finset.univ : Finset (Fin S.n)), ((a i) • F i) y ≠ 0 := by
    exact Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
      (f := fun i => ((a i) • F i) y) hy'
  rcases hyne with ⟨i, _hi, hyFi⟩
  exact Set.mem_iUnion.2 ⟨i, ZetaAdmissibleFunction.support_smul_subset (a i) (F i) hyFi⟩

/-- A finite sample admits an admissible interpolant. -/
theorem exists_admissible_eval_sample (S : FiniteSample) (a : Fin S.n → ℂ) :
    ∃ f : ZetaAdmissibleFunction, ∀ i, f (S.x i) = a i := by
  exact
    match exists_admissible_delta_sample_with_support S with
    | ⟨F, hF1, hF0, hFc⟩ =>
        Exists.intro (sampleInterpolant S a F)
          (fun i => sampleInterpolant_apply S a F hF1 hF0 i)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ProbeInterface.ZetaAdmissibleFunction.ZetaAdmissibleFunction
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
          ext x
          simp [Function.mem_support]
        unfold HasCompactSupport at hb ⊢
        rw [tsupport, hsupport]
        exact hb)
  smooth := by
    have hreal := ContDiffBump.contDiff
      (f := (⟨rIn, rOut, hrIn, hr⟩ : ContDiffBump c))
      (n := ⊤)
    have hreal' :
        ContDiff ℝ ∞ (fun x : ℝ => ((⟨rIn, rOut, hrIn, hr⟩ : ContDiffBump c) x : ℝ)) := by
      simpa [ContDiffBump.toFun] using hreal
    exact Complex.ofRealCLM.contDiff.comp hreal'

/-- The admissible bump evaluates to `1` at its center. -/
theorem admissibleBump_apply_center (c rIn rOut : ℝ) (hrIn : 0 < rIn) (hr : rIn < rOut) :
    admissibleBump (c := c) rIn rOut hrIn hr c = (1 : ℂ) := by
  change (((⟨rIn, rOut, hrIn, hr⟩ : ContDiffBump c) c : ℝ) : ℂ) = (1 : ℂ)
  exact_mod_cast
    ContDiffBump.one_of_mem_closedBall (f := (⟨rIn, rOut, hrIn, hr⟩ : ContDiffBump c))
      (Metric.mem_closedBall_self hrIn.le)

/-- The admissible bump has compact support. -/
theorem admissibleBump_hasCompactSupport (c rIn rOut : ℝ) (hrIn : 0 < rIn) (hr : rIn < rOut) :
    HasCompactSupport (admissibleBump (c := c) rIn rOut hrIn hr) := by
  exact (admissibleBump (c := c) rIn rOut hrIn hr).hasCompactSupport

/-- The admissible bump vanishes outside its outer radius. -/
theorem admissibleBump_zero_of_le_dist (c rIn rOut : ℝ) (hrIn : 0 < rIn) (hr : rIn < rOut)
    {x : ℝ} (hx : rOut ≤ dist x c) :
    admissibleBump (c := c) rIn rOut hrIn hr x = 0 := by
  change (((⟨rIn, rOut, hrIn, hr⟩ : ContDiffBump c) x : ℝ) : ℂ) = (0 : ℂ)
  exact_mod_cast
    ContDiffBump.zero_of_le_dist (f := (⟨rIn, rOut, hrIn, hr⟩ : ContDiffBump c)) hx

/-- The admissible bump vanishes away from the closed `rOut`-ball around its center. -/
theorem admissibleBump_eq_zero_of_not_mem_closedBall (c rIn rOut : ℝ) (hrIn : 0 < rIn)
    (hr : rIn < rOut) {x : ℝ} (hx : x ∉ Metric.closedBall c rOut) :
    admissibleBump (c := c) rIn rOut hrIn hr x = 0 := by
  have hdist : rOut < dist x c := by
    exact lt_of_not_ge (fun h => hx (by simpa [Metric.mem_closedBall] using h))
  exact admissibleBump_zero_of_le_dist (c := c) (rIn := rIn) (rOut := rOut) hrIn hr (by
    linarith [le_of_lt hdist])

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
  refine ⟨a • b, ?_⟩
  rw [ZetaAdmissibleFunction.smul_apply, admissibleBump_apply_center]
  exact mul_one a

/-- Two prescribed values can be interpolated at two distinct real points. -/
theorem exists_admissible_eval_pair (c₁ c₂ : ℝ) (hc : c₁ ≠ c₂) (a₁ a₂ : ℂ) :
    ∃ f : ZetaAdmissibleFunction, f c₁ = a₁ ∧ f c₂ = a₂ := by
  have hdist : 0 < dist c₁ c₂ := dist_pos.2 hc
  let rOut : ℝ := dist c₁ c₂ / 2
  have hrOut_pos : 0 < rOut := by dsimp [rOut]; linarith
  have hrOut_lt : rOut < dist c₁ c₂ := by dsimp [rOut]; linarith
  let b₁ : ZetaAdmissibleFunction := admissibleBump (c := c₁) (rOut / 2) rOut (by
    dsimp [rOut]
    linarith) (by linarith)
  let b₂ : ZetaAdmissibleFunction := admissibleBump (c := c₂) (rOut / 2) rOut (by
    dsimp [rOut]
    linarith) (by linarith)
  have hb₁₁ : b₁ c₁ = (1 : ℂ) := by simp [b₁, admissibleBump_apply_center]
  have hb₁₂ : b₁ c₂ = 0 := by
    exact admissibleBump_zero_of_le_dist (c := c₁) (rIn := rOut / 2) (rOut := rOut)
      (by linarith) (by linarith) (le_of_lt (by simpa [rOut, dist_comm] using hrOut_lt))
  have hb₂₂ : b₂ c₂ = (1 : ℂ) := by simp [b₂, admissibleBump_apply_center]
  have hb₂₁ : b₂ c₁ = 0 := by
    exact admissibleBump_zero_of_le_dist (c := c₂) (rIn := rOut / 2) (rOut := rOut)
      (by linarith) (by linarith) (le_of_lt (by simpa [rOut, dist_comm] using hrOut_lt))
  refine
    ⟨a₁ • b₁ + (a₂ - a₁ * b₁ c₂) • b₂, ?_⟩
  constructor
  · simp [add_apply, smul_apply, hb₁₁, hb₂₁]
  · simp [add_apply, smul_apply, hb₁₂, hb₂₂]

/-- The support of the admissible bump is contained in the closed outer ball. -/
theorem admissibleBump_support_subset_closedBall (c rIn rOut : ℝ) (hrIn : 0 < rIn)
    (hr : rIn < rOut) :
    Function.support (admissibleBump (c := c) rIn rOut hrIn hr) ⊆ Metric.closedBall c rOut := by
  intro x hx
  by_contra hx'
  exact hx (by
    simpa [Function.mem_support] using
      admissibleBump_eq_zero_of_not_mem_closedBall (c := c) (rIn := rIn) (rOut := rOut) hrIn hr hx')

/-- The explicit separation radius for one point of a finite sample. -/
def sampleSeparationRadius (S : FiniteSample) (i₀ : Fin S.n) : ℝ :=
  let s : Finset (Fin S.n) := Finset.univ.erase i₀
  if hne : s = ∅ then
    1
  else
    let t : Finset ℝ := s.image fun j => dist (S.x j) (S.x i₀)
    have ht : t.Nonempty := by
      rcases Finset.nonempty_iff_ne_empty.mpr hne with ⟨j, hj⟩
      exact ⟨dist (S.x j) (S.x i₀), Finset.mem_image.2 ⟨j, hj, rfl⟩⟩
    t.min' ht / 2

/-- The explicit separation radius is positive and below every other sample-point distance. -/
theorem sampleSeparationRadius_pos_and_le (S : FiniteSample) (i₀ : Fin S.n) :
    0 < sampleSeparationRadius S i₀ ∧
      ∀ j ∈ (Finset.univ.erase i₀),
        sampleSeparationRadius S i₀ ≤ dist (S.x j) (S.x i₀) := by
  let s : Finset (Fin S.n) := Finset.univ.erase i₀
  have hs : i₀ ∉ s := by
    dsimp [s]
    simp
  by_cases hne : s = ∅
  · constructor
    · dsimp [sampleSeparationRadius, s]
      rw [dif_pos hne]
      exact zero_lt_one
    intro j hj
    have hjs : j ∈ s := by
      simpa [s] using hj
    have hfalse : j ∈ (∅ : Finset (Fin S.n)) := by
      rw [hne] at hjs
      exact hjs
    exact False.elim (Finset.not_mem_empty j hfalse)
  · let t : Finset ℝ := s.image fun j => dist (S.x j) (S.x i₀)
    have ht : t.Nonempty := by
      rcases Finset.nonempty_iff_ne_empty.mpr hne with ⟨j, hj⟩
      refine ⟨dist (S.x j) (S.x i₀), ?_⟩
      exact Finset.mem_image.2 ⟨j, hj, rfl⟩
    have hpos : 0 < t.min' ht := by
      have hm : t.min' ht ∈ t := Finset.min'_mem _ _
      rcases Finset.mem_image.1 hm with ⟨j, hj, hjdist⟩
      have hneq : j ≠ i₀ := by
        intro hji
        apply hs
        simpa [hji] using hj
      rw [← hjdist]
      exact dist_pos.2 (S.inj.ne hneq)
    constructor
    · dsimp [sampleSeparationRadius, s, t]
      rw [dif_neg hne]
      exact half_pos hpos
    intro j hj
    dsimp [sampleSeparationRadius, s, t]
    rw [dif_neg hne]
    have hmem : dist (S.x j) (S.x i₀) ∈ t := by
      exact Finset.mem_image.2 ⟨j, hj, rfl⟩
    have hle : t.min' ht ≤ dist (S.x j) (S.x i₀) := Finset.min'_le _ _ hmem
    linarith

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
      (by linarith [(sampleSeparationRadius_pos_and_le S i).1])
  refine ⟨F, ?_, ?_, ?_⟩
  · intro i
    exact admissibleBump_apply_center (c := S.x i) (rIn := rOut i / 2)
      (rOut := rOut i) (half_pos (sampleSeparationRadius_pos_and_le S i).1)
      (by linarith [(sampleSeparationRadius_pos_and_le S i).1])
  · intro i j hj
    have hj' : j ∈ Finset.univ.erase i := by simp [hj]
    exact admissibleBump_zero_of_le_dist (c := S.x i) (rIn := rOut i / 2)
      (rOut := rOut i) (half_pos (sampleSeparationRadius_pos_and_le S i).1)
      (by linarith [(sampleSeparationRadius_pos_and_le S i).1])
      ((sampleSeparationRadius_pos_and_le S i).2 j hj')
  · intro i
    exact ⟨rOut i, (sampleSeparationRadius_pos_and_le S i).1,
      admissibleBump_support_subset_closedBall (c := S.x i) (rIn := rOut i / 2)
        (rOut := rOut i) (half_pos (sampleSeparationRadius_pos_and_le S i).1)
        (by linarith [(sampleSeparationRadius_pos_and_le S i).1])⟩

/-- A finite sample admits a Kronecker-delta family with compact support. -/
theorem exists_admissible_delta_sample_with_support (S : FiniteSample) :
    ∃ F : ∀ _i, ZetaAdmissibleFunction,
      (∀ i, F i (S.x i) = (1 : ℂ)) ∧
      (∀ i j, j ≠ i → F i (S.x j) = 0) ∧
      (∀ i, HasCompactSupport (F i)) := by
  rcases exists_admissible_delta_sample_with_closedBall_support S with ⟨F, hF1, hF0, _hFr⟩
  refine ⟨F, hF1, hF0, ?_⟩
  intro i
  exact (F i).hasCompactSupport

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
    rw [ZetaAdmissibleFunction.sum_apply]
    simp [ZetaAdmissibleFunction.smul_apply]
  rw [hsum]
  have hsingle :
      (∑ j : Fin S.n, a j * F j (S.x i)) = a i * F i (S.x i) := by
    refine Finset.sum_eq_single i ?_ ?_
    · intro j _hj hji
      rw [hF0 j i hji.symm, mul_zero]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  rw [hsingle, hF1 i, mul_one]

/-- The sample interpolant assembled from admissible probes has compact support. -/
theorem sampleInterpolant_hasCompactSupport (S : FiniteSample) (a : Fin S.n → ℂ)
    (F : (i : Fin S.n) → ZetaAdmissibleFunction) :
    HasCompactSupport (sampleInterpolant S a F) := by
  dsimp [sampleInterpolant]
  rw [ZetaAdmissibleFunction.coeFn_sum_apply]
  convert ZetaAdmissibleFunction.hasCompactSupport_sum Finset.univ fun i => (a i) • F i using 1
  ext x
  simp [Finset.sum_apply]

/-- The sample interpolant support is contained in the union of the delta-basis supports. -/
theorem sampleInterpolant_support_subset_iUnion (S : FiniteSample) (a : Fin S.n → ℂ)
    (F : (i : Fin S.n) → ZetaAdmissibleFunction) :
    Function.support (sampleInterpolant S a F) ⊆ Set.iUnion fun i => Function.support (F i) := by
  intro y hy
  dsimp [sampleInterpolant] at hy
  rw [ZetaAdmissibleFunction.support_sum_apply] at hy
  rw [Function.mem_support] at hy
  have hyne : ∃ i ∈ (Finset.univ : Finset (Fin S.n)), ((a i) • F i) y ≠ 0 := by
    exact Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
      (f := fun i => ((a i) • F i) y) hy
  rcases hyne with ⟨i, _hi, hyFi⟩
  exact Set.mem_iUnion.2 ⟨i, ZetaAdmissibleFunction.support_smul_subset (a i) (F i) hyFi⟩

/-- A finite sample admits an admissible interpolant. -/
theorem exists_admissible_eval_sample (S : FiniteSample) (a : Fin S.n → ℂ) :
    ∃ f : ZetaAdmissibleFunction, ∀ i, f (S.x i) = a i := by
  rcases exists_admissible_delta_sample_with_support S with ⟨F, hF1, hF0, _hFc⟩
  let f : ZetaAdmissibleFunction := sampleInterpolant S a F
  refine ⟨f, ?_⟩
  intro i
  exact sampleInterpolant_apply S a F hF1 hF0 i

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

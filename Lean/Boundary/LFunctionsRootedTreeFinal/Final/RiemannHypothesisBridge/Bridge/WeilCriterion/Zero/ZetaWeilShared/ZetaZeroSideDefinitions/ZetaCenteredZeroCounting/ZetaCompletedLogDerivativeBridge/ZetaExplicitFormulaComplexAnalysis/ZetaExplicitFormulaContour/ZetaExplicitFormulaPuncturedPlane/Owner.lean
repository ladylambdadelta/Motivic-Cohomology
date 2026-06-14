import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalizationBridge.ZetaCompletedLogDerivativeCore.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalizationBridge.Owner
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.Topology.Basic
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Constructions

/-!
# Boundary explicit-formula punctured-plane lemmas

This file owns the zero-set and gamma nonvanishing facts that the contour
argument needs without importing the full complex-analysis surface.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- `Γℝ` does not vanish on the right half-plane. -/
theorem Gammaℝ_ne_zero_of_re_pos (s : ℂ) (hs : 0 < s.re) : Gammaℝ s ≠ 0 := by
  exact Complex.Gammaℝ_ne_zero_of_re_pos hs

/-- The punctured-plane neighborhood used to rule out local vanishing of `completedRiemannZeta`. -/
theorem completedRiemannZeta_eventuallyEq_zero_on_puncturedPlane
  (z : ℂ) (hz0 : z ≠ 0) (hz1 : z ≠ 1)
    (hzero : ∀ᶠ w in 𝓝 z, completedRiemannZeta w = 0) :
    Set.EqOn completedRiemannZeta (fun _ : ℂ => 0) {w : ℂ | w ≠ 0 ∧ w ≠ 1} := by
  let U : Set ℂ := {w : ℂ | w ≠ 0 ∧ w ≠ 1}
  have hU : IsPreconnected U := by
    have hcount : ({0, 1} : Set ℂ).Countable := by
      simp
    have hU_eq : U = ({0, 1} : Set ℂ)ᶜ := by
      ext w
      simp [U, and_comm]
    have hpath : IsPathConnected (U : Set ℂ) := by
      rw [hU_eq]
      exact
        (Set.Countable.isPathConnected_compl_of_one_lt_rank
          (show 1 < Module.rank ℝ ℂ by simp [Complex.rank_real_complex])
          hcount)
    exact hpath.isConnected.isPreconnected
  have hzU : z ∈ U := by
    simp [U, hz0, hz1]
  exact
    AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (f := completedRiemannZeta) (U := U)
      (by
        intro w hw
        rw [Complex.analyticAt_iff_eventually_differentiableAt]
        filter_upwards [eventually_ne_nhds hw.1, eventually_ne_nhds hw.2] with y hy0 hy1
        exact differentiableAt_completedZeta hy0 hy1)
      hU hzU hzero

/-- The completed zeta is nonzero at `2`, which is enough to contradict eventual vanishing. -/
theorem completedRiemannZeta_nonzero_two : completedRiemannZeta (2 : ℂ) ≠ 0 := by
  rw [completedRiemannZeta_eq_riemannZeta_mul_gamma (by norm_num : (2 : ℂ) ≠ 0)
      (Gammaℝ_ne_zero_of_re_pos (2 : ℂ) (by norm_num))]
  intro h
  have hzeta2 : riemannZeta (2 : ℂ) ≠ 0 := by
    rw [riemannZeta_two]
    norm_num [Complex.normSq, Real.pi_ne_zero]
  rcases mul_eq_zero.mp h with hzeta | hGamma
  · exact hzeta2 hzeta
  · exact (Gammaℝ_ne_zero_of_re_pos (2 : ℂ) (by norm_num)) hGamma

/-- The completed zeta function is not identically zero on the punctured plane `ℂ \ {0,1}`. -/
theorem completedRiemannZeta_not_eventually_zero
    (z : ℂ) (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    ¬ ∀ᶠ w in 𝓝 z, completedRiemannZeta w = 0 := by
  intro hzero
  have hzeroU :=
    completedRiemannZeta_eventuallyEq_zero_on_puncturedPlane z hz0 hz1 hzero
  have h2 : (2 : ℂ) ≠ 0 ∧ (2 : ℂ) ≠ 1 := by
    constructor
    · norm_num
    · norm_num
  exact completedRiemannZeta_nonzero_two (hzeroU h2)

/-- Away from its poles, the completed zeta has isolated zeros. -/
theorem completedRiemannZeta_eventually_ne_zero_of_zero
    (z : ℂ) (hz0 : z ≠ 0) (hz1 : z ≠ 1) (_hz : completedRiemannZeta z = 0) :
    ∀ᶠ w in 𝓝[≠] z, completedRiemannZeta w ≠ 0 := by
  have hA : AnalyticAt ℂ completedRiemannZeta z := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [eventually_ne_nhds hz0, eventually_ne_nhds hz1] with y hy0 hy1
    exact differentiableAt_completedZeta hy0 hy1
  rcases hA.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
  · exfalso
    exact completedRiemannZeta_not_eventually_zero z hz0 hz1 hzero
  · exact hne

/-- A nontrivial completed-zeta zero is isolated inside the nontrivial zero set. -/
theorem completedRiemannZeta_nontrivialZeroSet_disjoint_at
    {S : Set ℂ} {x : ℂ}
    (hS : S = {z : ℂ | z ≠ 0 ∧ z ≠ 1 ∧ completedRiemannZeta z = 0})
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hxz : completedRiemannZeta x = 0) :
    Disjoint (𝓝[≠] x) (𝓟 S) := by
  have hne : ∀ᶠ w in 𝓝[≠] x, completedRiemannZeta w ≠ 0 :=
    completedRiemannZeta_eventually_ne_zero_of_zero x hx0 hx1 hxz
  have hScompl : Sᶜ ∈ 𝓝[≠] x :=
    Filter.mem_of_superset hne
      (fun w hw hwS => hw ((hS ▸ hwS).2.2))
  exact (Filter.disjoint_principal_right).2 hScompl

/-- The nontrivial zero set of the completed zeta function is discrete. -/
theorem completedRiemannZeta_nontrivialZeroSet_discreteTopology :
    DiscreteTopology
      ({z : ℂ | z ≠ 0 ∧ z ≠ 1 ∧ completedRiemannZeta z = 0} : Set ℂ) := by
  let S : Set ℂ := {z : ℂ | z ≠ 0 ∧ z ≠ 1 ∧ completedRiemannZeta z = 0}
  refine (discreteTopology_subtype_iff).2 ?_
  intro x hx
  rcases hx with ⟨hx0, hx1, hxz⟩
  exact
    (completedRiemannZeta_nontrivialZeroSet_disjoint_at
      (S := S) (x := x) rfl hx0 hx1 hxz).eq_bot

/-- A discrete Lindelöf complex subtype is countable. -/
theorem completedRiemannZeta_countable_of_discrete {S : Set ℂ}
    (hdisc : DiscreteTopology S) : S.Countable := by
  haveI : DiscreteTopology S := hdisc
  haveI : LindelofSpace S := by infer_instance
  exact countable_of_Lindelof_of_discrete (X := S)

/-- The nontrivial zero set of the completed zeta function is countable. -/
theorem completedRiemannZeta_nontrivialZeroSet_countable :
    ({z : ℂ | z ≠ 0 ∧ z ≠ 1 ∧ completedRiemannZeta z = 0} : Set ℂ).Countable := by
  exact completedRiemannZeta_countable_of_discrete
    completedRiemannZeta_nontrivialZeroSet_discreteTopology

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

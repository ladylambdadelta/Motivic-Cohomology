import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.PuncturedStripTopology
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.TailIdentity
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.FixedCutoffHolomorphic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.FixedCutoffBernoulliHolomorphic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.PuncturedStripContinuation.PathConnectivityExtra

/-!
# Euler–Maclaurin punctured-strip analytic continuation
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
open Filter MeasureTheory Set
local notation "π" => Real.pi

/-- The fixed-cutoff defect vanishes on the open half-plane part of the
punctured strip. -/
theorem eulerMaclaurin_fixedCutoffTailIdentityDefect_zero_on_halfPlaneSubset
    (N : ℕ)
    (hN : 0 < N) :
    EqOn
      (eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect N)
      0
      ({z : ℂ | 1 < z.re ∧ z.re < 2}) := by
  intro z hz
  have hsplit :
      HasSum
        (fun n : ℕ =>
          if N < n then
            (1 : ℂ) / ((n : ℂ) ^ z)
          else
            0)
        (riemannZeta z - eulerMaclaurinZetaFinitePartWithCutoff N z) :=
    eulerMaclaurin_riemannZeta_fixedCutoff_halfPlane_finite_split_tail_hasSum
      N z hz.1
  have htail :
      HasSum
        (fun n : ℕ =>
          if N < n then
            (1 : ℂ) / ((n : ℂ) ^ z)
          else
            0)
        (eulerMaclaurinZetaMainTermWithCutoff N z +
          eulerMaclaurinZetaEndpointTermWithCutoff N z +
          eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff N z) :=
    eulerMaclaurin_riemannZeta_fixedCutoff_postCutoffTail_ownerTerms_hasSum
      N hN z hz.1
  have hidentity :
      riemannZeta z - eulerMaclaurinZetaFinitePartWithCutoff N z =
        eulerMaclaurinZetaMainTermWithCutoff N z +
          eulerMaclaurinZetaEndpointTermWithCutoff N z +
          eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff N z :=
    hsplit.unique htail
  exact sub_eq_zero.mpr hidentity

/-- The open half-plane part `1 < Re z < 2` accumulates at the base point used
for the punctured-strip identity theorem. -/
theorem eulerMaclaurin_halfPlaneSubset_frequently_near_identityBase :
    ∃ᶠ z in 𝓝[≠] ((3 / 2 : ℝ) : ℂ),
      z ∈ ({z : ℂ | 1 < z.re ∧ z.re < 2}) := by
  have hopen : IsOpen ({z : ℂ | 1 < z.re ∧ z.re < 2}) := by
    have hleft : IsOpen {z : ℂ | 1 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hright : IsOpen {z : ℂ | z.re < 2} :=
      isOpen_lt Complex.continuous_re continuous_const
    exact hleft.inter hright
  have hbase : ((3 / 2 : ℝ) : ℂ) ∈ ({z : ℂ | 1 < z.re ∧ z.re < 2}) := by
    constructor
    · exact (lt_div_iff₀ zero_lt_two).mpr (by
        calc
          (1 : ℝ) * 2 = 2 := one_mul 2
          _ < 3 := real_two_lt_three_for_puncturedVerticalStrip)
    · exact (div_lt_iff₀ zero_lt_two).mpr (by
        calc
          (3 : ℝ) < 4 := real_three_lt_four_for_puncturedVerticalStrip
          _ = 2 * 2 := real_two_mul_two_eq_four_for_puncturedVerticalStrip.symm)
  have heventually :
      ∀ᶠ z in 𝓝[≠] ((3 / 2 : ℝ) : ℂ),
        z ∈ ({z : ℂ | 1 < z.re ∧ z.re < 2}) :=
    mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hbase)
  exact heventually.frequently

/-- The chosen base point for the identity theorem lies in the punctured
vertical strip. -/
theorem eulerMaclaurin_identityBase_mem_puncturedVerticalStrip :
    ((3 / 2 : ℝ) : ℂ) ∈
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  constructor
  · exact div_pos zero_lt_three zero_lt_two
  · constructor
    · exact (div_lt_iff₀ zero_lt_two).mpr (by
        calc
          (3 : ℝ) < 4 := real_three_lt_four_for_puncturedVerticalStrip
          _ = 2 * 2 := real_two_mul_two_eq_four_for_puncturedVerticalStrip.symm)
    · intro h
      have hre : (3 / 2 : ℝ) = 1 := by
        exact congrArg Complex.re h
      have hmul : (3 / 2 : ℝ) * 2 = 1 * 2 :=
        congrArg (fun x : ℝ => x * 2) hre
      have hleft : (3 / 2 : ℝ) * 2 = 3 :=
        div_mul_cancel₀ (3 : ℝ) (show (2 : ℝ) ≠ 0 by exact two_ne_zero)
      have hright : (1 : ℝ) * 2 = 2 :=
        one_mul 2
      have hthree_eq_two : (3 : ℝ) = 2 :=
        Eq.trans hleft.symm (Eq.trans hmul hright)
      have hthree_ne_two : (3 : ℝ) ≠ 2 := by
        exact ne_of_gt real_two_lt_three_for_puncturedVerticalStrip
      exact hthree_ne_two hthree_eq_two

/-- Identity theorem specialized to a fixed-cutoff defect on the punctured
vertical strip, using its vanishing on the half-plane substrip. -/
theorem eulerMaclaurin_fixedCutoffTailIdentityDefect_identityTheorem_from_analytic_zeroSet
    (N : ℕ)
    (hN : 0 < N) :
    EqOn
      (eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect N)
      0
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  have han :
      AnalyticOnNhd ℂ
        (eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect N)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    eulerMaclaurin_fixedCutoffTailIdentityDefect_analyticOnNhd_puncturedStrip
      N hN
  have hpre :
      IsPreconnected ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    eulerMaclaurin_puncturedVerticalStrip_isPreconnected
  have hbase_mem :
      ((3 / 2 : ℝ) : ℂ) ∈ ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
    exact eulerMaclaurin_identityBase_mem_puncturedVerticalStrip
  have hfreq :
      ∃ᶠ z in 𝓝[≠] ((3 / 2 : ℝ) : ℂ),
        eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect N z = 0 :=
    eulerMaclaurin_halfPlaneSubset_frequently_near_identityBase.mono
      (fun z hz =>
        eulerMaclaurin_fixedCutoffTailIdentityDefect_zero_on_halfPlaneSubset
          N hN hz)
  exact
    han.eqOn_zero_of_preconnected_of_frequently_eq_zero
      hpre hbase_mem hfreq

/-- Identity theorem for the fixed-cutoff Euler-Maclaurin defect on the
connected punctured strip. -/
theorem eulerMaclaurin_fixedCutoffTailIdentityDefect_identityTheorem_from_halfPlaneZero_standard
    (N : ℕ)
    (hN : 0 < N)
    (z : ℂ)
    (hz_re_pos : 0 < z.re)
    (hz_re_lt_two : z.re < 2)
    (hz_ne_one : z ≠ 1) :
    eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect N z = 0 := by
  exact
    (eulerMaclaurin_fixedCutoffTailIdentityDefect_identityTheorem_from_analytic_zeroSet
      N hN) ⟨hz_re_pos, hz_re_lt_two, hz_ne_one⟩

/-- Identity theorem for the fixed-cutoff Euler-Maclaurin defect on the
connected punctured strip. -/
theorem eulerMaclaurin_fixedCutoffTailIdentityDefect_analyticContinuation_zero_on_puncturedStrip_standard
    (N : ℕ)
    (hN : 0 < N)
    (z : ℂ)
    (hz_re_pos : 0 < z.re)
    (hz_re_lt_two : z.re < 2)
    (hz_ne_one : z ≠ 1) :
    eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect N z = 0 := by
  exact
    eulerMaclaurin_fixedCutoffTailIdentityDefect_identityTheorem_from_halfPlaneZero_standard
      N hN z hz_re_pos hz_re_lt_two hz_ne_one

/-- Identity theorem for the fixed-cutoff Euler-Maclaurin defect on the
connected punctured strip. -/
theorem eulerMaclaurin_fixedCutoffTailIdentityDefect_identityTheorem_on_puncturedStrip_standard
    (N : ℕ)
    (hN : 0 < N)
    (z : ℂ)
    (hz_re_pos : 0 < z.re)
    (hz_re_lt_two : z.re < 2)
    (hz_ne_one : z ≠ 1) :
    eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect N z = 0 := by
  exact
    eulerMaclaurin_fixedCutoffTailIdentityDefect_analyticContinuation_zero_on_puncturedStrip_standard
      N hN z hz_re_pos hz_re_lt_two hz_ne_one

/-- Fixed-cutoff defect vanishes on the convergent half-plane by the
Dirichlet-series split and the fixed-cutoff Euler-Maclaurin formula. -/
theorem eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect_eq_zero_on_halfPlane_standard
    (N : ℕ)
    (hN : 0 < N)
    (z : ℂ)
    (hhalf_plane : 1 < z.re) :
    eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect N z = 0 := by
  have hsplit :
      HasSum
        (fun n : ℕ =>
          if N < n then
            (1 : ℂ) / ((n : ℂ) ^ z)
          else
            0)
        (riemannZeta z - eulerMaclaurinZetaFinitePartWithCutoff N z) :=
    eulerMaclaurin_riemannZeta_fixedCutoff_halfPlane_finite_split_tail_hasSum
      N z hhalf_plane
  have htail :
      HasSum
        (fun n : ℕ =>
          if N < n then
            (1 : ℂ) / ((n : ℂ) ^ z)
          else
            0)
        (eulerMaclaurinZetaMainTermWithCutoff N z +
          eulerMaclaurinZetaEndpointTermWithCutoff N z +
          eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff N z) :=
    eulerMaclaurin_riemannZeta_fixedCutoff_postCutoffTail_ownerTerms_hasSum
      N hN z hhalf_plane
  have hidentity :
      riemannZeta z - eulerMaclaurinZetaFinitePartWithCutoff N z =
        eulerMaclaurinZetaMainTermWithCutoff N z +
          eulerMaclaurinZetaEndpointTermWithCutoff N z +
          eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff N z :=
    hsplit.unique htail
  exact sub_eq_zero.mpr hidentity

/-- Identity theorem for the fixed-cutoff Euler-Maclaurin defect on the
connected punctured strip. -/
theorem eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect_eq_zero_on_puncturedStrip_by_identityTheorem_standard
    (N : ℕ)
    (hN : 0 < N)
    (z : ℂ)
    (hz_re_pos : 0 < z.re)
    (hz_re_lt_two : z.re < 2)
    (hz_ne_one : z ≠ 1) :
    eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect N z = 0 := by
  exact
    eulerMaclaurin_fixedCutoffTailIdentityDefect_identityTheorem_on_puncturedStrip_standard
      N hN z hz_re_pos hz_re_lt_two hz_ne_one

/-- Boundary-line vanishing of the Euler-Maclaurin tail defect by analytic
continuation.

The defect is holomorphic on the punctured strip, vanishes on the connected
open subset `1 < Re z ≤ 2` by the half-plane Dirichlet-series calculation, and
therefore vanishes at the non-pole boundary points on `Re z = 1`. -/
theorem eulerMaclaurin_riemannZeta_tailIdentityDefect_boundaryLine_eq_zero_by_identityTheorem_standard
    (z : ℂ)
    (hz_re : z.re = 1)
    (hz_ne_one : z ≠ 1) :
    eulerMaclaurin_riemannZeta_tailIdentityDefect z = 0 := by
  have hfixed :
      eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect
        (eulerMaclaurinPoleClearedZetaCutoff z) z = 0 :=
    eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect_eq_zero_on_puncturedStrip_by_identityTheorem_standard
      (eulerMaclaurinPoleClearedZetaCutoff z)
      (eulerMaclaurinPoleClearedZetaCutoff_pos z)
      z
      (Eq.subst (motive := fun x : ℝ => 0 < x) hz_re.symm zero_lt_one)
      (Eq.subst (motive := fun x : ℝ => x < 2) hz_re.symm one_lt_two)
      hz_ne_one
  exact
    Eq.trans
      (eulerMaclaurin_riemannZeta_tailIdentityDefect_eq_fixedCutoffDefect z)
      hfixed

/-- Boundary-line analytic-continuation uniqueness for the first-order
Euler-Maclaurin zeta tail. -/
theorem eulerMaclaurin_riemannZeta_boundaryLine_tail_identity_by_analyticContinuation_standard
    (z : ℂ)
    (hz_re : z.re = 1)
    (hz_ne_one : z ≠ 1) :
    riemannZeta z - eulerMaclaurinZetaFinitePart z =
      eulerMaclaurinZetaMainTerm z +
        eulerMaclaurinZetaEndpointTerm z +
        eulerMaclaurinZetaBernoulliIntegralRemainder z := by
  exact
    eulerMaclaurin_riemannZeta_tailIdentity_of_defect_eq_zero
      (eulerMaclaurin_riemannZeta_tailIdentityDefect_boundaryLine_eq_zero_by_identityTheorem_standard
        z hz_re hz_ne_one)

/-- Boundary-line analytic continuation of the first-order Euler-Maclaurin
tail identity. -/
theorem eulerMaclaurin_riemannZeta_boundaryLine_tail_identity_with_bernoulliIntegralRemainder_standard
    (z : ℂ)
    (hz_re : z.re = 1)
    (hz_ne_one : z ≠ 1) :
    riemannZeta z - eulerMaclaurinZetaFinitePart z =
      eulerMaclaurinZetaMainTerm z +
        eulerMaclaurinZetaEndpointTerm z +
        eulerMaclaurinZetaBernoulliIntegralRemainder z := by
  exact
    eulerMaclaurin_riemannZeta_boundaryLine_tail_identity_by_analyticContinuation_standard
      z hz_re hz_ne_one

end
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.FixedCutoffBernoulliHolomorphic

/-!
# Punctured-strip topology for the Euler-Maclaurin defect

This file records the Euler-Maclaurin wrappers around the shared punctured-strip
geometry facts used by the identity-theorem layer.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- The fixed punctured vertical strip used for the Euler-Maclaurin defect is open. -/
theorem eulerMaclaurin_fixedCutoff_puncturedStrip_isOpen :
    IsOpen ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  have hleft : IsOpen {z : ℂ | 0 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hright : IsOpen {z : ℂ | z.re < 2} :=
    isOpen_lt Complex.continuous_re continuous_const
  have hpole : IsOpen {z : ℂ | z ≠ 1} :=
    isOpen_compl_singleton
  have hstrip_eq :
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) =
        ({z : ℂ | 0 < z.re} ∩ {z : ℂ | z.re < 2} ∩ {z : ℂ | z ≠ 1}) := by
    ext z
    exact
      Iff.intro
        (fun hz => ⟨⟨hz.1, hz.2.1⟩, hz.2.2⟩)
        (fun hz => ⟨hz.1.1, hz.1.2, hz.2⟩)
  exact
    Eq.subst
      (motive := fun s : Set ℂ => IsOpen s)
      hstrip_eq.symm
      ((hleft.inter hright).inter hpole)

/-- The fixed-cutoff Euler-Maclaurin defect is analytic on a neighborhood of
the punctured strip. -/
theorem eulerMaclaurin_fixedCutoffTailIdentityDefect_analyticOnNhd_puncturedStrip
    (N : ℕ)
    (hN : 0 < N) :
    AnalyticOnNhd ℂ
      (eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect N)
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  exact
    (eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect_holomorphicOn_puncturedStrip_standard
      N hN).analyticOnNhd
      eulerMaclaurin_fixedCutoff_puncturedStrip_isOpen

/-- The punctured vertical strip is nonempty. -/
theorem eulerMaclaurin_puncturedVerticalStrip_nonempty :
    ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}).Nonempty := by
  exact puncturedVerticalStrip_nonempty

/-- The punctured vertical strip `0 < Re z < 2`, `z ≠ 1`, is path-connected. -/
theorem eulerMaclaurin_puncturedVerticalStrip_isPathConnected :
    IsPathConnected ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  exact puncturedVerticalStrip_isPathConnected

/-- The punctured vertical strip `0 < Re z < 2`, `z ≠ 1`, is preconnected. -/
theorem eulerMaclaurin_puncturedVerticalStrip_isPreconnected :
    IsPreconnected ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  exact puncturedVerticalStrip_isPreconnected

end

end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.FactorBoundData
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part02

/-!
# Completed-log-derivative singular separation

This file owns the pointwise-to-positive-distance step for singleton carriers.
The completed-zero component is stated in the uncentered residue coordinate,
which is the actual singular coordinate of `completedRiemannZeta`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

theorem positive_norm_separation_of_eventually_property
    {ι : Type} (z₀ : ℂ) (singularPoint : ι → ℂ) (P : ℂ → Prop)
    (eventuallyProperty : ∀ᶠ z in 𝓝 z₀, P z)
    (singularExclusion : ∀ i : ι, ¬ P (singularPoint i)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i : ι, δ ≤ ‖z₀ - singularPoint i‖ :=
  Exists.elim (Metric.mem_nhds_iff.mp eventuallyProperty)
    (fun ε hε =>
      let ε_pos : 0 < ε := hε.1
      let ball_subset : Metric.ball z₀ ε ⊆ {z : ℂ | P z} := hε.2
      Exists.intro ε
        (And.intro ε_pos
          (fun i =>
            le_of_not_gt
              (fun hlt =>
                let hdist :
                    dist z₀ (singularPoint i) < ε :=
                  Eq.subst
                    (motive := fun r : ℝ => r < ε)
                    (dist_eq_norm z₀ (singularPoint i)).symm
                    hlt
                let hmem : singularPoint i ∈ Metric.ball z₀ ε :=
                  Metric.mem_ball.mpr
                    (Eq.subst
                      (motive := fun r : ℝ => r < ε)
                      (dist_comm (singularPoint i) z₀).symm
                      hdist)
                singularExclusion i (ball_subset hmem)))))

theorem completedZeroResidueCoordinate_norm_separation_of_completedRiemannZeta_ne_zero
    (z₀ : ℂ)
    (hz₀_zero : z₀ ≠ 0)
    (hz₀_one : z₀ ≠ 1)
    (hz₀_zeta : completedRiemannZeta z₀ ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ρ : {ρ : ℂ // _root_.Boundary.LFunctions.ZetaCompletedZero ρ},
        δ ≤ ‖z₀ - ((1 / 2 : ℂ) + (ρ : ℂ))‖ :=
  positive_norm_separation_of_eventually_property
    z₀
    (fun ρ : {ρ : ℂ // _root_.Boundary.LFunctions.ZetaCompletedZero ρ} =>
      (1 / 2 : ℂ) + (ρ : ℂ))
    (fun z : ℂ => completedRiemannZeta z ≠ 0)
    ((differentiableAt_completedRiemannZeta hz₀_zero hz₀_one).continuousAt.eventually_ne
      hz₀_zeta)
    (fun ρ hne =>
      hne (completedRiemannZeta_zero_at_completedZeroResidueCoordinate ρ))

theorem gammaPole_norm_separation_of_Gammaℝ_ne_zero
    (z₀ : ℂ)
    (hz₀_gamma : Complex.Gammaℝ z₀ ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ n : ℕ, δ ≤ ‖z₀ - (-(2 * (n : ℂ)))‖ :=
  let avoidsGammaZero :
      ∀ n : ℕ, z₀ ≠ -(2 * (n : ℂ)) :=
    fun n hn =>
      hz₀_gamma (Complex.Gammaℝ_eq_zero_iff.mpr (Exists.intro n hn))
  positive_norm_separation_of_eventually_property
    z₀
    (fun n : ℕ => -(2 * (n : ℂ)))
    (fun z : ℂ => Complex.Gammaℝ z ≠ 0)
    ((Gammaℝ_differentiableAt_of_ne_zero_locus avoidsGammaZero).continuousAt.eventually_ne
      hz₀_gamma)
    (fun n hne =>
      hne
        (Complex.Gammaℝ_eq_zero_iff.mpr
          (Exists.intro n (Eq.refl (-(2 * (n : ℂ)))))))

/-- Every right-half-plane Gamma-real coordinate has a quantitative positive
distance from the complete Gamma-real pole lattice.  This is the analytic
owner input used when a scheduled inverse-Gamma carrier is centered there. -/
theorem gammaPole_norm_separation_of_re_pos
    (z₀ : ℂ)
    (hz₀_re : 0 < z₀.re) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ n : ℕ, δ ≤ ‖z₀ - (-(2 * (n : ℂ)))‖ :=
  gammaPole_norm_separation_of_Gammaℝ_ne_zero
    z₀ (Complex.Gammaℝ_ne_zero_of_re_pos hz₀_re)

theorem Gammaℝ_half_zero_is_even_negative
    {z : ℂ} (hz : Complex.Gammaℝ (z / 2) = 0) :
    ∃ n : ℕ, z = -(2 * (n : ℂ)) := by
  obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp hz
  refine ⟨2 * n, ?_⟩
  have htwo : (2 : ℂ) ≠ 0 := by
    exact OfNat.zero_ne_ofNat
  have hcancel : (z / 2) * 2 = z := by
    exact div_mul_cancel₀ z htwo
  have hscaled : (z / 2) * 2 = (-(2 * (n : ℂ))) * 2 :=
    congrArg (fun w : ℂ => w * 2) hn
  calc
    z = (z / 2) * 2 := hcancel.symm
    _ = (-(2 * (n : ℂ))) * 2 := hscaled
    _ = -(2 * ((2 * n : ℕ) : ℂ)) := by
      calc
        (-(2 * (n : ℂ))) * 2 = -((2 * (n : ℂ)) * 2) :=
          neg_mul (2 * (n : ℂ)) 2
        _ = -(2 * (2 * (n : ℂ))) :=
          congrArg Neg.neg (congrArg (fun w : ℂ => 2 * w) (mul_comm (n : ℂ) 2))
        _ = -(2 * ((2 * n : ℕ) : ℂ)) := by
          exact congrArg (fun w : ℂ => -(2 * w))
            (Nat.cast_mul 2 n).symm

theorem contourSingularPoint_norm_separation_of_factor_nonzero
    (z₀ : ℂ)
    (hz₀_zero : z₀ ≠ 0)
    (hz₀_one : z₀ ≠ 1)
    (hz₀_zeta : completedRiemannZeta z₀ ≠ 0)
    (hz₀_gamma : Complex.Gammaℝ z₀ ≠ 0)
    (hz₀_halfGamma : Complex.Gammaℝ (z₀ / 2) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ q : ℂ,
        explicitFormulaContourSingularPoint q →
          δ ≤ ‖z₀ - q‖ := by
  obtain ⟨δCompleted, hδCompleted_pos, hδCompleted⟩ :=
    completedZeroResidueCoordinate_norm_separation_of_completedRiemannZeta_ne_zero
      z₀ hz₀_zero hz₀_one hz₀_zeta
  obtain ⟨δGamma, hδGamma_pos, hδGamma⟩ :=
    gammaPole_norm_separation_of_Gammaℝ_ne_zero z₀ hz₀_gamma
  let δZero : ℝ := ‖z₀‖
  let δOne : ℝ := ‖z₀ - 1‖
  have hδZero_pos : 0 < δZero := norm_pos_iff.mpr hz₀_zero
  have hδOne_pos : 0 < δOne := by
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hz₀_one)
  let δ : ℝ := min δCompleted (min δGamma (min δZero δOne))
  have hδ_pos : 0 < δ := by
    exact lt_min hδCompleted_pos
      (lt_min hδGamma_pos (lt_min hδZero_pos hδOne_pos))
  refine ⟨δ, hδ_pos, ?_⟩
  intro q hq
  rcases hq with hq_zero | hq_one | hq_gamma | hq_halfGamma | hq_zeta
  · exact (min_le_right δCompleted (min δGamma (min δZero δOne))).trans_eq
      (show ‖z₀ - q‖ = δZero by
        exact congrArg norm (congrArg (fun w : ℂ => z₀ - w) hq_zero))
  · exact (min_le_right δCompleted (min δGamma (min δZero δOne))).trans_eq
      (show ‖z₀ - q‖ = δOne by
        exact congrArg norm (congrArg (fun w : ℂ => z₀ - w) hq_one))
  · obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp hq_gamma
    exact (min_le_right δCompleted (min δGamma (min δZero δOne))).trans
      (Eq.subst
        (motive := fun w : ℂ => δGamma ≤ ‖z₀ - w‖)
        hn
        (hδGamma n))
  · obtain ⟨n, hn⟩ := Gammaℝ_half_zero_is_even_negative hq_halfGamma
    exact (min_le_right δCompleted (min δGamma (min δZero δOne))).trans
      (Eq.subst
        (motive := fun w : ℂ => δGamma ≤ ‖z₀ - w‖)
        hn
        (hδGamma n))
  · rcases hq_zeta with ⟨hq_zero, hq_one, hq_zeta⟩
    have hrho : ZetaCompletedZero (q - (1 / 2 : ℂ)) :=
      zetaCompletedZero_of_completed_zero hq_zero hq_one hq_zeta
    have hresidue := hδCompleted ⟨q - (1 / 2 : ℂ), hrho⟩
    have hcoordinate :
        (1 / 2 : ℂ) + (q - (1 / 2 : ℂ)) = q :=
      complex_half_add_sub_half q
    exact (min_le_left δCompleted).trans
      (Eq.subst
        (motive := fun w : ℂ => δCompleted ≤ ‖z₀ - w‖)
        hcoordinate
        hresidue)

def CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.singleton_of_pointwise_regular
    {a b : ℝ}
    (z₀ : ℂ)
    (hz₀_strip : a ≤ z₀.re ∧ z₀.re ≤ b)
    (hz₀_zero : z₀ ≠ 0)
    (hz₀_one : z₀ ≠ 1)
    (hz₀_zeta : completedRiemannZeta z₀ ≠ 0)
    (hz₀_gamma : Complex.Gammaℝ z₀ ≠ 0) :
    CompletedZetaZeroExcisedStrip.FactorBoundedCarrier a b :=
  let completedSeparation :=
    completedZeroResidueCoordinate_norm_separation_of_completedRiemannZeta_ne_zero
      z₀ hz₀_zero hz₀_one hz₀_zeta
  let gammaSeparation := gammaPole_norm_separation_of_Gammaℝ_ne_zero z₀ hz₀_gamma
  Exists.elim completedSeparation
    (fun δCompleted hδCompleted =>
      Exists.elim gammaSeparation
        (fun δGamma hδGamma =>
          CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.singleton_of_singular_component_lower_bounds
            z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma
            δCompleted δGamma
            hδCompleted.1 hδGamma.1
            hδCompleted.2 hδGamma.2))

theorem CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.singleton_of_pointwise_regular_mem
    {a b : ℝ}
    (z₀ : ℂ)
    (hz₀_strip : a ≤ z₀.re ∧ z₀.re ≤ b)
    (hz₀_zero : z₀ ≠ 0)
    (hz₀_one : z₀ ≠ 1)
    (hz₀_zeta : completedRiemannZeta z₀ ≠ 0)
    (hz₀_gamma : Complex.Gammaℝ z₀ ≠ 0) :
    z₀ ∈
      (CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.singleton_of_pointwise_regular
        z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma).carrier.carrier :=
  by
    change z₀ ∈
      (CompletedZetaZeroExcisedStrip.singleton
        z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma).carrier
    exact CompletedZetaZeroExcisedStrip.mem_singleton
      z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

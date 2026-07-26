import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.CauchyBoundData

/-!
# Finite carrier completed-log-derivative bound data

This file owns the completely elementary finite-carrier bound-data
constructors.  On a singleton carrier every complex-valued function is bounded
by an explicit constant times every polynomial height weight; finite carriers
then follow by the existing union constructor.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

theorem CompletedZetaZeroExcisedStrip.HasPositiveSingularSeparation.singleton_of_lower_bounds
    {a b : ℝ}
    (z₀ : ℂ)
    (hz₀_strip : a ≤ z₀.re ∧ z₀.re ≤ b)
    (hz₀_zero : z₀ ≠ 0)
    (hz₀_one : z₀ ≠ 1)
    (hz₀_zeta : completedRiemannZeta z₀ ≠ 0)
    (hz₀_gamma : Complex.Gammaℝ z₀ ≠ 0)
    (δ : ℝ)
    (δ_pos : 0 < δ)
    (δ_zero : δ ≤ ‖z₀‖)
    (δ_one : δ ≤ ‖z₀ - 1‖)
    (δ_completedZero :
      ∀ ρ : {ρ : ℂ // _root_.Boundary.LFunctions.ZetaCompletedZero ρ},
        δ ≤ ‖z₀ - ((1 / 2 : ℂ) + (ρ : ℂ))‖)
    (δ_gammaPole :
      ∀ n : ℕ, δ ≤ ‖z₀ - (-(2 * (n : ℂ)))‖) :
    CompletedZetaZeroExcisedStrip.HasPositiveSingularSeparation
      (CompletedZetaZeroExcisedStrip.singleton
        z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma) :=
  Exists.intro δ
    (And.intro δ_pos
      (And.intro
        (fun z hz =>
          Eq.subst
            (motive := fun w : ℂ => δ ≤ ‖w‖)
            (Set.eq_of_mem_singleton hz).symm
            δ_zero)
        (And.intro
          (fun z hz =>
            Eq.subst
              (motive := fun w : ℂ => δ ≤ ‖w - 1‖)
              (Set.eq_of_mem_singleton hz).symm
              δ_one)
          (And.intro
            (fun z hz (ρ : {ρ : ℂ // _root_.Boundary.LFunctions.ZetaCompletedZero ρ}) =>
              Eq.subst
                (motive := fun w : ℂ =>
                  δ ≤ ‖w - ((1 / 2 : ℂ) + (ρ : ℂ))‖)
                (Set.eq_of_mem_singleton hz).symm
                (δ_completedZero ρ))
            (fun z hz n =>
              Eq.subst
                (motive := fun w : ℂ =>
                  δ ≤ ‖w - (-(2 * (n : ℂ)))‖)
                (Set.eq_of_mem_singleton hz).symm
                (δ_gammaPole n))))))

theorem CompletedZetaZeroExcisedStrip.HasPositiveSingularSeparation.singleton_of_factor_nonzero
    {a b : ℝ} (z₀ : ℂ)
    (hz₀_strip : a ≤ z₀.re ∧ z₀.re ≤ b)
    (hz₀_zero : z₀ ≠ 0) (hz₀_one : z₀ ≠ 1)
    (hz₀_zeta : completedRiemannZeta z₀ ≠ 0)
    (hz₀_gamma : Complex.Gammaℝ z₀ ≠ 0)
    (hz₀_halfGamma : Complex.Gammaℝ (z₀ / 2) ≠ 0) :
    CompletedZetaZeroExcisedStrip.HasPositiveSingularSeparation
      (CompletedZetaZeroExcisedStrip.singleton
        z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma) := by
  obtain ⟨δ, hδ, hseparated⟩ :=
    contourSingularPoint_norm_separation_of_factor_nonzero
      z₀ hz₀_zero hz₀_one hz₀_zeta hz₀_gamma hz₀_halfGamma
  exact CompletedZetaZeroExcisedStrip.HasPositiveSingularSeparation.singleton_of_lower_bounds
    z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma δ hδ
    (hseparated 0 (Or.inl rfl))
    (hseparated 1 (Or.inr (Or.inl rfl)))
    (fun ρ => hseparated ((1 / 2 : ℂ) + (ρ : ℂ))
      (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨completedZeroResidueCoordinate_ne_zero ρ,
          completedZeroResidueCoordinate_ne_one ρ,
          completedRiemannZeta_zero_at_completedZeroResidueCoordinate ρ⟩)))))
    (fun n => hseparated (-(2 * (n : ℂ)))
      (Or.inr (Or.inr (Or.inl (Complex.Gammaℝ_eq_zero_iff.mpr ⟨n, rfl⟩)))))

def CompletedZetaZeroExcisedStrip.ZetaSideBoundData.singleton
    {a b : ℝ}
    (z₀ : ℂ)
    (hz₀_strip : a ≤ z₀.re ∧ z₀.re ≤ b)
    (hz₀_zero : z₀ ≠ 0)
    (hz₀_one : z₀ ≠ 1)
    (hz₀_zeta : completedRiemannZeta z₀ ≠ 0)
    (hz₀_gamma : Complex.Gammaℝ z₀ ≠ 0)
    (separated :
      CompletedZetaZeroExcisedStrip.HasPositiveSingularSeparation
        (CompletedZetaZeroExcisedStrip.singleton
          z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma)) :
    CompletedZetaZeroExcisedStrip.ZetaSideBoundData
      (CompletedZetaZeroExcisedStrip.singleton
        z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma) :=
  { separated := separated
    constant := fun _N : ℕ => ‖zetaSideNegLogDeriv z₀‖ + 1
    constant_pos :=
      fun _N : ℕ =>
        add_pos_of_nonneg_of_pos
          (norm_nonneg (zetaSideNegLogDeriv z₀))
          zero_lt_one
    bound :=
      fun N z hz =>
        singleton_norm_le_value_add_one_mul_height
          zetaSideNegLogDeriv z₀ z N hz }

def CompletedZetaZeroExcisedStrip.ZetaSideBoundData.singleton_of_lower_bounds
    {a b : ℝ}
    (z₀ : ℂ)
    (hz₀_strip : a ≤ z₀.re ∧ z₀.re ≤ b)
    (hz₀_zero : z₀ ≠ 0)
    (hz₀_one : z₀ ≠ 1)
    (hz₀_zeta : completedRiemannZeta z₀ ≠ 0)
    (hz₀_gamma : Complex.Gammaℝ z₀ ≠ 0)
    (δ : ℝ)
    (δ_pos : 0 < δ)
    (δ_zero : δ ≤ ‖z₀‖)
    (δ_one : δ ≤ ‖z₀ - 1‖)
    (δ_completedZero :
      ∀ ρ : {ρ : ℂ // _root_.Boundary.LFunctions.ZetaCompletedZero ρ},
        δ ≤ ‖z₀ - ((1 / 2 : ℂ) + (ρ : ℂ))‖)
    (δ_gammaPole :
      ∀ n : ℕ, δ ≤ ‖z₀ - (-(2 * (n : ℂ)))‖) :
    CompletedZetaZeroExcisedStrip.ZetaSideBoundData
      (CompletedZetaZeroExcisedStrip.singleton
        z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma) :=
  CompletedZetaZeroExcisedStrip.ZetaSideBoundData.singleton
    z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma
    (CompletedZetaZeroExcisedStrip.HasPositiveSingularSeparation.singleton_of_lower_bounds
      z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma
      δ δ_pos δ_zero δ_one δ_completedZero δ_gammaPole)

def CompletedZetaZeroExcisedStrip.InverseGammaBoundData.singleton
    {a b : ℝ}
    (z₀ : ℂ)
    (hz₀_strip : a ≤ z₀.re ∧ z₀.re ≤ b)
    (hz₀_zero : z₀ ≠ 0)
    (hz₀_one : z₀ ≠ 1)
    (hz₀_zeta : completedRiemannZeta z₀ ≠ 0)
    (hz₀_gamma : Complex.Gammaℝ z₀ ≠ 0)
    (separated :
      CompletedZetaZeroExcisedStrip.HasPositiveSingularSeparation
        (CompletedZetaZeroExcisedStrip.singleton
          z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma)) :
    CompletedZetaZeroExcisedStrip.InverseGammaBoundData
      (CompletedZetaZeroExcisedStrip.singleton
        z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma) :=
  { separated := separated
    constant :=
      fun _N : ℕ =>
        ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z₀ /
            (Complex.Gammaℝ z₀)⁻¹‖ + 1
    constant_pos :=
      fun _N : ℕ =>
        add_pos_of_nonneg_of_pos
          (norm_nonneg
            (deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z₀ /
              (Complex.Gammaℝ z₀)⁻¹))
          zero_lt_one
    bound :=
      fun N z hz =>
        singleton_norm_le_value_add_one_mul_height
          (fun w : ℂ =>
            deriv (fun u : ℂ => (Complex.Gammaℝ u)⁻¹) w /
              (Complex.Gammaℝ w)⁻¹)
          z₀ z N hz }

def CompletedZetaZeroExcisedStrip.InverseGammaBoundData.singleton_of_lower_bounds
    {a b : ℝ}
    (z₀ : ℂ)
    (hz₀_strip : a ≤ z₀.re ∧ z₀.re ≤ b)
    (hz₀_zero : z₀ ≠ 0)
    (hz₀_one : z₀ ≠ 1)
    (hz₀_zeta : completedRiemannZeta z₀ ≠ 0)
    (hz₀_gamma : Complex.Gammaℝ z₀ ≠ 0)
    (δ : ℝ)
    (δ_pos : 0 < δ)
    (δ_zero : δ ≤ ‖z₀‖)
    (δ_one : δ ≤ ‖z₀ - 1‖)
    (δ_completedZero :
      ∀ ρ : {ρ : ℂ // _root_.Boundary.LFunctions.ZetaCompletedZero ρ},
        δ ≤ ‖z₀ - ((1 / 2 : ℂ) + (ρ : ℂ))‖)
    (δ_gammaPole :
      ∀ n : ℕ, δ ≤ ‖z₀ - (-(2 * (n : ℂ)))‖) :
    CompletedZetaZeroExcisedStrip.InverseGammaBoundData
      (CompletedZetaZeroExcisedStrip.singleton
        z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma) :=
  CompletedZetaZeroExcisedStrip.InverseGammaBoundData.singleton
    z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma
    (CompletedZetaZeroExcisedStrip.HasPositiveSingularSeparation.singleton_of_lower_bounds
      z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma
      δ δ_pos δ_zero δ_one δ_completedZero δ_gammaPole)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

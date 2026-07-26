import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.FactorBoundData

/-!
# Physical log-derivative control owner

This file owns the analytic control input needed by the physical affine
endpoint in the final autocorrelation lane.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The Binet/Stirling completion bound transports to the reciprocal-Gamma
derivative quotient stored by `InverseGammaBoundData`. -/
theorem inverseGammaDerivativeQuotient_norm_le_of_completion_norm_le_owner
    {z : ℂ} {B : ℝ} (hB :
      ‖inverseGammaCompletionLogDeriv z‖ ≤ B) :
    ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
        (Complex.Gammaℝ z)⁻¹‖ ≤ B :=
  let hidentity :
      inverseGammaCompletionLogDeriv z =
        deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
          (Complex.Gammaℝ z)⁻¹ :=
    inverseGammaCompletionLogDeriv_eq z
  let hnorm :
      ‖inverseGammaCompletionLogDeriv z‖ =
        ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
          (Complex.Gammaℝ z)⁻¹‖ :=
    congrArg norm hidentity
  Eq.subst
    (motive := fun value : ℝ => value ≤ B)
    hnorm.symm
    hB

/-- A pointwise polynomial bound is already the upper-bound witness needed by
the normalized zeta-side supremum owner. -/
theorem bddAbove_zetaSide_normalized_image_of_pointwise_bound_owner
    {f : ZetaAdmissibleFunction} {a b : ℝ}
    {E : CompletedZetaZeroExcisedStrip a b} (N : ℕ) (C : ℝ)
    (hbound : ∀ z : ℂ, z ∈ E.carrier →
      ‖zetaSideNegLogDeriv z‖ / (1 + ‖z.im‖) ^ N ≤ C) :
    BddAbove
      ((fun z : ℂ =>
          ‖zetaSideNegLogDeriv z‖ / (1 + ‖z.im‖) ^ N) '' E.carrier) :=
  Exists.intro C
    (fun y hy =>
      Exists.elim hy
        (fun z hzAnd =>
          match hzAnd with
          | And.intro hz hy_eq =>
              Eq.subst
                (motive := fun value : ℝ => value ≤ C)
                hy_eq
                (hbound z hz)))

/-- A pointwise polynomial bound is already the upper-bound witness needed by
the normalized inverse-Gamma logarithmic-derivative supremum owner. -/
theorem bddAbove_inverseGamma_normalized_image_of_pointwise_bound_owner
    {f : ZetaAdmissibleFunction} {a b : ℝ}
    {E : CompletedZetaZeroExcisedStrip a b} (N : ℕ) (C : ℝ)
    (hbound : ∀ z : ℂ, z ∈ E.carrier →
      ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
          (Complex.Gammaℝ z)⁻¹‖ / (1 + ‖z.im‖) ^ N ≤ C) :
    BddAbove
      ((fun z : ℂ =>
          ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
              (Complex.Gammaℝ z)⁻¹‖ /
            (1 + ‖z.im‖) ^ N) '' E.carrier) :=
  Exists.intro C
    (fun y hy =>
      Exists.elim hy
        (fun z hzAnd =>
          match hzAnd with
          | And.intro hz hy_eq =>
              Eq.subst
                (motive := fun value : ℝ => value ≤ C)
                hy_eq
                (hbound z hz)))

/- A uniform normalized pointwise estimate is the canonical source of the
upper-bound witnesses used by the two supremum owners. -/
def completedZetaNegLogDerivAutocorrelationConcreteControl_of_normalizedPointwiseBounds_owner
    (zetaPointwise :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
        (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ),
        ∃ C : ℝ, 0 < C ∧
          ∀ z : ℂ, z ∈ E.carrier →
            ‖zetaSideNegLogDeriv z‖ / (1 + ‖z.im‖) ^ N ≤ C)
    (gammaPointwise :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
        (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ),
        ∃ C : ℝ, 0 < C ∧
          ∀ z : ℂ, z ∈ E.carrier →
            ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
                (Complex.Gammaℝ z)⁻¹‖ /
              (1 + ‖z.im‖) ^ N ≤ C) :
    CompletedZetaNegLogDerivAutocorrelationConcreteControl :=
  completedZetaNegLogDerivAutocorrelationConcreteControl_of_factorControls
    (completedZetaNegLogDerivAutocorrelationZetaSideControl_owner
      (fun f a b E N =>
        match zetaPointwise f a b E N with
        | ⟨C, hC, hbound⟩ =>
            bddAbove_zetaSide_normalized_image_of_pointwise_bound_owner
              N C hbound))
    (completedZetaNegLogDerivAutocorrelationInverseGammaControl_owner
      (fun f a b E N =>
        match gammaPointwise f a b E N with
        | ⟨C, hC, hbound⟩ =>
            bddAbove_inverseGamma_normalized_image_of_pointwise_bound_owner
              N C hbound))

noncomputable def completedZetaNegLogDerivAutocorrelationZetaSideConstant_owner
    (f : ZetaAdmissibleFunction) (a b : ℝ)
    (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ) : ℝ :=
  1 +
    ‖sSup
        ((fun z : ℂ =>
            ‖zetaSideNegLogDeriv z‖ / (1 + ‖z.im‖) ^ N) ''
          E.carrier)‖

theorem completedZetaNegLogDerivAutocorrelationZetaSideConstant_pos_owner
    (f : ZetaAdmissibleFunction) (a b : ℝ)
    (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ) :
    0 <
      completedZetaNegLogDerivAutocorrelationZetaSideConstant_owner
        f a b E N :=
  add_pos_of_pos_of_nonneg
    zero_lt_one
    (norm_nonneg
      (sSup
        ((fun z : ℂ =>
            ‖zetaSideNegLogDeriv z‖ / (1 + ‖z.im‖) ^ N) ''
          E.carrier)))

theorem completedZetaNegLogDerivAutocorrelationZetaSide_bound_owner
    (f : ZetaAdmissibleFunction) (a b : ℝ)
    (E : CompletedZetaZeroExcisedStrip a b)
    (N : ℕ) (z : ℂ)
    (hbounded : BddAbove
      ((fun w : ℂ =>
          ‖zetaSideNegLogDeriv w‖ / (1 + ‖w.im‖) ^ N) '' E.carrier)) :
    z ∈ E.carrier →
      ‖zetaSideNegLogDeriv z‖ ≤
        completedZetaNegLogDerivAutocorrelationZetaSideConstant_owner
          f a b E N *
          (1 + ‖z.im‖) ^ N :=
  fun hz =>
  let normalizedSet : Set ℝ :=
    ((fun w : ℂ =>
        ‖zetaSideNegLogDeriv w‖ / (1 + ‖w.im‖) ^ N) '' E.carrier)
  let hmem :
      ‖zetaSideNegLogDeriv z‖ / (1 + ‖z.im‖) ^ N ∈
        normalizedSet :=
    Exists.intro z (And.intro hz rfl)
  let hsSup :
      ‖zetaSideNegLogDeriv z‖ / (1 + ‖z.im‖) ^ N ≤
        sSup normalizedSet :=
    le_csSup hbounded hmem
  let hheight : 0 < (1 + ‖z.im‖) ^ N :=
    pow_pos
      (add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg z.im))
      N
  let hmul :
      ‖zetaSideNegLogDeriv z‖ ≤
        sSup normalizedSet * (1 + ‖z.im‖) ^ N :=
    (div_le_iff₀ hheight).mp hsSup
  let hsSup_le_norm :
      sSup normalizedSet ≤ ‖sSup normalizedSet‖ :=
    le_abs_self (sSup normalizedSet)
  let hsSup_le_constant :
      sSup normalizedSet ≤
        1 + ‖sSup normalizedSet‖ :=
    le_trans hsSup_le_norm (le_add_of_nonneg_left zero_le_one)
  le_trans hmul
    (mul_le_mul_of_nonneg_right hsSup_le_constant (le_of_lt hheight))

def completedZetaNegLogDerivAutocorrelationZetaSideControl_owner
    (hbounded : ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
      (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ),
      BddAbove
        ((fun z : ℂ =>
            ‖zetaSideNegLogDeriv z‖ / (1 + ‖z.im‖) ^ N) '' E.carrier)) :
    CompletedZetaNegLogDerivAutocorrelationZetaSideControl :=
  { Czeta :=
      completedZetaNegLogDerivAutocorrelationZetaSideConstant_owner
    Czeta_pos :=
      completedZetaNegLogDerivAutocorrelationZetaSideConstant_pos_owner
    Czeta_bound :=
      fun f a b E N z hz =>
        completedZetaNegLogDerivAutocorrelationZetaSide_bound_owner
          f a b E N z (hbounded f a b E N) hz }

noncomputable def completedZetaNegLogDerivAutocorrelationInverseGammaConstant_owner
    (f : ZetaAdmissibleFunction) (a b : ℝ)
    (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ) : ℝ :=
  1 +
    ‖sSup
        ((fun z : ℂ =>
            ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
                (Complex.Gammaℝ z)⁻¹‖ /
              (1 + ‖z.im‖) ^ N) ''
          E.carrier)‖

theorem completedZetaNegLogDerivAutocorrelationInverseGammaConstant_pos_owner
    (f : ZetaAdmissibleFunction) (a b : ℝ)
    (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ) :
    0 <
      completedZetaNegLogDerivAutocorrelationInverseGammaConstant_owner
        f a b E N :=
  add_pos_of_pos_of_nonneg
    zero_lt_one
    (norm_nonneg
      (sSup
        ((fun z : ℂ =>
            ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
                (Complex.Gammaℝ z)⁻¹‖ /
              (1 + ‖z.im‖) ^ N) ''
          E.carrier)))

theorem completedZetaNegLogDerivAutocorrelationInverseGamma_bound_owner
    (f : ZetaAdmissibleFunction) (a b : ℝ)
    (E : CompletedZetaZeroExcisedStrip a b)
    (N : ℕ) (z : ℂ)
    (hbounded : BddAbove
      ((fun w : ℂ =>
          ‖deriv (fun u : ℂ => (Complex.Gammaℝ u)⁻¹) w /
            (Complex.Gammaℝ w)⁻¹‖ /
            (1 + ‖w.im‖) ^ N) '' E.carrier)) :
    z ∈ E.carrier →
      ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
          (Complex.Gammaℝ z)⁻¹‖ ≤
        completedZetaNegLogDerivAutocorrelationInverseGammaConstant_owner
          f a b E N *
          (1 + ‖z.im‖) ^ N :=
  fun hz =>
  let normalizedSet : Set ℝ :=
    ((fun w : ℂ =>
        ‖deriv (fun u : ℂ => (Complex.Gammaℝ u)⁻¹) w /
          (Complex.Gammaℝ w)⁻¹‖ /
          (1 + ‖w.im‖) ^ N) '' E.carrier)
  let hmem :
      ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
          (Complex.Gammaℝ z)⁻¹‖ /
          (1 + ‖z.im‖) ^ N ∈
        normalizedSet :=
    Exists.intro z (And.intro hz rfl)
  let hsSup :
      ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
          (Complex.Gammaℝ z)⁻¹‖ /
          (1 + ‖z.im‖) ^ N ≤
        sSup normalizedSet :=
    le_csSup hbounded hmem
  let hheight : 0 < (1 + ‖z.im‖) ^ N :=
    pow_pos
      (add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg z.im))
      N
  let hmul :
      ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
          (Complex.Gammaℝ z)⁻¹‖ ≤
        sSup normalizedSet * (1 + ‖z.im‖) ^ N :=
    (div_le_iff₀ hheight).mp hsSup
  let hsSup_le_norm :
      sSup normalizedSet ≤ ‖sSup normalizedSet‖ :=
    le_abs_self (sSup normalizedSet)
  let hsSup_le_constant :
      sSup normalizedSet ≤
        1 + ‖sSup normalizedSet‖ :=
    le_trans hsSup_le_norm (le_add_of_nonneg_left zero_le_one)
  le_trans hmul
    (mul_le_mul_of_nonneg_right hsSup_le_constant (le_of_lt hheight))

def completedZetaNegLogDerivAutocorrelationInverseGammaControl_owner
    (hbounded : ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
      (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ),
      BddAbove
        ((fun z : ℂ =>
            ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
                (Complex.Gammaℝ z)⁻¹‖ /
              (1 + ‖z.im‖) ^ N) '' E.carrier)) :
    CompletedZetaNegLogDerivAutocorrelationInverseGammaControl :=
  { Cgamma :=
      completedZetaNegLogDerivAutocorrelationInverseGammaConstant_owner
    Cgamma_pos :=
      completedZetaNegLogDerivAutocorrelationInverseGammaConstant_pos_owner
    Cgamma_bound :=
      fun f a b E N z hz =>
        completedZetaNegLogDerivAutocorrelationInverseGamma_bound_owner
          f a b E N z (hbounded f a b E N) hz }

def completedZetaNegLogDerivAutocorrelationConcreteControl_of_pointwise_bounds_owner
    (Czeta Cgamma : ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
      (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ), ℝ)
    (hZeta : ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
      (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ) (z : ℂ),
      z ∈ E.carrier →
      ‖zetaSideNegLogDeriv z‖ / (1 + ‖z.im‖) ^ N ≤ Czeta f a b E N)
    (hGamma : ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
      (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ) (z : ℂ),
      z ∈ E.carrier →
      ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
          (Complex.Gammaℝ z)⁻¹‖ / (1 + ‖z.im‖) ^ N ≤ Cgamma f a b E N) :
    CompletedZetaNegLogDerivAutocorrelationConcreteControl :=
  completedZetaNegLogDerivAutocorrelationConcreteControl_of_factorControls
    (completedZetaNegLogDerivAutocorrelationZetaSideControl_owner
      (fun f a b E N =>
        bddAbove_zetaSide_normalized_image_of_pointwise_bound_owner
          (f := f)
          N (Czeta f a b E N) (hZeta f a b E N)))
    (completedZetaNegLogDerivAutocorrelationInverseGammaControl_owner
      (fun f a b E N =>
        bddAbove_inverseGamma_normalized_image_of_pointwise_bound_owner
          (f := f)
          N (Cgamma f a b E N) (hGamma f a b E N)))

def completedZetaNegLogDerivAutocorrelationConcreteControl_owner
    (hboundedZeta : ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
      (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ),
      BddAbove
        ((fun z : ℂ =>
            ‖zetaSideNegLogDeriv z‖ / (1 + ‖z.im‖) ^ N) '' E.carrier))
    (hboundedGamma : ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
      (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ),
      BddAbove
        ((fun z : ℂ =>
            ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
                (Complex.Gammaℝ z)⁻¹‖ /
              (1 + ‖z.im‖) ^ N) '' E.carrier)) :
    CompletedZetaNegLogDerivAutocorrelationConcreteControl :=
  completedZetaNegLogDerivAutocorrelationConcreteControl_of_factorControls
    (completedZetaNegLogDerivAutocorrelationZetaSideControl_owner hboundedZeta)
    (completedZetaNegLogDerivAutocorrelationInverseGammaControl_owner hboundedGamma)

def completedZetaNegLogDerivControl_autocorrelation_owner
    (hboundedZeta : ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
      (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ),
      BddAbove
        ((fun z : ℂ =>
            ‖zetaSideNegLogDeriv z‖ / (1 + ‖z.im‖) ^ N) '' E.carrier))
    (hboundedGamma : ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
      (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ),
      BddAbove
        ((fun z : ℂ =>
            ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
                (Complex.Gammaℝ z)⁻¹‖ /
              (1 + ‖z.im‖) ^ N) '' E.carrier)) :
    ∀ f : ZetaAdmissibleFunction,
      CompletedZetaNegLogDerivControl (convolutionAutocorrelation f) :=
  completedZetaNegLogDerivControl_autocorrelation_of_concreteControl
    (completedZetaNegLogDerivAutocorrelationConcreteControl_owner
      hboundedZeta hboundedGamma)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

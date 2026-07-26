import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.ZetaPrimePowerWindow.OwnerParts.Part03
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ProbeInterface.ZetaAdmissibleFunction.ZetaAdmissibleNormalizedScale
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.SupportEnvelope.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.SupportInterval.Owner
import Mathlib.Analysis.SpecialFunctions.Exp

namespace Boundary
namespace LFunctions

noncomputable section
open scoped BigOperators
open Filter

namespace ZetaPrimePowerIndex

open ZetaAdmissibleFunction

theorem one_le_two_nat : (1 : ℕ) ≤ 2 :=
  Nat.succ_le_succ (Nat.zero_le 1)

theorem zero_lt_two_nat : (0 : ℕ) < 2 :=
  Nat.lt.step Nat.zero_lt_one

/-- The logarithmic center of a prime-power index in its arithmetic normal
form.  This is the owner-level cut used by the weighted exponential-decay
estimates. -/
theorem center_eq_natCast_mul_log (ι : ZetaPrimePowerIndex) :
    center ι = (ι.n : ℝ) * Real.log (ι.p : ℝ) := by
  unfold center
  rfl

/-- A center exponential is the corresponding real power of the underlying
prime.  This is the arithmetic normal form used to combine support growth
with the square-root prime-power weight. -/
theorem exp_mul_center_eq_prime_rpow
    (ι : ZetaPrimePowerIndex) (hι : IsGenuine ι) (r : ℝ) :
    Real.exp (r * center ι) =
      (ι.p : ℝ) ^ (r * (ι.n : ℝ)) := by
  have hp_pos_nat : 0 < ι.p :=
    lt_of_lt_of_le zero_lt_two_nat (Nat.Prime.two_le hι.1)
  have hp_pos_real : 0 < (ι.p : ℝ) := by
    exact_mod_cast hp_pos_nat
  have harg :
      Real.log (ι.p : ℝ) * (r * (ι.n : ℝ)) = r * center ι := by
    calc
      Real.log (ι.p : ℝ) * (r * (ι.n : ℝ)) =
          (Real.log (ι.p : ℝ) * r) * (ι.n : ℝ) := by
        exact (mul_assoc (Real.log (ι.p : ℝ)) r (ι.n : ℝ)).symm
      _ = (r * Real.log (ι.p : ℝ)) * (ι.n : ℝ) := by
        exact congrArg (fun x : ℝ => x * (ι.n : ℝ))
          (mul_comm (Real.log (ι.p : ℝ)) r)
      _ = r * ((ι.n : ℝ) * Real.log (ι.p : ℝ)) := by
        exact Eq.trans
          (mul_assoc r (Real.log (ι.p : ℝ)) (ι.n : ℝ))
          (congrArg (fun x : ℝ => r * x)
            (mul_comm (Real.log (ι.p : ℝ)) (ι.n : ℝ)))
      _ = r * center ι := by
        exact congrArg (fun x : ℝ => r * x)
          (center_eq_natCast_mul_log ι).symm
  exact Eq.trans
    (congrArg Real.exp harg.symm)
    (Real.rpow_def_of_pos hp_pos_real (r * (ι.n : ℝ))).symm

/-- A nonpositive center exponent cannot enlarge a genuine prime-power
coordinate. -/
theorem exp_mul_center_le_one_of_nonpos
    (ι : ZetaPrimePowerIndex) (hι : IsGenuine ι) (r : ℝ)
    (hr : r ≤ 0) :
    Real.exp (r * center ι) ≤ 1 := by
  have hp_one_real : (1 : ℝ) ≤ (ι.p : ℝ) := by
    have hp_two : 2 ≤ ι.p := Nat.Prime.two_le hι.1
    exact_mod_cast le_trans one_le_two_nat hp_two
  have hpower :
      Real.exp (r * center ι) = (ι.p : ℝ) ^ (r * (ι.n : ℝ)) :=
    exp_mul_center_eq_prime_rpow ι hι r
  exact hpower ▸ Real.rpow_le_one_of_one_le_of_nonpos hp_one_real
    (mul_nonpos_of_nonpos_of_nonneg hr (Nat.cast_nonneg ι.n))

/-- The completed prime-power weight absorbs a nonpositive center exponent
without increasing the global weight constant. -/
theorem weight_mul_exp_mul_center_le_two_of_nonpos
    (ι : ZetaPrimePowerIndex) (hι : IsGenuine ι) (r : ℝ)
    (hr : r ≤ 0) :
    weight ι * Real.exp (r * center ι) ≤ 2 := by
  have hweight_eq :
      weight ι = Real.log (ι.p : ℝ) / Real.sqrt (ι.p ^ ι.n : ℝ) := by
    unfold weight
    exact (if_pos hι.1).trans (if_pos hι.2)
  have hweight_nonneg : 0 ≤ weight ι := by
    exact hweight_eq ▸ div_nonneg
      (Real.log_nonneg (by
        have hp_two : 2 ≤ ι.p := Nat.Prime.two_le hι.1
        exact_mod_cast le_trans one_le_two_nat hp_two))
      (Real.sqrt_nonneg _)
  have hweight_le : weight ι ≤ 2 := by
    have hp_two : 2 ≤ ι.p := Nat.Prime.two_le hι.1
    have hp_pos_nat : 0 < ι.p := lt_of_lt_of_le zero_lt_two_nat hp_two
    have hp_pow_pos_nat : 0 < ι.p ^ ι.n := pow_pos hp_pos_nat ι.n
    have hsqrt_pos : 0 < Real.sqrt (ι.p ^ ι.n : ℝ) := by
      exact Real.sqrt_pos.mpr (by exact_mod_cast hp_pow_pos_nat)
    have hlog : Real.log (ι.p : ℝ) ≤
        (2 : ℝ) * Real.sqrt (ι.p ^ ι.n : ℝ) := by
      have hlog_base : Real.log (ι.p : ℝ) ≤
          (2 : ℝ) * Real.sqrt (ι.p : ℝ) := by
        have hhalf_pos : 0 < (1 / 2 : ℝ) :=
          div_pos zero_lt_one zero_lt_two
        have hlog' : Real.log (ι.p : ℝ) ≤
            (ι.p : ℝ) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) :=
          Real.log_natCast_le_rpow_div ι.p hhalf_pos
        have hhalf : (ι.p : ℝ) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) =
            (2 : ℝ) * Real.sqrt (ι.p : ℝ) := by
          calc
            (ι.p : ℝ) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) =
                (ι.p : ℝ) ^ (1 / 2 : ℝ) * (1 / 2 : ℝ)⁻¹ :=
              div_eq_mul_inv _ _
            _ = (ι.p : ℝ) ^ (1 / 2 : ℝ) * 2 := by
              exact congrArg _ (inv_eq_of_mul_eq_one_right
                (Eq.trans (congrArg (fun x : ℝ => x * 2) (one_div 2))
                  (inv_mul_cancel₀ two_ne_zero)))
            _ = (2 : ℝ) * (ι.p : ℝ) ^ (1 / 2 : ℝ) :=
              mul_comm _ _
            _ = (2 : ℝ) * Real.sqrt (ι.p : ℝ) :=
              congrArg _ (Real.sqrt_eq_rpow (ι.p : ℝ)).symm
        exact hlog'.trans_eq hhalf
      have hp_one_real : (1 : ℝ) ≤ ι.p := by
        exact_mod_cast Nat.succ_le_of_lt hp_pos_nat
      have hn_pos : 0 < ι.n := hι.2
      have hp_le_pow : (ι.p : ℝ) ≤ (ι.p : ℝ) ^ ι.n :=
        le_self_pow₀ hp_one_real hn_pos.ne'
      have hsqrt_le : Real.sqrt (ι.p : ℝ) ≤
          Real.sqrt (ι.p ^ ι.n : ℝ) := by
        exact Real.sqrt_le_sqrt (by exact_mod_cast hp_le_pow)
      exact hlog_base.trans
        (mul_le_mul_of_nonneg_left hsqrt_le zero_le_two)
    exact hweight_eq ▸ (div_le_iff₀ hsqrt_pos).mpr hlog
  have hexp_nonneg : 0 ≤ Real.exp (r * center ι) :=
    le_of_lt (Real.exp_pos _)
  have hexp_le : Real.exp (r * center ι) ≤ 1 :=
    exp_mul_center_le_one_of_nonpos ι hι r hr
  have hmul :
      weight ι * Real.exp (r * center ι) ≤
        2 * Real.exp (r * center ι) :=
    mul_le_mul_of_nonneg_right hweight_le hexp_nonneg
  have htwo : 2 * Real.exp (r * center ι) ≤ 2 * 1 :=
    mul_le_mul_of_nonneg_left hexp_le zero_le_two
  exact hmul.trans (htwo.trans_eq (mul_one 2))

/-! The support-scale interface used by the arithmetic majorant: after a
normalization has made the support radius `M` small enough for the spectral
scale `R`, the square-root prime-power weight absorbs the resulting
exponential factor. -/

theorem weight_mul_exp_mul_center_le_two_of_support_margin
    (ι : ZetaPrimePowerIndex) (hι : IsGenuine ι)
    (R M : ℝ) (hmargin : 2 * R * M ≤ (1 / 2 : ℝ)) :
    weight ι *
        Real.exp ((2 * R * M - (1 / 2 : ℝ)) * center ι) ≤ 2 := by
  have hrate : 2 * R * M - (1 / 2 : ℝ) ≤ 0 :=
    sub_nonpos.mpr hmargin
  exact weight_mul_exp_mul_center_le_two_of_nonpos ι hι
    (2 * R * M - (1 / 2 : ℝ)) hrate

theorem exists_positive_scale_of_support_margin
    (R M : ℝ) :
    ∃ a : ℝ, 0 < a ∧ 2 * R * (M / a) ≤ (1 / 2 : ℝ) := by
  let a : ℝ := max 1 (4 * R * M)
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one (le_max_left 1 (4 * R * M))
  have hfour : 4 * R * M ≤ a := le_max_right 1 (4 * R * M)
  have hhalf : 0 ≤ (1 / 2 : ℝ) :=
    div_nonneg zero_le_one (le_of_lt zero_lt_two)
  have hscaled :
      (1 / 2 : ℝ) * (4 * R * M) ≤ (1 / 2 : ℝ) * a :=
    mul_le_mul_of_nonneg_left hfour hhalf
  have hscaled' : 2 * R * M ≤ (1 / 2 : ℝ) * a := by
    have hhalf_two : (1 / 2 : ℝ) * 2 = 1 := by
      exact Eq.trans
        (congrArg (fun value : ℝ => value * 2) (one_div 2))
        (inv_mul_cancel₀ two_ne_zero)
    have hhalf_four : (1 / 2 : ℝ) * 4 = 2 := by
      calc
        (1 / 2 : ℝ) * 4 = (1 / 2 : ℝ) * (2 * 2) := by
          exact congrArg (fun value : ℝ => (1 / 2 : ℝ) * value)
            (show (4 : ℝ) = 2 * 2 by
              exact Eq.trans
                (congrArg (fun n : ℕ => (n : ℝ))
                  (show (4 : ℕ) = 2 + 2 by rfl))
                (Eq.trans (Nat.cast_add 2 2)
                  (two_mul (2 : ℝ)).symm))
        _ = ((1 / 2 : ℝ) * 2) * 2 := by
          exact (mul_assoc (1 / 2 : ℝ) 2 2).symm
        _ = 1 * 2 := by
          exact congrArg (fun value : ℝ => value * 2) hhalf_two
        _ = 2 := one_mul 2
    exact Eq.subst
      (motive := fun value : ℝ => value ≤ (1 / 2 : ℝ) * a)
      (show (1 / 2 : ℝ) * (4 * R * M) = 2 * R * M by
        calc
          (1 / 2 : ℝ) * (4 * R * M) =
              ((1 / 2 : ℝ) * 4) * (R * M) := by
            calc
              (1 / 2 : ℝ) * (4 * R * M) =
                  ((1 / 2 : ℝ) * (4 * R)) * M :=
                (mul_assoc (1 / 2 : ℝ) (4 * R) M).symm
              _ = (((1 / 2 : ℝ) * 4) * R) * M := by
                exact congrArg (fun value : ℝ => value * M)
                  ((mul_assoc (1 / 2 : ℝ) 4 R).symm)
              _ = ((1 / 2 : ℝ) * 4) * (R * M) :=
                mul_assoc ((1 / 2 : ℝ) * 4) R M
          _ = 2 * (R * M) := by
            exact congrArg (fun value : ℝ => value * (R * M))
              hhalf_four
          _ = 2 * R * M := by
            exact (mul_assoc 2 R M).symm)
      hscaled
  have hdiv : 2 * R * M / a ≤ (1 / 2 : ℝ) :=
    (div_le_iff₀ ha).mpr hscaled'
  have hrewrite : 2 * R * (M / a) = 2 * R * M / a := by
    calc
      2 * R * (M / a) = (2 * R) * (M / a) := by
        exact Eq.refl _
      _ = (2 * R) * (M * a⁻¹) := by
        exact congrArg (fun value : ℝ => (2 * R) * value)
          (div_eq_mul_inv M a)
      _ = ((2 * R) * M) * a⁻¹ := by
        exact (mul_assoc (2 * R) M a⁻¹).symm
      _ = (2 * R * M) / a := by
        exact (div_eq_mul_inv (2 * R * M) a).symm
  exact ⟨a, ha, by
    calc
      2 * R * (M / a) = 2 * R * M / a := hrewrite
      _ ≤ (1 / 2 : ℝ) := hdiv⟩

theorem exists_normalizedScale_with_support_margin
    (_f : ZetaAdmissibleFunction)
    (_I : ZetaPaleyWienerSupportInterval _f)
    (R M : ℝ) :
    ∃ a : ℝ, 0 < a ∧
      2 * R * (M / a) ≤ (1 / 2 : ℝ) := by
  obtain ⟨a, ha, hmargin⟩ := exists_positive_scale_of_support_margin R M
  exact ⟨a, ha, hmargin⟩

/-! For `normalizedScale`, the physical support is multiplied by `a`; this is
the correctly oriented small-scale existence lemma used by the envelope
owner. -/

theorem exists_positive_dilation_scale_of_support_margin
    (R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M) :
    ∃ a : ℝ, 0 < a ∧ 2 * R * (a * M) ≤ (1 / 2 : ℝ) := by
  let d : ℝ := 4 * R * M + 1
  have hRM : 0 ≤ R * M := mul_nonneg hR hM
  have hd : 0 < d := by
    unfold d
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg (mul_nonneg zero_le_four hR) hM)
      zero_lt_one
  let a : ℝ := d⁻¹
  have ha : 0 < a := inv_pos.mpr hd
  have hfour : 4 * R * M ≤ d := by
    unfold d
    exact le_add_of_nonneg_right zero_le_one
  have hhalf : 0 ≤ (1 / 2 : ℝ) :=
    div_nonneg zero_le_one (le_of_lt zero_lt_two)
  have hscaled :
      (1 / 2 : ℝ) * (4 * R * M) ≤ (1 / 2 : ℝ) * d :=
    mul_le_mul_of_nonneg_left hfour hhalf
  have hscaled' : 2 * R * M ≤ (1 / 2 : ℝ) * d := by
    have hhalf_four : (1 / 2 : ℝ) * 4 = 2 := by
      have hhalf_two : (1 / 2 : ℝ) * 2 = 1 := by
        exact Eq.trans
          (congrArg (fun value : ℝ => value * 2) (one_div 2))
          (inv_mul_cancel₀ two_ne_zero)
      calc
        (1 / 2 : ℝ) * 4 = (1 / 2 : ℝ) * (2 * 2) := by
          exact congrArg (fun value : ℝ => (1 / 2 : ℝ) * value)
            (show (4 : ℝ) = 2 * 2 by
              exact Eq.trans
                (congrArg (fun n : ℕ => (n : ℝ))
                  (show (4 : ℕ) = 2 + 2 by rfl))
                (Eq.trans (Nat.cast_add 2 2)
                  (two_mul (2 : ℝ)).symm))
        _ = ((1 / 2 : ℝ) * 2) * 2 :=
          (mul_assoc (1 / 2 : ℝ) 2 2).symm
        _ = 1 * 2 := congrArg (fun value : ℝ => value * 2) hhalf_two
        _ = 2 := one_mul 2
    exact Eq.subst
      (motive := fun value : ℝ => value ≤ (1 / 2 : ℝ) * d)
      (show (1 / 2 : ℝ) * (4 * R * M) = 2 * R * M by
        calc
          (1 / 2 : ℝ) * (4 * R * M) =
              ((1 / 2 : ℝ) * 4) * (R * M) := by
            calc
              (1 / 2 : ℝ) * (4 * R * M) =
                  ((1 / 2 : ℝ) * (4 * R)) * M :=
                (mul_assoc (1 / 2 : ℝ) (4 * R) M).symm
              _ = (((1 / 2 : ℝ) * 4) * R) * M := by
                exact congrArg (fun value : ℝ => value * M)
                  ((mul_assoc (1 / 2 : ℝ) 4 R).symm)
              _ = ((1 / 2 : ℝ) * 4) * (R * M) :=
                mul_assoc ((1 / 2 : ℝ) * 4) R M
          _ = 2 * (R * M) := congrArg (fun value : ℝ => value * (R * M)) hhalf_four
          _ = 2 * R * M := (mul_assoc 2 R M).symm)
      hscaled
  have hquot : 2 * R * M / d ≤ (1 / 2 : ℝ) :=
    (div_le_iff₀ hd).mpr hscaled'
  have hrewrite : 2 * R * (a * M) = 2 * R * M / d := by
    unfold a
    calc
      2 * R * (d⁻¹ * M) = (2 * R) * (M * d⁻¹) := by
        exact congrArg (fun value : ℝ => (2 * R) * value)
          (mul_comm d⁻¹ M)
      _ = (2 * R * M) * d⁻¹ := by
        exact (mul_assoc (2 * R) M d⁻¹).symm
      _ = (2 * R * M) / d := (div_eq_mul_inv (2 * R * M) d).symm
  exact ⟨a, ha, by
    calc
      2 * R * (a * M) = 2 * R * M / d := hrewrite
      _ ≤ (1 / 2 : ℝ) := hquot⟩

theorem supportIntervalLength_scaled_by_positive
    {f : ZetaAdmissibleFunction}
    (I : ZetaPaleyWienerSupportInterval f) (a : ℝ) (ha : 0 ≤ a) :
    max (a * I.upper - a * I.lower) 0 =
      a * zetaPaleyWienerSupportIntervalLength I := by
  have hdiff : 0 ≤ I.upper - I.lower := sub_nonneg.mpr I.lower_le_upper
  have hscaled : 0 ≤ a * (I.upper - I.lower) :=
    mul_nonneg ha hdiff
  have hleft :
      max (a * I.upper - a * I.lower) 0 = a * (I.upper - I.lower) := by
    calc
      max (a * I.upper - a * I.lower) 0 =
          max (a * (I.upper - I.lower)) 0 :=
        congrArg (fun value : ℝ => max value 0)
          (mul_sub a I.upper I.lower).symm
      _ = a * (I.upper - I.lower) := max_eq_left hscaled
  have hright :
      a * zetaPaleyWienerSupportIntervalLength I =
        a * (I.upper - I.lower) := by
    unfold zetaPaleyWienerSupportIntervalLength
    exact congrArg (fun value : ℝ => a * value) (max_eq_left hdiff)
  exact hleft.trans hright.symm

theorem abs_endpoint_max_scaled_by_nonnegative
    {f : ZetaAdmissibleFunction}
    (I : ZetaPaleyWienerSupportInterval f) (a : ℝ) (ha : 0 ≤ a) :
    max (|a * I.lower|) (|a * I.upper|) =
      a * max |I.lower| |I.upper| := by
  have hlower : |a * I.lower| = a * |I.lower| := by
    exact Eq.trans (abs_mul a I.lower)
      (congrArg (fun value : ℝ => value * |I.lower|)
        (abs_of_nonneg ha))
  have hupper : |a * I.upper| = a * |I.upper| := by
    exact Eq.trans (abs_mul a I.upper)
      (congrArg (fun value : ℝ => value * |I.upper|)
        (abs_of_nonneg ha))
  have hmax :
      max (a * |I.lower|) (a * |I.upper|) =
        max (|I.lower| * a) (|I.upper| * a) := by
    exact congrArg₂ max
      (mul_comm a |I.lower|) (mul_comm a |I.upper|)
  exact Eq.trans (congrArg₂ max hlower hupper)
    (Eq.trans hmax
      (Eq.trans (max_mul_of_nonneg |I.lower| |I.upper| ha).symm
        (mul_comm (max |I.lower| |I.upper|) a)))

theorem normalizedScale_supportInterval_explicit_length
    (a : ℝ) (ha : 0 < a) (f : ZetaAdmissibleFunction)
    (I : ZetaPaleyWienerSupportInterval f) :
    ∃ J : ZetaPaleyWienerSupportInterval (normalizedScale a f),
      J.lower = a * I.lower ∧
      J.upper = a * I.upper ∧
      zetaPaleyWienerSupportIntervalLength J =
        a * zetaPaleyWienerSupportIntervalLength I := by
  obtain ⟨J, hlower, hupper⟩ :=
    normalizedScale_supportInterval_explicit a ha f I
  have hdifference :
      J.upper - J.lower = a * I.upper - a * I.lower :=
    congrArg₂ (fun x y : ℝ => x - y) hupper hlower
  have hlength :
      zetaPaleyWienerSupportIntervalLength J =
        max (a * I.upper - a * I.lower) 0 := by
    unfold zetaPaleyWienerSupportIntervalLength
    exact congrArg (fun value : ℝ => max value 0) hdifference
  have hscaled :
      max (a * I.upper - a * I.lower) 0 =
        a * zetaPaleyWienerSupportIntervalLength I :=
    supportIntervalLength_scaled_by_positive I a ha.le
  exact ⟨J, hlower, hupper, hlength.trans hscaled⟩

theorem stripExponentialEnvelope_realCenter_eq_endpoint_max
    {f : ZetaAdmissibleFunction}
    (I : ZetaPaleyWienerSupportInterval f) (R : ℝ) :
    zetaPaleyWienerStripExponentialEnvelope I R R =
      Real.exp (max (|R * I.lower|) (|R * I.upper|)) := by
  unfold zetaPaleyWienerStripExponentialEnvelope
  exact congrArg Real.exp (max_self
    (max (|R * I.lower|) (|R * I.upper|)))

theorem endpoint_max_of_positive_scaled_interval
    {f : ZetaAdmissibleFunction}
    (I : ZetaPaleyWienerSupportInterval f)
    (a R : ℝ) (ha : 0 ≤ a) (hR : 0 ≤ R)
    (J : ZetaPaleyWienerSupportInterval (normalizedScale a f))
    (hlower : J.lower = a * I.lower)
    (hupper : J.upper = a * I.upper) :
    max (|R * J.lower|) (|R * J.upper|) =
      (R * a) * max |I.lower| |I.upper| := by
  have hlower' :
      |R * J.lower| = |(R * a) * I.lower| := by
    exact Eq.trans
      (congrArg (fun value : ℝ => |R * value|) hlower)
      (congrArg abs (mul_assoc R a I.lower).symm)
  have hupper' :
      |R * J.upper| = |(R * a) * I.upper| := by
    exact Eq.trans
      (congrArg (fun value : ℝ => |R * value|) hupper)
      (congrArg abs (mul_assoc R a I.upper).symm)
  exact Eq.trans
    (congrArg₂ max hlower' hupper')
    (abs_endpoint_max_scaled_by_nonnegative I (R * a)
      (mul_nonneg hR ha))

/-- Polynomial powers are little-o of a positive exponential at the owner
level.  This is the asymptotic cut used to turn a strict center-decay margin
into a finite initial region plus a polynomial-height tail. -/
theorem polynomial_isLittleO_real_exp (k : ℕ) :
    (fun x : ℝ => x ^ k) =o[atTop] Real.exp := by
  exact Real.isLittleO_pow_exp_atTop

/-- The asymptotic cut supplies the eventual pointwise inequality used by the
finite-region/tail decomposition. -/
theorem eventually_polynomial_le_real_exp (k : ℕ) :
    ∀ᶠ x : ℝ in atTop, x ^ k ≤ Real.exp x := by
  have hbound := (polynomial_isLittleO_real_exp k).bound zero_lt_one
  filter_upwards [hbound, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  calc
    x ^ k = ‖x ^ k‖ := (Real.norm_of_nonneg (pow_nonneg hx0 k)).symm
    _ ≤ 1 * ‖Real.exp x‖ := hx
    _ = ‖Real.exp x‖ := one_mul _
    _ = Real.exp x := Real.norm_of_nonneg (le_of_lt (Real.exp_pos x))

/-- Every prime-power index that belongs to a window is genuine. -/
theorem mem_window_isGenuine
    (N : ℕ) (ι : ZetaPrimePowerIndex) :
    ι ∈ window N → IsGenuine ι := by
  intro hι
  exact isGenuine_of_mem_window N ι hι

/-- The real number `1` is strictly less than `2`. -/
theorem one_lt_two_real : (1 : ℝ) < 2 :=
  one_lt_two

/-- The real number `2` is positive. -/
theorem zero_lt_two_real : (0 : ℝ) < 2 :=
  lt_trans zero_lt_one one_lt_two_real

/-- Genuine prime-power centers are nonnegative. -/
theorem center_nonnegative_of_isGenuine
    (ι : ZetaPrimePowerIndex) (hι : IsGenuine ι) :
    0 ≤ center ι := by
  have hp_two : 2 ≤ ι.p := Nat.Prime.two_le hι.1
  have hp_one_real : (1 : ℝ) ≤ ι.p := by
    exact_mod_cast le_trans one_le_two_nat hp_two
  have hn_nonneg : 0 ≤ (ι.n : ℝ) := Nat.cast_nonneg ι.n
  have hlog_nonneg : 0 ≤ Real.log (ι.p : ℝ) := Real.log_nonneg hp_one_real
  unfold center
  unfold zetaPrimePacketCenter
  exact mul_nonneg hn_nonneg hlog_nonneg

/-- A genuine prime-power center is bounded by the square of its rectangular
height.  This is the owner-level comparison needed to transport vertical
Fourier decay into the height-indexed summability majorant. -/
theorem center_le_height_sq_of_isGenuine
    (ι : ZetaPrimePowerIndex) (hι : IsGenuine ι) :
    center ι ≤ ((ι.height : ℕ) : ℝ) ^ 2 := by
  have hp_two : 2 ≤ ι.p := Nat.Prime.two_le hι.1
  have hp_pos_nat : 0 < ι.p := lt_of_lt_of_le zero_lt_two_nat hp_two
  have hp_pos_real : 0 < (ι.p : ℝ) := by
    exact_mod_cast hp_pos_nat
  have hp_one_real : (1 : ℝ) ≤ ι.p := by
    exact_mod_cast Nat.succ_le_of_lt hp_pos_nat
  have hlog_nonneg : 0 ≤ Real.log (ι.p : ℝ) := Real.log_nonneg hp_one_real
  have hlog_le_p : Real.log (ι.p : ℝ) ≤ (ι.p : ℝ) := by
    exact le_trans
      (Real.log_le_sub_one_of_pos hp_pos_real)
      (sub_le_self (ι.p : ℝ) zero_le_one)
  have hn_height : (ι.n : ℝ) ≤ ((ι.height : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_max_right ι.p ι.n
  have hp_height : (ι.p : ℝ) ≤ ((ι.height : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_max_left ι.p ι.n
  have hn_nonnegative : 0 ≤ (ι.n : ℝ) := Nat.cast_nonneg ι.n
  have hp_nonnegative : 0 ≤ (ι.p : ℝ) := le_of_lt hp_pos_real
  have hheight_nonnegative : 0 ≤ ((ι.height : ℕ) : ℝ) := Nat.cast_nonneg ι.height
  have hcenter_mul :
      (ι.n : ℝ) * Real.log (ι.p : ℝ) ≤
        (ι.n : ℝ) * (ι.p : ℝ) :=
    mul_le_mul_of_nonneg_left hlog_le_p hn_nonnegative
  have hheight_mul :
      (ι.n : ℝ) * (ι.p : ℝ) ≤
        ((ι.height : ℕ) : ℝ) * ((ι.height : ℕ) : ℝ) :=
    mul_le_mul hn_height hp_height hp_nonnegative hheight_nonnegative
  unfold center
  unfold zetaPrimePacketCenter
  exact le_trans hcenter_mul hheight_mul

theorem one_add_sq_le_one_add_two_mul_of_nonnegative
    (x : ℝ) (hx : 0 ≤ x) :
    1 + x ^ 2 ≤ (1 + x) ^ 2 := by
  have hcross : 0 ≤ 2 * x :=
    mul_nonneg (by exact (0 : ℝ).le_of_lt zero_lt_two) hx
  have hmul : 2 * (1 : ℝ) * x = 2 * x := by
    exact Eq.trans
      (mul_assoc 2 1 x)
      (congrArg (fun value : ℝ => value * x) (mul_one 2))
  have hexpand : 1 + x ^ 2 + 2 * x = (1 + x) ^ 2 := by
    exact Eq.trans
      (Eq.trans
        (congrArg (fun value : ℝ => 1 + x ^ 2 + value) hmul.symm)
        (congrArg (fun value : ℝ => value + x ^ 2 + 2 * (1 : ℝ) * x)
          (one_pow 2).symm))
      (add_sq' (1 : ℝ) x).symm
  exact Eq.subst
    (motive := fun value : ℝ => 1 + x ^ 2 ≤ value)
    hexpand.symm
    (le_add_of_nonneg_right hcross)

theorem one_add_center_le_one_add_height_sq_of_isGenuine
    (ι : ZetaPrimePowerIndex) (hι : IsGenuine ι) :
    1 + center ι ≤ (1 + ((ι.height : ℕ) : ℝ)) ^ 2 := by
  have hcenter := center_le_height_sq_of_isGenuine ι hι
  have hheight : 0 ≤ ((ι.height : ℕ) : ℝ) := Nat.cast_nonneg ι.height
  exact le_trans
    (add_le_add_left hcenter 1)
    (one_add_sq_le_one_add_two_mul_of_nonnegative
      ((ι.height : ℕ) : ℝ) hheight)


/-- A genuine prime-power center bounded by `B` bounds the prime coordinate by `exp B`. -/
theorem prime_le_exp_of_isGenuine_center_le
    (B : ℝ) (ι : ZetaPrimePowerIndex)
    (hι : IsGenuine ι) (hcenter : center ι ≤ B) :
    (ι.p : ℝ) ≤ Real.exp B := by
  have hp_two : 2 ≤ ι.p := Nat.Prime.two_le hι.1
  have hp_pos_nat : 0 < ι.p := lt_of_lt_of_le zero_lt_two_nat hp_two
  have hp_pos_real : 0 < (ι.p : ℝ) := by
    exact_mod_cast hp_pos_nat
  have hp_one_real : (1 : ℝ) ≤ ι.p := by
    exact_mod_cast Nat.succ_le_of_lt hp_pos_nat
  have hlog_nonneg : 0 ≤ Real.log (ι.p : ℝ) := Real.log_nonneg hp_one_real
  have hn_one : (1 : ℝ) ≤ ι.n := by
    exact_mod_cast hι.2
  have hlog_le_center : Real.log (ι.p : ℝ) ≤ center ι := by
    unfold center
    unfold zetaPrimePacketCenter
    calc
      Real.log (ι.p : ℝ) = (1 : ℝ) * Real.log (ι.p : ℝ) := by
        exact (one_mul (Real.log (ι.p : ℝ))).symm
      _ ≤ (ι.n : ℝ) * Real.log (ι.p : ℝ) := by
        exact mul_le_mul_of_nonneg_right hn_one hlog_nonneg
  have hlog_le_B : Real.log (ι.p : ℝ) ≤ B := le_trans hlog_le_center hcenter
  exact (Real.log_le_iff_le_exp hp_pos_real).mp hlog_le_B

/-- A genuine prime-power center bounded by `B` bounds the exponent coordinate by
`B / log 2`. -/
theorem exponent_le_div_log_two_of_isGenuine_center_le
    (B : ℝ) (ι : ZetaPrimePowerIndex)
    (hι : IsGenuine ι) (hcenter : center ι ≤ B) :
    (ι.n : ℝ) ≤ B / Real.log 2 := by
  have hp_two : 2 ≤ ι.p := Nat.Prime.two_le hι.1
  have hlog_two_pos : 0 < Real.log 2 := Real.log_pos one_lt_two_real
  have hp_pos_real : 0 < (ι.p : ℝ) := by
    have hp_pos_nat : 0 < ι.p := lt_of_lt_of_le zero_lt_two_nat hp_two
    exact_mod_cast hp_pos_nat
  have htwo_pos : 0 < (2 : ℝ) := zero_lt_two_real
  have htwo_le_p : (2 : ℝ) ≤ ι.p := by
    exact_mod_cast hp_two
  have hlog_two_le_log_p : Real.log (2 : ℝ) ≤ Real.log (ι.p : ℝ) := by
    exact Real.log_le_log htwo_pos htwo_le_p
  have hn_nonneg : 0 ≤ (ι.n : ℝ) := Nat.cast_nonneg ι.n
  have hn_log_two_le_center :
      (ι.n : ℝ) * Real.log 2 ≤ center ι := by
    unfold center
    unfold zetaPrimePacketCenter
    exact mul_le_mul_of_nonneg_left hlog_two_le_log_p hn_nonneg
  have hn_log_two_le_B : (ι.n : ℝ) * Real.log 2 ≤ B :=
    le_trans hn_log_two_le_center hcenter
  exact (le_div_iff₀ hlog_two_pos).mpr hn_log_two_le_B

/-- Bounded genuine prime-power centers are contained in one rectangular raw box. -/
theorem exists_box_bound_of_isGenuine_center_le
    (B : ℝ) :
    ∃ N : ℕ, ∀ ι : ZetaPrimePowerIndex,
      IsGenuine ι → center ι ≤ B → ι ∈ box N := by
  by_cases hB : 0 ≤ B
  · obtain ⟨Np, hNp⟩ := exists_nat_ge (Real.exp B)
    obtain ⟨Nn, hNn⟩ := exists_nat_ge (B / Real.log 2)
    exact Exists.intro (max Np Nn)
      (fun ι hι hcenter =>
        have hp_exp : (ι.p : ℝ) ≤ Real.exp B :=
          prime_le_exp_of_isGenuine_center_le B ι hι hcenter
        have hn_div : (ι.n : ℝ) ≤ B / Real.log 2 :=
          exponent_le_div_log_two_of_isGenuine_center_le B ι hι hcenter
        have hp_le_Np_real : (ι.p : ℝ) ≤ Np := le_trans hp_exp hNp
        have hn_le_Nn_real : (ι.n : ℝ) ≤ Nn := le_trans hn_div hNn
        have hp_le_Np : ι.p ≤ Np := by
          exact_mod_cast hp_le_Np_real
        have hn_le_Nn : ι.n ≤ Nn := by
          exact_mod_cast hn_le_Nn_real
        have hp_le : ι.p ≤ max Np Nn :=
          le_trans hp_le_Np (Nat.le_max_left Np Nn)
        have hn_le : ι.n ≤ max Np Nn :=
          le_trans hn_le_Nn (Nat.le_max_right Np Nn)
        (mem_box_iff (max Np Nn) ι).mpr
          ⟨Nat.lt_succ_of_le hp_le, Nat.lt_succ_of_le hn_le⟩)
  · exact Exists.intro 0
      (fun ι hι hcenter =>
        have hcenter_nonneg : 0 ≤ center ι :=
          center_nonnegative_of_isGenuine ι hι
        have hBlt : B < 0 := lt_of_not_ge hB
        have hcenter_lt_zero : center ι < 0 := lt_of_le_of_lt hcenter hBlt
        False.elim ((not_lt_of_ge hcenter_nonneg) hcenter_lt_zero))

/-- The set of genuine prime-power indices with bounded center is finite. -/
theorem finite_setOf_isGenuine_and_center_le
    (B : ℝ) :
    ({ι : ZetaPrimePowerIndex | IsGenuine ι ∧ center ι ≤ B} : Set ZetaPrimePowerIndex).Finite := by
  obtain ⟨N, hN⟩ := exists_box_bound_of_isGenuine_center_le B
  exact Set.Finite.subset (Finset.finite_toSet (box N))
    (fun ι hι => hN ι hι.1 hι.2)

/-- Genuine prime-power weights are nonnegative. -/
theorem weight_nonnegative (ι : ZetaPrimePowerIndex) :
    0 ≤ weight ι := by
  by_cases hp : Nat.Prime ι.p
  · by_cases hn : 1 ≤ ι.n
    · have hp_two : 2 ≤ ι.p := Nat.Prime.two_le hp
      have hp_pos_nat : 0 < ι.p := lt_of_lt_of_le zero_lt_two_nat hp_two
      have hp_one_real : (1 : ℝ) ≤ ι.p := by exact_mod_cast Nat.succ_le_of_lt hp_pos_nat
      have hlog : 0 ≤ Real.log ι.p := Real.log_nonneg hp_one_real
      have hsqrt : 0 ≤ Real.sqrt (ι.p ^ ι.n) := Real.sqrt_nonneg _
      have hnonneg : 0 ≤ Real.log ι.p / Real.sqrt (ι.p ^ ι.n) :=
        div_nonneg hlog hsqrt
      have hweight :
          weight ι = Real.log ι.p / Real.sqrt (ι.p ^ ι.n) := by
        unfold weight
        exact (if_pos hp).trans (if_pos hn)
      exact Eq.subst
        (motive := fun x : ℝ => 0 ≤ x)
        hweight.symm
        hnonneg
    · have hweight : weight ι = 0 := by
        unfold weight
        exact (if_pos hp).trans (if_neg hn)
      exact Eq.subst
        (motive := fun x : ℝ => 0 ≤ x)
        hweight.symm
        (le_refl 0)
  · have hweight : weight ι = 0 := by
      unfold weight
      exact if_neg hp
    exact Eq.subst
      (motive := fun x : ℝ => 0 ≤ x)
      hweight.symm
      (le_refl 0)

/-- The real prime-power logarithmic quotient is nonnegative on genuine parameters. -/
theorem real_log_div_sqrt_primePower_nonnegative
    {p n : ℕ} (hp : Nat.Prime p) (_hn : 1 ≤ n) :
    0 ≤ Real.log (p : ℝ) / Real.sqrt (p ^ n : ℝ) := by
  have hp_two : 2 ≤ p := Nat.Prime.two_le hp
  have hp_pos_nat : 0 < p := lt_of_lt_of_le zero_lt_two_nat hp_two
  have hp_one_real : (1 : ℝ) ≤ p := by
    exact_mod_cast Nat.succ_le_of_lt hp_pos_nat
  have hlog_nonneg : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg hp_one_real
  have hsqrt_nonneg : 0 ≤ Real.sqrt (p ^ n : ℝ) :=
    Real.sqrt_nonneg (p ^ n : ℝ)
  exact div_nonneg hlog_nonneg hsqrt_nonneg

/-- The elementary logarithmic estimate at exponent `1 / 2`, in square-root form. -/
theorem real_log_natCast_le_two_sqrt (p : ℕ) :
    Real.log (p : ℝ) ≤ (2 : ℝ) * Real.sqrt (p : ℝ) := by
  have hhalf_pos : 0 < (1 / 2 : ℝ) :=
    div_pos zero_lt_one zero_lt_two
  have hlog :
      Real.log (p : ℝ) ≤ (p : ℝ) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) :=
    Real.log_natCast_le_rpow_div p hhalf_pos
  have hhalf :
      (p : ℝ) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) =
        (2 : ℝ) * Real.sqrt (p : ℝ) := by
    have htwo_ne_zero : (2 : ℝ) ≠ 0 := two_ne_zero
    have hhalf_mul_two : (1 / 2 : ℝ) * 2 = 1 := by
      exact Eq.trans
        (congrArg (fun x : ℝ => x * 2) (one_div 2))
        (inv_mul_cancel₀ htwo_ne_zero)
    have hhalf_inv : (1 / 2 : ℝ)⁻¹ = 2 :=
      inv_eq_of_mul_eq_one_right hhalf_mul_two
    calc
      (p : ℝ) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) =
          (p : ℝ) ^ (1 / 2 : ℝ) * (1 / 2 : ℝ)⁻¹ := by
        exact div_eq_mul_inv ((p : ℝ) ^ (1 / 2 : ℝ)) (1 / 2 : ℝ)
      _ = (p : ℝ) ^ (1 / 2 : ℝ) * 2 := by
        exact congrArg (fun x : ℝ => (p : ℝ) ^ (1 / 2 : ℝ) * x) hhalf_inv
      _ = 2 * (p : ℝ) ^ (1 / 2 : ℝ) := by
        exact mul_comm ((p : ℝ) ^ (1 / 2 : ℝ)) 2
      _ = (2 : ℝ) * Real.sqrt (p : ℝ) := by
        exact congrArg (fun x : ℝ => (2 : ℝ) * x)
          (Real.sqrt_eq_rpow (p : ℝ)).symm
  exact hlog.trans (le_of_eq hhalf)

/-- The square-root denominator increases when a genuine prime is raised to a positive power. -/
theorem real_sqrt_natCast_le_sqrt_primePower
    {p n : ℕ} (hp : Nat.Prime p) (hn : 1 ≤ n) :
    Real.sqrt (p : ℝ) ≤ Real.sqrt (p ^ n : ℝ) := by
  have hp_two : 2 ≤ p := Nat.Prime.two_le hp
  have hp_pos_nat : 0 < p := lt_of_lt_of_le zero_lt_two_nat hp_two
  have hp_one_real : (1 : ℝ) ≤ p := by
    exact_mod_cast Nat.succ_le_of_lt hp_pos_nat
  have hn_pos : 0 < n := hn
  have hp_le_pow : (p : ℝ) ≤ (p : ℝ) ^ n :=
    le_self_pow₀ hp_one_real hn_pos.ne'
  have hp_pow_cast : ((p : ℝ) ^ n) = (p ^ n : ℝ) := by
    exact_mod_cast (rfl : p ^ n = p ^ n)
  exact (Real.sqrt_le_sqrt hp_le_pow).trans_eq (congrArg Real.sqrt hp_pow_cast)

/-- The doubled square-root numerator is bounded by the prime-power denominator version. -/
theorem real_two_mul_sqrt_natCast_le_two_mul_sqrt_primePower
    {p n : ℕ} (hp : Nat.Prime p) (hn : 1 ≤ n) :
    (2 : ℝ) * Real.sqrt (p : ℝ) ≤ (2 : ℝ) * Real.sqrt (p ^ n : ℝ) := by
  exact mul_le_mul_of_nonneg_left
    (real_sqrt_natCast_le_sqrt_primePower hp hn)
    zero_le_two

/-- The logarithm is bounded by twice the prime-power square-root denominator. -/
theorem real_log_natCast_le_two_mul_sqrt_primePower
    {p n : ℕ} (hp : Nat.Prime p) (hn : 1 ≤ n) :
    Real.log (p : ℝ) ≤ (2 : ℝ) * Real.sqrt (p ^ n : ℝ) := by
  exact (real_log_natCast_le_two_sqrt p).trans
    (real_two_mul_sqrt_natCast_le_two_mul_sqrt_primePower hp hn)

/-- The real prime-power logarithmic quotient is bounded by two on genuine parameters. -/
theorem real_log_div_sqrt_primePower_le_two
    {p n : ℕ} (hp : Nat.Prime p) (hn : 1 ≤ n) :
    Real.log (p : ℝ) / Real.sqrt (p ^ n : ℝ) ≤ 2 := by
  have hp_two : 2 ≤ p := Nat.Prime.two_le hp
  have hp_pos_nat : 0 < p := lt_of_lt_of_le zero_lt_two_nat hp_two
  have hp_pow_pos_nat : 0 < p ^ n := pow_pos hp_pos_nat n
  have hp_pow_pos_real : 0 < (p ^ n : ℝ) := by
    exact_mod_cast hp_pow_pos_nat
  have hsqrt_pos : 0 < Real.sqrt (p ^ n : ℝ) :=
    Real.sqrt_pos.mpr hp_pow_pos_real
  exact (div_le_iff₀ hsqrt_pos).mpr
    (real_log_natCast_le_two_mul_sqrt_primePower hp hn)

/-- The scalar prime-power logarithmic weight is globally bounded on genuine
prime-power parameters. -/
theorem real_log_div_sqrt_primePower_norm_le_globalConstant :
    ∃ A : ℝ,
      0 ≤ A ∧
        ∀ p n : ℕ,
          Nat.Prime p →
            1 ≤ n →
              ‖((Real.log p / Real.sqrt (p ^ n) : ℝ) : ℂ)‖ ≤ A := by
  exact Exists.intro 2
    (And.intro zero_le_two
      (fun p n hp hn =>
        have hquot_nonneg :
            0 ≤ Real.log (p : ℝ) / Real.sqrt (p ^ n : ℝ) :=
          real_log_div_sqrt_primePower_nonnegative hp hn
        have hquot_le_two :
            Real.log (p : ℝ) / Real.sqrt (p ^ n : ℝ) ≤ 2 := by
          exact real_log_div_sqrt_primePower_le_two hp hn
        have hnorm_real :
            ‖((Real.log p / Real.sqrt (p ^ n) : ℝ) : ℂ)‖ =
              Real.log (p : ℝ) / Real.sqrt (p ^ n : ℝ) := by
          exact Eq.trans
            (RCLike.norm_ofReal (K := ℂ)
              (Real.log (p : ℝ) / Real.sqrt (p ^ n : ℝ)))
            (abs_of_nonneg hquot_nonneg)
        Eq.subst
          (motive := fun x : ℝ => x ≤ 2)
          hnorm_real.symm
          hquot_le_two))

/-- The completed prime-power weight is globally bounded over raw prime-power indices. -/
theorem weight_norm_le_globalConstant :
    ∃ A : ℝ,
      0 ≤ A ∧
        ∀ ι : ZetaPrimePowerIndex, ‖(weight ι : ℂ)‖ ≤ A := by
  obtain ⟨A, hA_nonneg, hA_bound⟩ :=
    real_log_div_sqrt_primePower_norm_le_globalConstant
  exact Exists.intro A
    (And.intro hA_nonneg
      (fun ι =>
        match Decidable.em (Nat.Prime ι.p) with
        | Or.inl hp =>
            match Decidable.em (1 ≤ ι.n) with
            | Or.inl hn =>
                have hweight :
                    weight ι = Real.log ι.p / Real.sqrt (ι.p ^ ι.n) := by
                  unfold weight
                  exact (if_pos hp).trans (if_pos hn)
                Eq.subst
                  (motive := fun x : ℝ => ‖(x : ℂ)‖ ≤ A)
                  hweight.symm
                  (hA_bound ι.p ι.n hp hn)
            | Or.inr hn =>
                have hweight : weight ι = 0 := by
                  unfold weight
                  exact (if_pos hp).trans (if_neg hn)
                have hzero : ‖((0 : ℝ) : ℂ)‖ ≤ A := by
                  exact Eq.subst
                    (motive := fun x : ℝ => x ≤ A)
                    (norm_zero : ‖((0 : ℝ) : ℂ)‖ = 0).symm
                    hA_nonneg
                Eq.subst
                  (motive := fun x : ℝ => ‖(x : ℂ)‖ ≤ A)
                  hweight.symm
                  hzero
        | Or.inr hp =>
            have hweight : weight ι = 0 := by
              unfold weight
              exact if_neg hp
            have hzero : ‖((0 : ℝ) : ℂ)‖ ≤ A := by
              exact Eq.subst
                (motive := fun x : ℝ => x ≤ A)
                (norm_zero : ‖((0 : ℝ) : ℂ)‖ = 0).symm
                hA_nonneg
            Eq.subst
              (motive := fun x : ℝ => ‖(x : ℂ)‖ ≤ A)
              hweight.symm
              hzero))

/-- Multiplication by the completed prime-power weight is absorbed by increasing the
rectangular-height decay exponent. -/
theorem weight_norm_mul_polynomialHeightDecay_le_shift
    (k : ℕ) :
    ∃ A : ℝ, ∃ l : ℕ,
      0 ≤ A ∧ k ≤ l ∧
        ∀ ι : ZetaPrimePowerIndex,
          ‖(weight ι : ℂ)‖ * polynomialHeightDecay k ι ≤
            A * polynomialHeightDecay l ι := by
  obtain ⟨A, hA_nonneg, hA_bound⟩ := weight_norm_le_globalConstant
  exact Exists.intro A
    (Exists.intro k
      (And.intro hA_nonneg
        (And.intro (le_refl k)
          (fun ι =>
            have hdecay_nonneg : 0 ≤ polynomialHeightDecay k ι :=
              polynomialHeightDecay_nonnegative k ι
            mul_le_mul_of_nonneg_right (hA_bound ι) hdecay_nonneg))))

/-- Non-genuine prime-power indices have zero completed prime-power weight. -/
theorem weight_eq_zero_of_not_isGenuine
    (ι : ZetaPrimePowerIndex) (hι : ¬ IsGenuine ι) :
    weight ι = 0 := by
  unfold IsGenuine at hι
  unfold weight
  by_cases hp : Nat.Prime ι.p
  · have hn : ¬ 1 ≤ ι.n := by
      intro hn
      exact hι ⟨hp, hn⟩
    exact (if_pos hp).trans (if_neg hn)
  · exact if_neg hp

/-- The square-root weight squares back to the weight. -/
theorem sqrtWeight_mul_self (ι : ZetaPrimePowerIndex) :
    sqrtWeight ι * sqrtWeight ι = weight ι := by
  calc
    sqrtWeight ι * sqrtWeight ι = sqrtWeight ι ^ 2 := by
      exact (pow_two (sqrtWeight ι)).symm
    _ = weight ι := by
      unfold sqrtWeight
      exact Real.sq_sqrt (weight_nonnegative ι)

end ZetaPrimePowerIndex

end
end LFunctions
end Boundary

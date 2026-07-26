import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part02

/-!
# Explicit-formula finite rectangle residues

This owner layer contains finite-rectangle residue equalities, scheduled avoidance, and residue-window error transport.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The completed negative logarithmic derivative has the same punctured local residue as
`- logDeriv completedRiemannZeta`. -/
theorem completedZetaNegLogDeriv_completedZero_residue_tendsto
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    Tendsto
      (fun z : ℂ => (z - completedZeroResidueCoordinate ρ) * completedZetaNegLogDeriv z)
      (𝓝[≠] (completedZeroResidueCoordinate ρ))
      (𝓝 (-(zetaZeroMultiplicity (ρ : ℂ) : ℂ))) := by
  let target : ℂ := -(zetaZeroMultiplicity (ρ : ℂ) : ℂ)
  let lhs : ℂ → ℂ :=
    fun z : ℂ => (z - completedZeroResidueCoordinate ρ) * completedZetaNegLogDeriv z
  let rhs : ℂ → ℂ :=
    fun z : ℂ => (z - completedZeroResidueCoordinate ρ) * (-logDeriv completedRiemannZeta z)
  have hrhs :
      Tendsto rhs (𝓝[≠] (completedZeroResidueCoordinate ρ)) (𝓝 target) :=
    completedRiemannZeta_negLogDeriv_completedZero_residue_tendsto ρ
  have hfun : lhs = rhs := by
    funext z
    exact
      congrArg
        (fun w : ℂ => (z - completedZeroResidueCoordinate ρ) * w)
        (completedZetaNegLogDeriv_eq_neg_logDeriv z)
  exact
    Eq.subst
      (motive := fun ψ : ℂ → ℂ =>
        Tendsto ψ (𝓝[≠] (completedZeroResidueCoordinate ρ)) (𝓝 target))
      hfun.symm
      hrhs

/-- At the completed-zeta pole coordinate `0`, the completed negative logarithmic
derivative coefficient is the corresponding coefficient for `-logDeriv completedRiemannZeta`. -/
theorem completedZetaNegLogDeriv_zeroPole_coeff_eq_negLogDeriv_coeff :
    (fun z : ℂ => z * completedZetaNegLogDeriv z) =
      (fun z : ℂ => z * (-logDeriv completedRiemannZeta z)) := by
  funext z
  exact
    congrArg
      (fun w : ℂ => z * w)
      (completedZetaNegLogDeriv_eq_neg_logDeriv z)

/-- At the completed-zeta pole coordinate `1`, the completed negative logarithmic
derivative coefficient is the corresponding coefficient for `-logDeriv completedRiemannZeta`. -/
theorem completedZetaNegLogDeriv_onePole_coeff_eq_negLogDeriv_coeff :
    (fun z : ℂ => (z - 1) * completedZetaNegLogDeriv z) =
      (fun z : ℂ => (z - 1) * (-logDeriv completedRiemannZeta z)) := by
  funext z
  exact
    congrArg
      (fun w : ℂ => (z - 1) * w)
      (completedZetaNegLogDeriv_eq_neg_logDeriv z)

/-- Transport a `0`-pole coefficient limit for `-logDeriv completedRiemannZeta` to the
completed negative logarithmic derivative. -/
theorem completedZetaNegLogDeriv_zeroPole_residue_tendsto_of_negLogDeriv
    (hlog :
      Tendsto
        (fun z : ℂ => z * (-logDeriv completedRiemannZeta z))
        (𝓝[≠] (0 : ℂ))
        (𝓝 (1 : ℂ))) :
    Tendsto
      (fun z : ℂ => z * completedZetaNegLogDeriv z)
      (𝓝[≠] (0 : ℂ))
      (𝓝 (1 : ℂ)) := by
  exact
    Eq.subst
      (motive := fun ψ : ℂ → ℂ =>
        Tendsto ψ (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)))
      completedZetaNegLogDeriv_zeroPole_coeff_eq_negLogDeriv_coeff.symm
      hlog

/-- Transport a `1`-pole coefficient limit for `-logDeriv completedRiemannZeta` to the
completed negative logarithmic derivative. -/
theorem completedZetaNegLogDeriv_onePole_residue_tendsto_of_negLogDeriv
    (hlog :
      Tendsto
        (fun z : ℂ => (z - 1) * (-logDeriv completedRiemannZeta z))
        (𝓝[≠] (1 : ℂ))
        (𝓝 (1 : ℂ))) :
    Tendsto
      (fun z : ℂ => (z - 1) * completedZetaNegLogDeriv z)
      (𝓝[≠] (1 : ℂ))
      (𝓝 (1 : ℂ)) := by
  exact
    Eq.subst
      (motive := fun ψ : ℂ → ℂ =>
        Tendsto ψ (𝓝[≠] (1 : ℂ)) (𝓝 (1 : ℂ)))
      completedZetaNegLogDeriv_onePole_coeff_eq_negLogDeriv_coeff.symm
      hlog

/-- The holomorphic factor obtained by removing the completed-zeta pole at `0`.

Mathlib's completed zeta satisfies
`Λ z = Λ₀ z - 1 / z - 1 / (1 - z)`, so this factor is the analytic continuation
of `z * Λ z` through `z = 0`. -/
noncomputable def completedRiemannZeta_zeroPoleRegularFactor (z : ℂ) : ℂ :=
  z * completedRiemannZeta₀ z - 1 - z / ((1 : ℂ) - z)

/-- The regular factor at the completed-zeta pole `0` is analytic at the pole. -/
theorem completedRiemannZeta_zeroPoleRegularFactor_analyticAt_zero :
    AnalyticAt ℂ completedRiemannZeta_zeroPoleRegularFactor (0 : ℂ) := by
  let linearDenom : ℂ → ℂ := fun z : ℂ => (1 : ℂ) - z
  have hΛ0 : AnalyticAt ℂ completedRiemannZeta₀ (0 : ℂ) :=
    differentiable_completedZeta₀.analyticAt (0 : ℂ)
  have hid : AnalyticAt ℂ (fun z : ℂ => z) (0 : ℂ) :=
    analyticAt_id
  have hone : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) (0 : ℂ) :=
    analyticAt_const
  have hlinear : AnalyticAt ℂ linearDenom (0 : ℂ) :=
    hone.sub hid
  have hlinear_ne : linearDenom (0 : ℂ) ≠ 0 := by
    change (1 : ℂ) - 0 ≠ 0
    intro h
    exact one_ne_zero (Eq.trans (sub_zero (1 : ℂ)).symm h)
  have hquot :
      AnalyticAt ℂ (fun z : ℂ => z / linearDenom z) (0 : ℂ) :=
    hid.div hlinear hlinear_ne
  have hmain :
      AnalyticAt ℂ
        (fun z : ℂ => z * completedRiemannZeta₀ z - 1 - z / linearDenom z)
        (0 : ℂ) :=
    ((hid.mul hΛ0).sub analyticAt_const).sub hquot
  exact hmain

/-- The regular factor has value `-1` at the completed-zeta pole `0`. -/
theorem completedRiemannZeta_zeroPoleRegularFactor_zero :
    completedRiemannZeta_zeroPoleRegularFactor (0 : ℂ) = -(1 : ℂ) := by
  calc
    completedRiemannZeta_zeroPoleRegularFactor (0 : ℂ) =
        (0 : ℂ) * completedRiemannZeta₀ (0 : ℂ) - 1 -
          (0 : ℂ) / ((1 : ℂ) - 0) := by
      rfl
    _ = (0 : ℂ) - 1 - (0 : ℂ) / ((1 : ℂ) - 0) := by
      exact congrArg
        (fun w : ℂ => w - 1 - (0 : ℂ) / ((1 : ℂ) - 0))
        (zero_mul (completedRiemannZeta₀ (0 : ℂ)))
    _ = (0 : ℂ) - 1 - 0 := by
      exact congrArg
        (fun w : ℂ => (0 : ℂ) - 1 - w)
        (zero_div ((1 : ℂ) - 0))
    _ = (0 : ℂ) - 1 := by
      exact sub_zero ((0 : ℂ) - 1)
    _ = -(1 : ℂ) := by
      exact zero_sub (1 : ℂ)

/-- The regular factor is nonzero at the completed-zeta pole `0`. -/
theorem completedRiemannZeta_zeroPoleRegularFactor_zero_ne_zero :
    completedRiemannZeta_zeroPoleRegularFactor (0 : ℂ) ≠ 0 := by
  intro hzero
  have hneg_one_zero : (-(1 : ℂ)) = 0 :=
    Eq.trans completedRiemannZeta_zeroPoleRegularFactor_zero.symm hzero
  exact neg_ne_zero.mpr one_ne_zero hneg_one_zero

/-- Away from `0`, the regular factor agrees with `z * completedRiemannZeta z`. -/
theorem completedRiemannZeta_zeroPoleRegularFactor_eq_mul_completedRiemannZeta
    {z : ℂ} (hz0 : z ≠ 0) :
    completedRiemannZeta_zeroPoleRegularFactor z =
      z * completedRiemannZeta z := by
  have hΛ :
      completedRiemannZeta z =
        completedRiemannZeta₀ z - 1 / z - 1 / ((1 : ℂ) - z) :=
    completedRiemannZeta_eq z
  have hzinv : z * (1 / z) = 1 :=
    mul_one_div_cancel hz0
  calc
    completedRiemannZeta_zeroPoleRegularFactor z =
        z * completedRiemannZeta₀ z - 1 - z / ((1 : ℂ) - z) := by
      rfl
    _ = z * completedRiemannZeta₀ z - z * (1 / z) -
          z * (1 / ((1 : ℂ) - z)) := by
      exact congrArg₂
        (fun a b : ℂ => z * completedRiemannZeta₀ z - a - b)
        hzinv.symm
        (Eq.trans
          (div_eq_mul_inv z ((1 : ℂ) - z))
          (congrArg
            (fun w : ℂ => z * w)
            (one_div ((1 : ℂ) - z)).symm))
    _ = z *
          (completedRiemannZeta₀ z - 1 / z - 1 / ((1 : ℂ) - z)) := by
      calc
        z * completedRiemannZeta₀ z - z * (1 / z) -
            z * (1 / ((1 : ℂ) - z)) =
            (z * completedRiemannZeta₀ z - z * (1 / z)) -
              z * (1 / ((1 : ℂ) - z)) := by
          rfl
        _ = z * (completedRiemannZeta₀ z - 1 / z) -
              z * (1 / ((1 : ℂ) - z)) := by
          exact congrArg
            (fun w : ℂ => w - z * (1 / ((1 : ℂ) - z)))
            (mul_sub z (completedRiemannZeta₀ z) (1 / z)).symm
        _ = z * ((completedRiemannZeta₀ z - 1 / z) -
              1 / ((1 : ℂ) - z)) := by
          exact (mul_sub z (completedRiemannZeta₀ z - 1 / z)
            (1 / ((1 : ℂ) - z))).symm
        _ = z *
              (completedRiemannZeta₀ z - 1 / z - 1 / ((1 : ℂ) - z)) := by
          rfl
    _ = z * completedRiemannZeta z := by
      exact congrArg (fun w : ℂ => z * w) hΛ.symm

/-- The completed-zeta zero-pole regular factor is eventually nonzero near `0`. -/
theorem completedRiemannZeta_zeroPoleRegularFactor_eventually_ne_zero :
    ∀ᶠ z in 𝓝 (0 : ℂ), completedRiemannZeta_zeroPoleRegularFactor z ≠ 0 := by
  exact
    completedRiemannZeta_zeroPoleRegularFactor_analyticAt_zero.continuousAt.eventually_ne
      completedRiemannZeta_zeroPoleRegularFactor_zero_ne_zero

/-- The regular factor contributes no pole coefficient: `z * H'/H tends to zero`. -/
theorem completedRiemannZeta_zeroPoleRegularFactor_logDeriv_coeff_tendsto_zero :
    Tendsto
      (fun z : ℂ => z * logDeriv completedRiemannZeta_zeroPoleRegularFactor z)
      (𝓝[≠] (0 : ℂ))
      (𝓝 (0 : ℂ)) := by
  let H : ℂ → ℂ := completedRiemannZeta_zeroPoleRegularFactor
  have hH_an : AnalyticAt ℂ H (0 : ℂ) :=
    completedRiemannZeta_zeroPoleRegularFactor_analyticAt_zero
  obtain ⟨s, hs_mem, hs_an⟩ := hH_an.exists_mem_nhds_analyticOnNhd
  have hderiv_cont : ContinuousAt (deriv H) (0 : ℂ) :=
    (hs_an.deriv (0 : ℂ) (mem_of_mem_nhds hs_mem)).continuousAt
  have hH_cont : ContinuousAt H (0 : ℂ) :=
    hH_an.continuousAt
  have hH_ne : H (0 : ℂ) ≠ 0 :=
    completedRiemannZeta_zeroPoleRegularFactor_zero_ne_zero
  have hlog_cont : ContinuousAt (logDeriv H) (0 : ℂ) :=
    hderiv_cont.div hH_cont hH_ne
  have hz_tendsto :
      Tendsto (fun z : ℂ => z) (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hlog_tendsto :
      Tendsto (fun z : ℂ => logDeriv H z) (𝓝[≠] (0 : ℂ)) (𝓝 (logDeriv H (0 : ℂ))) :=
    hlog_cont.tendsto.mono_left nhdsWithin_le_nhds
  have hmul :
      Tendsto
        (fun z : ℂ => z * logDeriv H z)
        (𝓝[≠] (0 : ℂ))
        (𝓝 ((0 : ℂ) * logDeriv H (0 : ℂ))) :=
    hz_tendsto.mul hlog_tendsto
  have htarget : (0 : ℂ) * logDeriv H (0 : ℂ) = 0 :=
    zero_mul (logDeriv H (0 : ℂ))
  exact
    Eq.subst
      (motive := fun w : ℂ =>
        Tendsto
          (fun z : ℂ => z * logDeriv H z)
          (𝓝[≠] (0 : ℂ))
          (𝓝 w))
      htarget
      hmul

/-- Off the pole, the completed-zeta negative logarithmic derivative splits into the
principal pole coefficient plus the logarithmic derivative of the regular factor. -/
theorem completedRiemannZeta_zeroPole_negLogDeriv_coeff_eq_regularFactor
    {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1)
    (hΛ : completedRiemannZeta z ≠ 0) :
    z * (-logDeriv completedRiemannZeta z) =
      1 - z * logDeriv completedRiemannZeta_zeroPoleRegularFactor z := by
  let H : ℂ → ℂ := completedRiemannZeta_zeroPoleRegularFactor
  let P : ℂ → ℂ := fun w : ℂ => w * completedRiemannZeta w
  have hH_eq_P : H =ᶠ[𝓝 z] P := by
    exact
      (eventually_ne_nhds hz0).mono
        (fun w hw =>
          completedRiemannZeta_zeroPoleRegularFactor_eq_mul_completedRiemannZeta
            (z := w) hw)
  have hderiv_eq : deriv H z = deriv P z :=
    hH_eq_P.deriv_eq
  have hvalue_eq : H z = P z :=
    completedRiemannZeta_zeroPoleRegularFactor_eq_mul_completedRiemannZeta hz0
  have hH_ne : H z ≠ 0 := by
    intro hzero
    have hprod_zero : P z = 0 :=
      Eq.trans hvalue_eq.symm hzero
    exact
      mul_ne_zero hz0 hΛ hprod_zero
  have hlogH_eq_P : logDeriv H z = logDeriv P z := by
    calc
      logDeriv H z = deriv H z / H z := by
        rfl
      _ = deriv P z / H z := by
        exact congrArg (fun w : ℂ => w / H z) hderiv_eq
      _ = deriv P z / P z := by
        exact congrArg (fun w : ℂ => deriv P z / w) hvalue_eq
      _ = logDeriv P z := by
        rfl
  have hP_log :
      logDeriv P z =
        logDeriv (fun w : ℂ => w) z + logDeriv completedRiemannZeta z := by
    exact
      logDeriv_mul
        (f := fun w : ℂ => w)
        (g := completedRiemannZeta)
        z
        hz0
        hΛ
        differentiableAt_id
        (differentiableAt_completedRiemannZeta hz0 hz1)
  have hid_log :
      logDeriv (fun w : ℂ => w) z = 1 / z :=
    logDeriv_id' z
  have hlogH :
      logDeriv H z = 1 / z + logDeriv completedRiemannZeta z := by
    calc
      logDeriv H z = logDeriv P z := by
        exact hlogH_eq_P
      _ = logDeriv (fun w : ℂ => w) z + logDeriv completedRiemannZeta z := by
        exact hP_log
      _ = 1 / z + logDeriv completedRiemannZeta z := by
        exact congrArg
          (fun w : ℂ => w + logDeriv completedRiemannZeta z)
          hid_log
  have hzinv : z * (1 / z) = 1 :=
    mul_one_div_cancel hz0
  calc
    z * (-logDeriv completedRiemannZeta z) =
        -(z * logDeriv completedRiemannZeta z) := by
      exact mul_neg z (logDeriv completedRiemannZeta z)
    _ = 1 - (1 + z * logDeriv completedRiemannZeta z) := by
      calc
        -(z * logDeriv completedRiemannZeta z) =
            0 - z * logDeriv completedRiemannZeta z := by
          exact (zero_sub (z * logDeriv completedRiemannZeta z)).symm
        _ = (1 - 1) - z * logDeriv completedRiemannZeta z := by
          exact congrArg
            (fun w : ℂ => w - z * logDeriv completedRiemannZeta z)
            (sub_self (1 : ℂ)).symm
        _ = 1 - (1 + z * logDeriv completedRiemannZeta z) := by
          exact
            (sub_add_eq_sub_sub (1 : ℂ) (1 : ℂ)
              (z * logDeriv completedRiemannZeta z)).symm
    _ = 1 - (z * (1 / z) + z * logDeriv completedRiemannZeta z) := by
      exact congrArg
        (fun w : ℂ => 1 - (w + z * logDeriv completedRiemannZeta z))
        hzinv.symm
    _ = 1 - z * (1 / z + logDeriv completedRiemannZeta z) := by
      exact congrArg
        (fun w : ℂ => 1 - w)
        (mul_add z (1 / z) (logDeriv completedRiemannZeta z)).symm
    _ = 1 - z * logDeriv H z := by
      exact congrArg
        (fun w : ℂ => 1 - z * w)
        hlogH.symm

/-- At the completed-zeta pole `0`, the raw negative logarithmic derivative has pole
coefficient `+1`. -/
theorem completedRiemannZeta_zeroPole_negLogDeriv_coeff_tendsto :
    Tendsto
      (fun z : ℂ => z * (-logDeriv completedRiemannZeta z))
      (𝓝[≠] (0 : ℂ))
      (𝓝 (1 : ℂ)) := by
  let H : ℂ → ℂ := completedRiemannZeta_zeroPoleRegularFactor
  have hregular :
      Tendsto
        (fun z : ℂ => z * logDeriv H z)
        (𝓝[≠] (0 : ℂ))
        (𝓝 (0 : ℂ)) :=
    completedRiemannZeta_zeroPoleRegularFactor_logDeriv_coeff_tendsto_zero
  have htarget_raw :
      Tendsto
        (fun z : ℂ => 1 - z * logDeriv H z)
        (𝓝[≠] (0 : ℂ))
        (𝓝 ((1 : ℂ) - 0)) :=
    tendsto_const_nhds.sub hregular
  have htarget : ((1 : ℂ) - 0) = 1 :=
    sub_zero (1 : ℂ)
  have htarget_limit :
      Tendsto
        (fun z : ℂ => 1 - z * logDeriv H z)
        (𝓝[≠] (0 : ℂ))
        (𝓝 (1 : ℂ)) :=
    Eq.subst
      (motive := fun w : ℂ =>
        Tendsto
          (fun z : ℂ => 1 - z * logDeriv H z)
          (𝓝[≠] (0 : ℂ))
          (𝓝 w))
      htarget
      htarget_raw
  have hΛ_ne_nhds :
      ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → completedRiemannZeta z ≠ 0 :=
    have hresidue_zero :
        Tendsto
          (fun s : ℂ => (s - (0 : ℂ)) * completedRiemannZeta s)
          (𝓝[≠] (0 : ℂ))
          (𝓝 (-(1 : ℂ))) := by
      have hfun :
          (fun s : ℂ => (s - (0 : ℂ)) * completedRiemannZeta s) =
            (fun s : ℂ => s * completedRiemannZeta s) := by
        funext s
        exact congrArg
          (fun w : ℂ => w * completedRiemannZeta s)
          (sub_zero s)
      exact
        Eq.subst
          (motive := fun g : ℂ → ℂ =>
            Tendsto g (𝓝[≠] (0 : ℂ)) (𝓝 (-(1 : ℂ))))
          hfun.symm
          completedRiemannZeta_residue_zero
    eventually_ne_zero_of_tendsto_sub_mul_ne_zero
      (f := completedRiemannZeta)
      (a := (0 : ℂ))
      (c := -(1 : ℂ))
      (neg_ne_zero.mpr one_ne_zero)
      hresidue_zero
  have hΛ_ne :
      ∀ᶠ z in 𝓝[≠] (0 : ℂ), completedRiemannZeta z ≠ 0 := by
    exact
      (eventually_nhdsWithin_iff.mpr hΛ_ne_nhds).mono
        (fun z hz => hz)
  have hone_ne :
      ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ≠ 1 :=
    (eventually_ne_nhds (zero_ne_one : (0 : ℂ) ≠ 1)).filter_mono nhdsWithin_le_nhds
  have hzero_ne :
      ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ≠ 0 :=
    self_mem_nhdsWithin
  have hpoint :
      (fun z : ℂ => z * (-logDeriv completedRiemannZeta z)) =ᶠ[𝓝[≠] (0 : ℂ)]
        (fun z : ℂ => 1 - z * logDeriv H z) := by
    exact
      ((hzero_ne.and hone_ne).and hΛ_ne).mono
        (fun z hz =>
          completedRiemannZeta_zeroPole_negLogDeriv_coeff_eq_regularFactor
            hz.left.left hz.left.right hz.right)
  exact htarget_limit.congr' hpoint.symm

/-- The reflection `z ↦ 1 - z` carries the punctured neighborhood of `1` to the
punctured neighborhood of `0`. -/
theorem completedRiemannZeta_oneSub_tendsto_punctured_one_to_zero :
    Tendsto
      (fun z : ℂ => (1 : ℂ) - z)
      (𝓝[≠] (1 : ℂ))
      (𝓝[≠] (0 : ℂ)) := by
  have hmap :
      Tendsto
        (Homeomorph.subLeft (1 : ℂ))
        (𝓝[≠] (1 : ℂ))
        (𝓝[≠] ((Homeomorph.subLeft (1 : ℂ)) (1 : ℂ))) := by
    exact le_of_eq
      ((Homeomorph.subLeft (1 : ℂ)).map_punctured_nhds_eq (1 : ℂ))
  have htarget :
      ((Homeomorph.subLeft (1 : ℂ)) (1 : ℂ)) = (0 : ℂ) :=
    sub_self (1 : ℂ)
  exact
    Eq.subst
      (motive := fun a : ℂ =>
        Tendsto
          (Homeomorph.subLeft (1 : ℂ))
          (𝓝[≠] (1 : ℂ))
          (𝓝[≠] a))
      htarget
      hmap

/-- Off the two completed-zeta pole coordinates, the raw negative logarithmic derivative
coefficient at `1` is the reflected coefficient at `0`. -/
theorem completedRiemannZeta_onePole_negLogDeriv_coeff_reflects_zeroPole
    {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    (z - 1) * (-logDeriv completedRiemannZeta z) =
      ((1 : ℂ) - z) *
        (-logDeriv completedRiemannZeta ((1 : ℂ) - z)) := by
  have hone_sub_ne_zero : (1 : ℂ) - z ≠ 0 := by
    intro h
    exact hz1 (sub_eq_zero.mp h).symm
  have hone_sub_ne_one : (1 : ℂ) - z ≠ 1 := by
    intro h
    have hbase : (1 : ℂ) = (1 : ℂ) + z :=
      sub_eq_iff_eq_add.mp h
    have hz_eq_zero : z = 0 :=
      calc
        z = ((1 : ℂ) + z) - 1 := by
          exact (add_sub_cancel_left (1 : ℂ) z).symm
        _ = (1 : ℂ) - 1 := by
          exact congrArg (fun w : ℂ => w - 1) hbase.symm
        _ = 0 := by
          exact sub_self (1 : ℂ)
    exact hz0 hz_eq_zero
  have hderiv :
      deriv completedRiemannZeta ((1 : ℂ) - z) =
        - deriv completedRiemannZeta z :=
    deriv_completedRiemannZeta_one_sub z hz0 hz1
  have hvalue :
      completedRiemannZeta ((1 : ℂ) - z) =
        completedRiemannZeta z :=
    completedRiemannZeta_one_sub z
  calc
    (z - 1) * (-logDeriv completedRiemannZeta z) =
        (-((1 : ℂ) - z)) * (-(deriv completedRiemannZeta z / completedRiemannZeta z)) := by
      exact
        congrArg₂ (fun a b : ℂ => a * b)
          (neg_sub (1 : ℂ) z).symm
          (congrArg Neg.neg (logDeriv_apply completedRiemannZeta z))
    _ = ((1 : ℂ) - z) * (deriv completedRiemannZeta z / completedRiemannZeta z) := by
      exact neg_mul_neg ((1 : ℂ) - z) (deriv completedRiemannZeta z / completedRiemannZeta z)
    _ = ((1 : ℂ) - z) *
        (-((-deriv completedRiemannZeta z) / completedRiemannZeta z)) := by
      have hnegdiv :
          -((-deriv completedRiemannZeta z) / completedRiemannZeta z) =
            deriv completedRiemannZeta z / completedRiemannZeta z := by
        calc
          -((-deriv completedRiemannZeta z) / completedRiemannZeta z) =
              -(-(deriv completedRiemannZeta z / completedRiemannZeta z)) := by
            exact congrArg Neg.neg
              (neg_div (completedRiemannZeta z) (deriv completedRiemannZeta z))
          _ = deriv completedRiemannZeta z / completedRiemannZeta z := by
            exact neg_neg (deriv completedRiemannZeta z / completedRiemannZeta z)
      exact congrArg
        (fun w : ℂ => ((1 : ℂ) - z) * w)
        hnegdiv.symm
    _ = ((1 : ℂ) - z) *
        (-(deriv completedRiemannZeta ((1 : ℂ) - z) /
            completedRiemannZeta ((1 : ℂ) - z))) := by
      exact congrArg
        (fun w : ℂ => ((1 : ℂ) - z) * (-w))
        (congrArg₂ (fun a b : ℂ => a / b) hderiv.symm hvalue.symm)
    _ = ((1 : ℂ) - z) *
        (-logDeriv completedRiemannZeta ((1 : ℂ) - z)) := by
      exact congrArg
        (fun w : ℂ => ((1 : ℂ) - z) * (-w))
        (logDeriv_apply completedRiemannZeta ((1 : ℂ) - z)).symm

/-- The completed functional equation transports the `0`-pole coefficient of
`-logDeriv completedRiemannZeta` to the `1`-pole coefficient. -/
theorem completedRiemannZeta_onePole_negLogDeriv_coeff_tendsto_of_zeroPole
    (hzero :
      Tendsto
        (fun z : ℂ => z * (-logDeriv completedRiemannZeta z))
        (𝓝[≠] (0 : ℂ))
        (𝓝 (1 : ℂ))) :
    Tendsto
      (fun z : ℂ => (z - 1) * (-logDeriv completedRiemannZeta z))
      (𝓝[≠] (1 : ℂ))
      (𝓝 (1 : ℂ)) := by
  have hreflected :
      Tendsto
        (fun z : ℂ =>
          ((1 : ℂ) - z) *
            (-logDeriv completedRiemannZeta ((1 : ℂ) - z)))
        (𝓝[≠] (1 : ℂ))
        (𝓝 (1 : ℂ)) :=
    hzero.comp completedRiemannZeta_oneSub_tendsto_punctured_one_to_zero
  have hcongr :
      (fun z : ℂ => (z - 1) * (-logDeriv completedRiemannZeta z)) =ᶠ[𝓝[≠] (1 : ℂ)]
        (fun z : ℂ =>
          ((1 : ℂ) - z) *
            (-logDeriv completedRiemannZeta ((1 : ℂ) - z))) := by
    have hnear_zero : ∀ᶠ z in 𝓝 (1 : ℂ), z ≠ 0 :=
      eventually_ne_nhds (one_ne_zero : (1 : ℂ) ≠ 0)
    have hnear_zero' : ∀ᶠ z in 𝓝[≠] (1 : ℂ), z ≠ 0 :=
      hnear_zero.filter_mono nhdsWithin_le_nhds
    have hnear_one : ∀ᶠ z in 𝓝[≠] (1 : ℂ), z ≠ 1 :=
      self_mem_nhdsWithin
    exact
      (hnear_zero'.and hnear_one).mono
        (fun z hz =>
          completedRiemannZeta_onePole_negLogDeriv_coeff_reflects_zeroPole
            hz.left hz.right)
  exact hreflected.congr' hcongr.symm

/-- At the completed-zeta pole `1`, the raw negative logarithmic derivative has pole
coefficient `+1`. -/
theorem completedRiemannZeta_onePole_negLogDeriv_coeff_tendsto :
    Tendsto
      (fun z : ℂ => (z - 1) * (-logDeriv completedRiemannZeta z))
      (𝓝[≠] (1 : ℂ))
      (𝓝 (1 : ℂ)) := by
  exact
    completedRiemannZeta_onePole_negLogDeriv_coeff_tendsto_of_zeroPole
      completedRiemannZeta_zeroPole_negLogDeriv_coeff_tendsto

/-- At the completed-zeta pole `0`, the completed negative logarithmic derivative has
pole coefficient `+1`. -/
theorem completedZetaNegLogDeriv_zeroPole_residue_tendsto :
    Tendsto
      (fun z : ℂ => z * completedZetaNegLogDeriv z)
      (𝓝[≠] (0 : ℂ))
      (𝓝 (1 : ℂ)) := by
  exact
    completedZetaNegLogDeriv_zeroPole_residue_tendsto_of_negLogDeriv
      completedRiemannZeta_zeroPole_negLogDeriv_coeff_tendsto

/-- At the completed-zeta pole `1`, the completed negative logarithmic derivative has
pole coefficient `+1`. -/
theorem completedZetaNegLogDeriv_onePole_residue_tendsto :
    Tendsto
      (fun z : ℂ => (z - 1) * completedZetaNegLogDeriv z)
      (𝓝[≠] (1 : ℂ))
      (𝓝 (1 : ℂ)) := by
  exact
    completedZetaNegLogDeriv_onePole_residue_tendsto_of_negLogDeriv
      completedRiemannZeta_onePole_negLogDeriv_coeff_tendsto

/-- The shifted completed explicit-formula transform tends to its value at a completed zero
whenever the analytic-control package is supplied. -/
theorem zetaCompletedExplicitFormulaPhi_completedZero_shift_tendsto_of_control
    (f : ZetaAdmissibleFunction) (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hPhi : ZetaPhiAnalyticControl f) :
    Tendsto
      (fun z : ℂ => zetaCompletedExplicitFormulaPhi f (z - 1 / 2))
      (𝓝[≠] (completedZeroResidueCoordinate ρ))
      (𝓝 (zetaCompletedExplicitFormulaPhi f
        (completedZeroResidueCoordinate ρ - 1 / 2))) := by
  have hcontinuous :
      Continuous
        (fun z : ℂ => zetaCompletedExplicitFormulaPhi f (z - 1 / 2)) :=
    continuous_iff_continuousAt.mpr
      (fun z : ℂ =>
        let shift : ℂ → ℂ := fun w : ℂ => w - (1 / 2 : ℂ)
        have hshift : ContinuousAt shift z :=
          ((continuous_id.sub continuous_const).continuousAt : ContinuousAt shift z)
        have houter :
            ContinuousAt
              (fun w : ℂ => zetaCompletedExplicitFormulaPhi f w)
              (shift z) :=
          (hPhi.differentiableAt (shift z)).continuousAt
        have hcomp :
            ContinuousAt
              ((fun w : ℂ => zetaCompletedExplicitFormulaPhi f w) ∘ shift)
              z :=
          ContinuousAt.comp houter hshift
        hcomp)
  exact hcontinuous.continuousAt.tendsto.mono_left inf_le_left

theorem zetaCompletedExplicitFormulaPhi_completedZero_shift_tendsto
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    Tendsto
      (fun z : ℂ => zetaCompletedExplicitFormulaPhi f (z - 1 / 2))
      (𝓝[≠] (completedZeroResidueCoordinate ρ))
      (𝓝 (zetaCompletedExplicitFormulaPhi f
        (completedZeroResidueCoordinate ρ - 1 / 2))) := by
  exact
    zetaCompletedExplicitFormulaPhi_completedZero_shift_tendsto_of_control
      f ρ hPhi

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.BoundaryLogAssembly.Owner

/-!
# Origin Taylor transport and zero-counting consequences

This file is a sequential owner sublayer split from the Jensen formula owner.
Declaration order is preserved so downstream import behavior remains routed
through `EntireJensenFormula.Owner`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

theorem entireFunction_classicalJensenFormula_originTaylorFactor_transport_of_nonzeroAtOrigin
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0) :
    ∃ C : ℝ,
      (∀ R : ℝ,
        1 ≤ R →
        Summable
          (fun z : EntireFunctionZero F =>
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)) ∧
      (∀ ρ : ℝ,
          1 ≤ ρ →
          Summable
            (fun z : EntireFunctionZero F =>
              entireFunctionJensenRadialGapSummand F hF ρ z) ∧
          entireFunctionJensenRadialGapSum F hF ρ +
              entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
              C =
            entireFunctionJensenBoundaryLogAverage F ρ) := by
  rcases
      entireFunction_classicalJensenFormula_nonzeroAtOrigin_radialGapSum_eq_boundaryLogAverage
        F hF hF0 with
    ⟨C, hclosed, hidentity⟩
  refine ⟨C, hclosed, ?_⟩
  intro ρ hρ
  rcases hidentity ρ hρ with ⟨hsum, hradial⟩
  refine ⟨hsum, ?_⟩
  have horigin :
      entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ = 0 :=
    entireFunctionOriginMultiplicityLogRadiusContribution_eq_zero_of_ne_zero
      F hF hF0 ρ
  calc
    entireFunctionJensenRadialGapSum F hF ρ +
        entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ + C =
        entireFunctionJensenRadialGapSum F hF ρ + 0 + C := by
      exact congrArg
        (fun x : ℝ => entireFunctionJensenRadialGapSum F hF ρ + x + C)
        horigin
    _ = entireFunctionJensenRadialGapSum F hF ρ + C := by
      exact congrArg (fun x : ℝ => x + C)
        (add_zero (entireFunctionJensenRadialGapSum F hF ρ))
    _ = entireFunctionJensenBoundaryLogAverage F ρ :=
      hradial

/-- The canonical punctured quotient obtained by dividing an entire function by
its origin Taylor power away from the origin.  The removable-singularity owner
root extends this object across `0`. -/
noncomputable def entireFunction_originTaylorPuncturedQuotient
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (z : ℂ) : ℂ :=
  (z ^ entireFunctionZeroMultiplicity F hF 0)⁻¹ • F z

/-- Away from the origin, the punctured quotient reconstructs the original
function by multiplying back the origin Taylor power. -/
theorem entireFunction_originTaylorPuncturedQuotient_factorization_of_ne_zero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    {z : ℂ}
    (hz : z ≠ 0) :
    F z =
      z ^ entireFunctionZeroMultiplicity F hF 0 •
        entireFunction_originTaylorPuncturedQuotient F hF z := by
  let a : ℂ := z ^ entireFunctionZeroMultiplicity F hF 0
  have ha : a ≠ 0 :=
    pow_ne_zero (entireFunctionZeroMultiplicity F hF 0) hz
  calc
    F z = (1 : ℂ) • F z := by
      exact (one_smul ℂ (F z)).symm
    _ = (a * a⁻¹) • F z := by
      exact congrArg (fun c : ℂ => c • F z) (mul_inv_cancel₀ ha).symm
    _ = a • (a⁻¹ • F z) := by
      exact (smul_smul a a⁻¹ (F z)).symm
    _ =
        z ^ entireFunctionZeroMultiplicity F hF 0 •
          entireFunction_originTaylorPuncturedQuotient F hF z := rfl

/-- Global removal of the origin Taylor factor for a nontrivial entire
function.

This is the owner construction needed for Jensen transport: the local unit
supplied by `AnalyticAt.order_eq_nat_iff` extends to a global entire quotient
after dividing out the origin power, with the removable singularity filled in
at the origin. -/
theorem entireFunction_originTaylorFactor_entireQuotient_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ G : ℂ → ℂ,
      (∀ z : ℂ, AnalyticAt ℂ G z) ∧
      G 0 ≠ 0 ∧
      (∀ z : ℂ,
        F z =
          z ^ entireFunctionZeroMultiplicity F hF 0 • G z) := by
  let m : ℕ := entireFunctionZeroMultiplicity F hF 0
  have horder : (hF 0).order = (m : ENat) :=
    entireFunction_origin_order_eq_multiplicity_of_nontrivial F hF hnontrivial
  rcases (hF 0).order_eq_nat_iff m |>.mp horder with
    ⟨g, hg_an, hg_ne, hg_factor⟩
  let G : ℂ → ℂ :=
    fun z =>
      if z = 0 then
        g 0
      else
        entireFunction_originTaylorPuncturedQuotient F hF z
  have hG_eq_g_nhds : G =ᶠ[𝓝 (0 : ℂ)] g := by
    filter_upwards [hg_factor] with z hz_factor
    by_cases hz : z = 0
    · calc
        G z = g 0 := by
          exact if_pos hz
        _ = g z := by
          exact congrArg g hz.symm
    · have hpow : z ^ m ≠ 0 :=
        pow_ne_zero m hz
      calc
        G z =
            entireFunction_originTaylorPuncturedQuotient F hF z := by
          exact if_neg hz
        _ = (z ^ m)⁻¹ • F z := rfl
        _ = (z ^ m)⁻¹ • (z ^ m • g z) := by
          exact congrArg (fun w : ℂ => (z ^ m)⁻¹ • w) hz_factor
        _ = ((z ^ m)⁻¹ * z ^ m) • g z := by
          exact smul_smul (z ^ m)⁻¹ (z ^ m) (g z)
        _ = (1 : ℂ) • g z := by
          exact congrArg (fun a : ℂ => a • g z) (inv_mul_cancel₀ hpow)
        _ = g z := by
          exact one_smul ℂ (g z)
  have hG_origin_an : AnalyticAt ℂ G 0 :=
    hg_an.congr hG_eq_g_nhds.symm
  have hG_ne : G 0 ≠ 0 := by
    have hG0 : G 0 = g 0 := by
      exact if_pos rfl
    exact fun hzero => hg_ne (Eq.trans hG0.symm hzero)
  have hG_off_origin_an :
      ∀ z : ℂ, z ≠ 0 → AnalyticAt ℂ G z := by
    intro z hz
    have hpow_ne : z ^ m ≠ 0 :=
      pow_ne_zero m hz
    have hquot_an :
        AnalyticAt ℂ (fun w : ℂ => (w ^ m)⁻¹ * F w) z := by
      have hpow_an : AnalyticAt ℂ (fun w : ℂ => w ^ m) z :=
        (analyticAt_id : AnalyticAt ℂ (fun w : ℂ => w) z).pow m
      exact (hpow_an.inv hpow_ne).mul (hF z)
    refine hquot_an.congr ?_
    filter_upwards [isOpen_ne.mem_nhds hz] with w hw
    calc
      (w ^ m)⁻¹ * F w =
          (w ^ m)⁻¹ • F w := by
        exact (smul_eq_mul (w ^ m)⁻¹ (F w)).symm
      _ = entireFunction_originTaylorPuncturedQuotient F hF w := rfl
      _ = G w := by
        exact (if_neg hw).symm
  have hG_an : ∀ z : ℂ, AnalyticAt ℂ G z := by
    intro z
    by_cases hz : z = 0
    · exact Eq.subst (motive := fun w : ℂ => AnalyticAt ℂ G w) hz.symm hG_origin_an
    · exact hG_off_origin_an z hz
  have hfactor : ∀ z : ℂ, F z = z ^ m • G z := by
    intro z
    by_cases hz : z = 0
    · have hlocal_at_origin : F 0 = (0 - 0) ^ m • g 0 :=
        Filter.Eventually.self_of_nhds hg_factor
      calc
        F z = F 0 := by
          exact congrArg F hz
        _ = (0 - 0) ^ m • g 0 :=
          hlocal_at_origin
        _ = z ^ m • G z := by
          subst hz
          rfl
    · exact
        entireFunction_originTaylorPuncturedQuotient_factorization_of_ne_zero
          F hF hz
  exact ⟨G, hG_an, hG_ne, hfactor⟩

/-- Global removal of the origin Taylor factor for a nontrivial entire
function.

This public theorem is a thin wrapper over the removable-singularity owner root
above.  All later zero-set, multiplicity, and Jensen-transport lemmas consume
this stable public API rather than reproving the quotient construction. -/
theorem entireFunction_originTaylorFactor_entireQuotient
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ G : ℂ → ℂ,
      (∀ z : ℂ, AnalyticAt ℂ G z) ∧
      G 0 ≠ 0 ∧
      (∀ z : ℂ,
        F z =
          z ^ entireFunctionZeroMultiplicity F hF 0 • G z) := by
  exact entireFunction_originTaylorFactor_entireQuotient_ownerRoot F hF hnontrivial

/-- Away from the origin, zeros of an entire function agree with zeros of its
global origin Taylor quotient. -/
theorem entireFunction_originTaylorFactor_nonzero_zero_iff_quotient_zero
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {z : ℂ}
    (hz : z ≠ 0) :
    F z = 0 ↔ G z = 0 := by
  have hpow : z ^ entireFunctionZeroMultiplicity F hF 0 ≠ 0 :=
    pow_ne_zero (entireFunctionZeroMultiplicity F hF 0) hz
  constructor
  · intro hFz
    have hmul :
        z ^ entireFunctionZeroMultiplicity F hF 0 * G z = 0 := by
      calc
        z ^ entireFunctionZeroMultiplicity F hF 0 * G z =
            z ^ entireFunctionZeroMultiplicity F hF 0 • G z := by
          exact (smul_eq_mul
            (z ^ entireFunctionZeroMultiplicity F hF 0) (G z)).symm
        _ = F z := (hfactor z).symm
        _ = 0 := hFz
    exact (mul_eq_zero.mp hmul).resolve_left hpow
  · intro hGz
    calc
      F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z := hfactor z
      _ = z ^ entireFunctionZeroMultiplicity F hF 0 • 0 := by
        exact congrArg
          (fun w : ℂ => z ^ entireFunctionZeroMultiplicity F hF 0 • w)
          hGz
      _ = 0 :=
        smul_zero (z ^ entireFunctionZeroMultiplicity F hF 0)

/-- Multiplication by a local analytic unit preserves analytic zero
order. -/
theorem complex_smul_smul_eq_smul_mul
    (a b c : ℂ) :
    a • (b • c) = b • (a * c) := by
  calc
    a • (b • c) = a * (b * c) := by
      exact congrArg (fun x : ℂ => a * x) (smul_eq_mul b c)
    _ = (a * b) * c := (mul_assoc a b c).symm
    _ = (b * a) * c := by
      exact congrArg (fun x : ℂ => x * c) (mul_comm a b)
    _ = b * (a * c) := mul_assoc b a c
    _ = b • (a * c) := (smul_eq_mul b (a * c)).symm

theorem analyticAt_order_eq_of_eventually_eq_unit_smul
    (F G u : ℂ → ℂ)
    {z : ℂ}
    (hF : AnalyticAt ℂ F z)
    (hG : AnalyticAt ℂ G z)
    (hu : AnalyticAt ℂ u z)
    (hu_ne : u z ≠ 0)
    (hfactor : ∀ᶠ w in 𝓝 z, F w = u w • G w) :
    hF.order = hG.order := by
  by_cases hG_top : hG.order = ⊤
  · have hG_zero : ∀ᶠ w in 𝓝 z, G w = 0 :=
      (hG.order_eq_top_iff).mp hG_top
    have hF_zero : ∀ᶠ w in 𝓝 z, F w = 0 := by
      filter_upwards [hfactor, hG_zero] with w hFw hGw
      calc
        F w = u w • G w := hFw
        _ = u w • 0 := congrArg (fun x : ℂ => u w • x) hGw
        _ = 0 := smul_zero (u w)
    exact Eq.trans ((hF.order_eq_top_iff).mpr hF_zero) hG_top.symm
  · let n : ℕ := hG.order.untop hG_top
    have hG_order : hG.order = (n : ENat) := by
      exact (WithTop.coe_untop hG.order hG_top).symm
    rcases (hG.order_eq_nat_iff n).mp hG_order with
      ⟨g, hg_an, hg_ne, hg_model⟩
    have hF_order : hF.order = (n : ENat) := by
      refine (hF.order_eq_nat_iff n).mpr ?_
      refine ⟨fun w : ℂ => u w * g w, hu.mul hg_an, ?_, ?_⟩
      · exact mul_ne_zero hu_ne hg_ne
      · filter_upwards [hfactor, hg_model] with w hFw hGw
        calc
          F w = u w • G w := hFw
          _ = u w • ((w - z) ^ n • g w) := by
            exact congrArg (fun x : ℂ => u w • x) hGw
          _ = (w - z) ^ n • (u w * g w) :=
            complex_smul_smul_eq_smul_mul (u w) ((w - z) ^ n) (g w)
    exact Eq.trans hF_order hG_order.symm

/-- Multiplication by a local analytic unit preserves the file's entire-function
zero multiplicity. -/
theorem entireFunctionZeroMultiplicity_eq_of_eventually_eq_unit_smul
    (F G u : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hG : ∀ z : ℂ, AnalyticAt ℂ G z)
    {z : ℂ}
    (hu : AnalyticAt ℂ u z)
    (hu_ne : u z ≠ 0)
    (hfactor : ∀ᶠ w in 𝓝 z, F w = u w • G w) :
    entireFunctionZeroMultiplicity F hF z =
      entireFunctionZeroMultiplicity G hG z := by
  unfold entireFunctionZeroMultiplicity
  exact congrArg (fun e : ENat => e.toNat)
    (analyticAt_order_eq_of_eventually_eq_unit_smul
      F G u (hF z) (hG z) hu hu_ne hfactor)

/-- Away from the origin, removing the origin Taylor factor preserves analytic
zero multiplicity. -/
theorem entireFunction_originTaylorFactor_multiplicity_eq_quotient_of_ne_zero
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hG : ∀ z : ℂ, AnalyticAt ℂ G z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {z : ℂ}
    (hz : z ≠ 0) :
    entireFunctionZeroMultiplicity F hF z =
      entireFunctionZeroMultiplicity G hG z := by
  exact
    entireFunctionZeroMultiplicity_eq_of_eventually_eq_unit_smul
      F G
      (fun w : ℂ => w ^ entireFunctionZeroMultiplicity F hF 0)
      hF hG
      (analyticAt_id.pow (entireFunctionZeroMultiplicity F hF 0))
      (pow_ne_zero (entireFunctionZeroMultiplicity F hF 0) hz)
      (eventually_of_forall hfactor)

/-- The origin Taylor quotient identifies the nonzero-zero index types. -/
def entireFunction_originTaylorFactor_nonzeroZeroEquiv
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z) :
    EntireFunctionNonzeroZero F ≃ EntireFunctionNonzeroZero G where
  toFun z :=
    ⟨z,
      (entireFunction_originTaylorFactor_nonzero_zero_iff_quotient_zero
        F G hF hfactor z.property.2).mp z.property.1,
      z.property.2⟩
  invFun z :=
    ⟨z,
      (entireFunction_originTaylorFactor_nonzero_zero_iff_quotient_zero
        F G hF hfactor z.property.2).mpr z.property.1,
      z.property.2⟩
  left_inv z := by
    exact Subtype.ext rfl
  right_inv z := by
    exact Subtype.ext rfl

/-- Closed-disk summand on the canonical nonzero-zero index. -/
noncomputable def entireFunctionNonzeroZeroClosedDiskSummand
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
    (z : EntireFunctionNonzeroZero F) : ℝ :=
  if ‖(z : ℂ)‖ ≤ R then
    (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ)
  else
    0

/-- Radial-gap summand on the canonical nonzero-zero index. -/
noncomputable def entireFunctionNonzeroZeroRadialGapSummand
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (z : EntireFunctionNonzeroZero F) : ℝ :=
  if ‖(z : ℂ)‖ < ρ then
    (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
      Real.log (ρ / ‖(z : ℂ)‖)
  else
    0

/-- Closed-disk summands on nonzero zeros are invariant under the origin
Taylor quotient equivalence. -/
theorem entireFunction_originTaylorFactor_nonzeroClosedDiskSummand_equiv
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hG : ∀ z : ℂ, AnalyticAt ℂ G z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    (R : ℝ)
    (z : EntireFunctionNonzeroZero F) :
    entireFunctionNonzeroZeroClosedDiskSummand G hG R
        (entireFunction_originTaylorFactor_nonzeroZeroEquiv F G hF hfactor z) =
      entireFunctionNonzeroZeroClosedDiskSummand F hF R z := by
  unfold entireFunctionNonzeroZeroClosedDiskSummand
  have hmult :
      entireFunctionZeroMultiplicity G hG (z : ℂ) =
        entireFunctionZeroMultiplicity F hF (z : ℂ) :=
    (entireFunction_originTaylorFactor_multiplicity_eq_quotient_of_ne_zero
      F G hF hG hfactor z.property.2).symm
  exact
    if_congr
      (by rfl)
      (congrArg (fun n : ℕ => (n : ℝ)) hmult)
      rfl

/-- Radial-gap summands on nonzero zeros are invariant under the origin Taylor
quotient equivalence. -/
theorem entireFunction_originTaylorFactor_nonzeroRadialGapSummand_equiv
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hG : ∀ z : ℂ, AnalyticAt ℂ G z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    (ρ : ℝ)
    (z : EntireFunctionNonzeroZero F) :
    entireFunctionNonzeroZeroRadialGapSummand G hG ρ
        (entireFunction_originTaylorFactor_nonzeroZeroEquiv F G hF hfactor z) =
      entireFunctionNonzeroZeroRadialGapSummand F hF ρ z := by
  unfold entireFunctionNonzeroZeroRadialGapSummand
  have hmult :
      entireFunctionZeroMultiplicity G hG (z : ℂ) =
        entireFunctionZeroMultiplicity F hF (z : ℂ) :=
    (entireFunction_originTaylorFactor_multiplicity_eq_quotient_of_ne_zero
      F G hF hG hfactor z.property.2).symm
  exact
    if_congr
      (by rfl)
      (congrArg
        (fun n : ℕ =>
          (n : ℝ) * Real.log (ρ / ‖(z : ℂ)‖))
        hmult)
      rfl

/-- Closed-disk summability on the canonical nonzero-zero index transports
through the origin Taylor quotient. -/
theorem entireFunction_originTaylorFactor_nonzeroClosedDiskSummable_canonical
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hG : ∀ z : ℂ, AnalyticAt ℂ G z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {R : ℝ}
    (hGsum :
      Summable
        (fun z : EntireFunctionNonzeroZero G =>
          entireFunctionNonzeroZeroClosedDiskSummand G hG R z)) :
    Summable
      (fun z : EntireFunctionNonzeroZero F =>
        entireFunctionNonzeroZeroClosedDiskSummand F hF R z) := by
  let e : EntireFunctionNonzeroZero F ≃ EntireFunctionNonzeroZero G :=
    entireFunction_originTaylorFactor_nonzeroZeroEquiv F G hF hfactor
  have hcomp :
      Summable
        (fun z : EntireFunctionNonzeroZero F =>
          entireFunctionNonzeroZeroClosedDiskSummand G hG R (e z)) :=
    (e.summable_iff).mpr hGsum
  exact hcomp.congr
    (fun z =>
      entireFunction_originTaylorFactor_nonzeroClosedDiskSummand_equiv
        F G hF hG hfactor R z)

/-- Radial-gap summability on the canonical nonzero-zero index transports
through the origin Taylor quotient. -/
theorem entireFunction_originTaylorFactor_nonzeroRadialGapSummable_canonical
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hG : ∀ z : ℂ, AnalyticAt ℂ G z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {ρ : ℝ}
    (hGsum :
      Summable
        (fun z : EntireFunctionNonzeroZero G =>
          entireFunctionNonzeroZeroRadialGapSummand G hG ρ z)) :
    Summable
      (fun z : EntireFunctionNonzeroZero F =>
        entireFunctionNonzeroZeroRadialGapSummand F hF ρ z) := by
  let e : EntireFunctionNonzeroZero F ≃ EntireFunctionNonzeroZero G :=
    entireFunction_originTaylorFactor_nonzeroZeroEquiv F G hF hfactor
  have hcomp :
      Summable
        (fun z : EntireFunctionNonzeroZero F =>
          entireFunctionNonzeroZeroRadialGapSummand G hG ρ (e z)) :=
    (e.summable_iff).mpr hGsum
  exact hcomp.congr
    (fun z =>
      entireFunction_originTaylorFactor_nonzeroRadialGapSummand_equiv
        F G hF hG hfactor ρ z)

/-- The old `EntireFunctionZero` nonzero closed-disk summability surface is
equivalent to summability on the canonical nonzero-zero index. -/
theorem entireFunctionNonzeroZeroClosedDiskSummable_canonical_iff_zeroSubtype
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ) :
    Summable
        (fun z : EntireFunctionNonzeroZero F =>
          entireFunctionNonzeroZeroClosedDiskSummand F hF R z) ↔
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) := by
  let i : EntireFunctionNonzeroZero F → EntireFunctionZero F :=
    EntireFunctionNonzeroZero.toZero F
  have hi : Function.Injective i :=
    EntireFunctionNonzeroZero.toZero_injective F
  have houtside :
      ∀ z : EntireFunctionZero F,
        z ∉ Set.range i →
        entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z = 0 := by
    intro z hz_not_range
    have hz_zero : (z : ℂ) = 0 := by
      by_contra hz_ne
      exact hz_not_range
        ((EntireFunctionNonzeroZero.mem_range_toZero_iff F z).mpr hz_ne)
    unfold entireFunctionNonzeroZeroMultiplicityClosedDiskSummand
    exact if_pos hz_zero
  have hiff :
      Summable
          (fun z : EntireFunctionNonzeroZero F =>
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R (i z)) ↔
        Summable
          (fun z : EntireFunctionZero F =>
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) :=
    hi.summable_iff houtside
  have hpoint :
      (fun z : EntireFunctionNonzeroZero F =>
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R (i z)) =
        (fun z : EntireFunctionNonzeroZero F =>
          entireFunctionNonzeroZeroClosedDiskSummand F hF R z) := by
    funext z
    unfold entireFunctionNonzeroZeroMultiplicityClosedDiskSummand
    unfold entireFunctionNonzeroZeroClosedDiskSummand
    unfold entireFunctionZeroMultiplicityClosedDiskSummand
    have hz_ne : ((i z : EntireFunctionZero F) : ℂ) ≠ 0 := z.property.2
    exact if_neg hz_ne
  constructor
  · intro hcanonical
    exact hiff.mp (Eq.subst
      (motive := fun f : EntireFunctionNonzeroZero F → ℝ => Summable f)
      hpoint.symm
      hcanonical)
  · intro hold
    exact Eq.subst
      (motive := fun f : EntireFunctionNonzeroZero F → ℝ => Summable f)
      hpoint
      (hiff.mpr hold)

/-- The old `EntireFunctionZero` radial-gap summability surface is equivalent
to summability on the canonical nonzero-zero index. -/
theorem entireFunctionNonzeroZeroRadialGapSummable_canonical_iff_zeroSubtype
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ) :
    Summable
        (fun z : EntireFunctionNonzeroZero F =>
          entireFunctionNonzeroZeroRadialGapSummand F hF ρ z) ↔
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionJensenRadialGapSummand F hF ρ z) := by
  let i : EntireFunctionNonzeroZero F → EntireFunctionZero F :=
    EntireFunctionNonzeroZero.toZero F
  have hi : Function.Injective i :=
    EntireFunctionNonzeroZero.toZero_injective F
  have houtside :
      ∀ z : EntireFunctionZero F,
        z ∉ Set.range i →
        entireFunctionJensenRadialGapSummand F hF ρ z = 0 := by
    intro z hz_not_range
    have hz_zero : (z : ℂ) = 0 := by
      by_contra hz_ne
      exact hz_not_range
        ((EntireFunctionNonzeroZero.mem_range_toZero_iff F z).mpr hz_ne)
    unfold entireFunctionJensenRadialGapSummand
    exact if_pos hz_zero
  have hiff :
      Summable
          (fun z : EntireFunctionNonzeroZero F =>
            entireFunctionJensenRadialGapSummand F hF ρ (i z)) ↔
        Summable
          (fun z : EntireFunctionZero F =>
            entireFunctionJensenRadialGapSummand F hF ρ z) :=
    hi.summable_iff houtside
  have hpoint :
      (fun z : EntireFunctionNonzeroZero F =>
          entireFunctionJensenRadialGapSummand F hF ρ (i z)) =
        (fun z : EntireFunctionNonzeroZero F =>
          entireFunctionNonzeroZeroRadialGapSummand F hF ρ z) := by
    funext z
    unfold entireFunctionJensenRadialGapSummand
    unfold entireFunctionNonzeroZeroRadialGapSummand
    have hz_ne : ((i z : EntireFunctionZero F) : ℂ) ≠ 0 := z.property.2
    exact if_neg hz_ne
  constructor
  · intro hcanonical
    exact hiff.mp (Eq.subst
      (motive := fun f : EntireFunctionNonzeroZero F → ℝ => Summable f)
      hpoint.symm
      hcanonical)
  · intro hold
    exact Eq.subst
      (motive := fun f : EntireFunctionNonzeroZero F → ℝ => Summable f)
      hpoint
      (hiff.mpr hold)

/-- The old `EntireFunctionZero` radial-gap sum agrees with the canonical
nonzero-zero radial-gap sum. -/
theorem entireFunctionNonzeroZeroRadialGap_tsum_eq_zeroSubtype_tsum
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ) :
    (∑' z : EntireFunctionNonzeroZero F,
        entireFunctionNonzeroZeroRadialGapSummand F hF ρ z) =
      ∑' z : EntireFunctionZero F,
        entireFunctionJensenRadialGapSummand F hF ρ z := by
  let i : EntireFunctionNonzeroZero F → EntireFunctionZero F :=
    EntireFunctionNonzeroZero.toZero F
  have hi : Function.Injective i :=
    EntireFunctionNonzeroZero.toZero_injective F
  have houtside :
      ∀ z : EntireFunctionZero F,
        z ∉ Set.range i →
        entireFunctionJensenRadialGapSummand F hF ρ z = 0 := by
    intro z hz_not_range
    have hz_zero : (z : ℂ) = 0 := by
      by_contra hz_ne
      exact hz_not_range
        ((EntireFunctionNonzeroZero.mem_range_toZero_iff F z).mpr hz_ne)
    unfold entireFunctionJensenRadialGapSummand
    exact if_pos hz_zero
  have hpoint :
      (fun z : EntireFunctionNonzeroZero F =>
          entireFunctionJensenRadialGapSummand F hF ρ (i z)) =
        (fun z : EntireFunctionNonzeroZero F =>
          entireFunctionNonzeroZeroRadialGapSummand F hF ρ z) := by
    funext z
    unfold entireFunctionJensenRadialGapSummand
    unfold entireFunctionNonzeroZeroRadialGapSummand
    have hz_ne : ((i z : EntireFunctionZero F) : ℂ) ≠ 0 := z.property.2
    exact if_neg hz_ne
  calc
    (∑' z : EntireFunctionNonzeroZero F,
        entireFunctionNonzeroZeroRadialGapSummand F hF ρ z) =
        ∑' z : EntireFunctionNonzeroZero F,
          entireFunctionJensenRadialGapSummand F hF ρ (i z) := by
      exact congrArg
        (fun f : EntireFunctionNonzeroZero F → ℝ => ∑' z, f z)
        hpoint.symm
    _ =
        ∑' z : EntireFunctionZero F,
          entireFunctionJensenRadialGapSummand F hF ρ z :=
      hi.tsum_eq houtside

/-- The canonical nonzero-zero radial-gap sum is invariant under the origin
Taylor quotient equivalence. -/
theorem entireFunction_originTaylorFactor_nonzeroRadialGap_tsum_eq_quotient
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hG : ∀ z : ℂ, AnalyticAt ℂ G z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    (ρ : ℝ) :
    (∑' z : EntireFunctionNonzeroZero F,
        entireFunctionNonzeroZeroRadialGapSummand F hF ρ z) =
      ∑' z : EntireFunctionNonzeroZero G,
        entireFunctionNonzeroZeroRadialGapSummand G hG ρ z := by
  let e : EntireFunctionNonzeroZero F ≃ EntireFunctionNonzeroZero G :=
    entireFunction_originTaylorFactor_nonzeroZeroEquiv F G hF hfactor
  calc
    (∑' z : EntireFunctionNonzeroZero F,
        entireFunctionNonzeroZeroRadialGapSummand F hF ρ z) =
        ∑' z : EntireFunctionNonzeroZero F,
          entireFunctionNonzeroZeroRadialGapSummand G hG ρ (e z) := by
      exact congrArg
        (fun f : EntireFunctionNonzeroZero F → ℝ => ∑' z, f z)
        (funext
          (fun z =>
            (entireFunction_originTaylorFactor_nonzeroRadialGapSummand_equiv
              F G hF hG hfactor ρ z).symm))
    _ =
        ∑' z : EntireFunctionNonzeroZero G,
          entireFunctionNonzeroZeroRadialGapSummand G hG ρ z :=
      e.tsum_eq
        (fun z : EntireFunctionNonzeroZero G =>
          entireFunctionNonzeroZeroRadialGapSummand G hG ρ z)

/-- Closed-disk nonzero-zero summability transports from the global origin
Taylor quotient back to the original entire function. -/
theorem entireFunction_originTaylorFactor_nonzeroClosedDiskSummable_of_quotient
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hG : ∀ z : ℂ, AnalyticAt ℂ G z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {R : ℝ}
    (hR : 1 ≤ R)
    (hGsum :
      Summable
        (fun z : EntireFunctionZero G =>
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand G hG R z)) :
    Summable
      (fun z : EntireFunctionZero F =>
        entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) := by
  have hGcanonical :
      Summable
        (fun z : EntireFunctionNonzeroZero G =>
          entireFunctionNonzeroZeroClosedDiskSummand G hG R z) :=
    (entireFunctionNonzeroZeroClosedDiskSummable_canonical_iff_zeroSubtype
      G hG R).mpr hGsum
  have hFcanonical :
      Summable
        (fun z : EntireFunctionNonzeroZero F =>
          entireFunctionNonzeroZeroClosedDiskSummand F hF R z) :=
    entireFunction_originTaylorFactor_nonzeroClosedDiskSummable_canonical
      F G hF hG hfactor hGcanonical
  exact
    (entireFunctionNonzeroZeroClosedDiskSummable_canonical_iff_zeroSubtype
      F hF R).mp hFcanonical

/-- Radial-gap summability and radial-gap sums transport through the global
origin Taylor quotient. -/
theorem entireFunction_originTaylorFactor_radialGapSum_eq_quotient_radialGapSum
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hG : ∀ z : ℂ, AnalyticAt ℂ G z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ)
    (hGsum :
      Summable
        (fun z : EntireFunctionZero G =>
          entireFunctionJensenRadialGapSummand G hG ρ z)) :
    Summable
      (fun z : EntireFunctionZero F =>
        entireFunctionJensenRadialGapSummand F hF ρ z) ∧
      entireFunctionJensenRadialGapSum F hF ρ =
        entireFunctionJensenRadialGapSum G hG ρ := by
  have hGcanonical :
      Summable
        (fun z : EntireFunctionNonzeroZero G =>
          entireFunctionNonzeroZeroRadialGapSummand G hG ρ z) :=
    (entireFunctionNonzeroZeroRadialGapSummable_canonical_iff_zeroSubtype
      G hG ρ).mpr hGsum
  have hFcanonical :
      Summable
        (fun z : EntireFunctionNonzeroZero F =>
          entireFunctionNonzeroZeroRadialGapSummand F hF ρ z) :=
    entireFunction_originTaylorFactor_nonzeroRadialGapSummable_canonical
      F G hF hG hfactor hGcanonical
  have hFsum :
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionJensenRadialGapSummand F hF ρ z) :=
    (entireFunctionNonzeroZeroRadialGapSummable_canonical_iff_zeroSubtype
      F hF ρ).mp hFcanonical
  refine ⟨hFsum, ?_⟩
  unfold entireFunctionJensenRadialGapSum
  calc
    (∑' z : EntireFunctionZero F,
        entireFunctionJensenRadialGapSummand F hF ρ z) =
        ∑' z : EntireFunctionNonzeroZero F,
          entireFunctionNonzeroZeroRadialGapSummand F hF ρ z := by
      exact
        (entireFunctionNonzeroZeroRadialGap_tsum_eq_zeroSubtype_tsum
          F hF ρ).symm
    _ =
        ∑' z : EntireFunctionNonzeroZero G,
          entireFunctionNonzeroZeroRadialGapSummand G hG ρ z :=
      entireFunction_originTaylorFactor_nonzeroRadialGap_tsum_eq_quotient
        F G hF hG hfactor ρ
    _ =
        ∑' z : EntireFunctionZero G,
          entireFunctionJensenRadialGapSummand G hG ρ z :=
      entireFunctionNonzeroZeroRadialGap_tsum_eq_zeroSubtype_tsum G hG ρ

/-- Interval-integral transport across a finite exceptional set.

This theorem is the measure-theoretic root underneath the origin-factor
boundary integral comparison.  Once a finite set `S` contains all logarithmic
singular parameters and the two integrands agree off `S` on `[0,2π]`, the
interval integral sees only the off-exception identity. -/
theorem intervalIntegral_eq_of_finite_exception_congr
    (u v : ℝ → ℝ)
    (S : Set ℝ)
    (hS : S.Finite)
    (hcongr :
      ∀ θ : ℝ,
        θ ∈ Set.Icc 0 (2 * Real.pi) →
        θ ∉ S →
        u θ = v θ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), u θ) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), v θ := by
  refine intervalIntegral.integral_congr_ae ?_
  have hAeNotMem :
      ∀ᵐ θ ∂MeasureTheory.volume, θ ∉ S :=
    hS.countable.ae_not_mem MeasureTheory.volume
  filter_upwards [hAeNotMem] with θ hθ_not_mem hθ_interval
  have hθ_uIcc :
      θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi) :=
    Set.uIoc_subset_uIcc hθ_interval
  have hθ_Icc :
      θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
    have hle : (0 : ℝ) ≤ 2 * Real.pi :=
      le_of_lt Real.two_pi_pos
    exact Eq.subst
      (motive := fun T : Set ℝ => θ ∈ T)
      (Set.uIcc_of_le hle)
      hθ_uIcc
  exact hcongr θ hθ_Icc hθ_not_mem

/-- Finite-exception transport to a constant-plus integrand. -/
theorem intervalIntegral_eq_const_add_of_finite_exception_congr
    (u v : ℝ → ℝ)
    (c : ℝ)
    (S : Set ℝ)
    (hS : S.Finite)
    (hcongr :
      ∀ θ : ℝ,
        θ ∈ Set.Icc 0 (2 * Real.pi) →
        θ ∉ S →
        u θ = c + v θ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), u θ) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), c + v θ := by
  exact
    intervalIntegral_eq_of_finite_exception_congr
      u
      (fun θ : ℝ => c + v θ)
      S
      hS
      hcongr

/-- Interval integration of a constant plus an interval-integrable remainder. -/
theorem intervalIntegral_const_add_eq_length_smul_add
    (v : ℝ → ℝ)
    (c a b : ℝ)
    (hv :
      IntervalIntegrable v MeasureTheory.volume a b) :
    (∫ θ in a..b, c + v θ) =
      (b - a) • c + ∫ θ in a..b, v θ := by
  have hconst :
      IntervalIntegrable (fun _θ : ℝ => c) MeasureTheory.volume a b :=
    Continuous.intervalIntegrable continuous_const a b
  calc
    (∫ θ in a..b, c + v θ) =
        ∫ θ in a..b, (fun _θ : ℝ => c) θ + v θ := rfl
    _ =
        (∫ _θ in a..b, c) + ∫ θ in a..b, v θ := by
      exact intervalIntegral.integral_add hconst hv
    _ =
        (b - a) • c + ∫ θ in a..b, v θ := by
      exact congrArg
        (fun x : ℝ => x + ∫ θ in a..b, v θ)
        (intervalIntegral.integral_const c)

/-- Finite-exception constant-plus transport, including the constant-integral
evaluation, on the Jensen boundary interval. -/
theorem intervalIntegral_finiteException_const_add_eq_twoPi_smul_add
    (u v : ℝ → ℝ)
    (c : ℝ)
    (S : Set ℝ)
    (hS : S.Finite)
    (hcongr :
      ∀ θ : ℝ,
        θ ∈ Set.Icc 0 (2 * Real.pi) →
        θ ∉ S →
        u θ = c + v θ)
    (hv :
      IntervalIntegrable v MeasureTheory.volume
        (0 : ℝ) (2 * Real.pi)) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), u θ) =
      (2 * Real.pi - 0) • c +
        ∫ θ in (0 : ℝ)..(2 * Real.pi), v θ := by
  calc
    (∫ θ in (0 : ℝ)..(2 * Real.pi), u θ) =
        ∫ θ in (0 : ℝ)..(2 * Real.pi), c + v θ :=
      intervalIntegral_eq_const_add_of_finite_exception_congr
        u v c S hS hcongr
    _ =
        (2 * Real.pi - 0) • c +
          ∫ θ in (0 : ℝ)..(2 * Real.pi), v θ :=
      intervalIntegral_const_add_eq_length_smul_add
        v c (0 : ℝ) (2 * Real.pi) hv

/-- A nonnegative real radius has the same norm after embedding in `ℂ`. -/
theorem complex_norm_ofReal_of_nonnegative
    {r : ℝ}
    (hr : 0 ≤ r) :
    ‖(r : ℂ)‖ = r := by
  have hnorm_real : ‖(r : ℂ)‖ = ‖r‖ :=
    Complex.norm_real r
  have hreal_norm_abs : ‖r‖ = |r| :=
    Real.norm_eq_abs r
  have habs : |r| = r :=
    abs_of_nonneg hr
  exact hnorm_real.trans (hreal_norm_abs.trans habs)

/-- The Jensen circle parametrization has the requested radius. -/
theorem entireFunctionJensenBoundaryCircle_norm
    {R θ : ℝ}
    (hR : 0 ≤ R) :
    ‖(R : ℂ) * Complex.exp (θ * Complex.I)‖ = R := by
  have hR_norm : ‖(R : ℂ)‖ = R :=
    complex_norm_ofReal_of_nonnegative hR
  have hExp_norm : ‖Complex.exp (θ * Complex.I)‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I θ
  calc
    ‖(R : ℂ) * Complex.exp (θ * Complex.I)‖ =
        ‖(R : ℂ)‖ * ‖Complex.exp (θ * Complex.I)‖ := by
      exact norm_mul (R : ℂ) (Complex.exp (θ * Complex.I))
    _ = R * 1 := by
      exact congrArg₂ HMul.hMul hR_norm hExp_norm
    _ = R := mul_one R

/-- The origin Taylor quotient gives the expected boundary-circle norm
factorization at every sample. -/
theorem entireFunction_originTaylorFactor_boundaryCircle_norm_factorization
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {R θ : ℝ}
    (hR : 0 ≤ R) :
    ‖F ((R : ℂ) * Complex.exp (θ * Complex.I))‖ =
      R ^ entireFunctionZeroMultiplicity F hF 0 *
        ‖G ((R : ℂ) * Complex.exp (θ * Complex.I))‖ := by
  let z : ℂ := (R : ℂ) * Complex.exp (θ * Complex.I)
  have hz_norm : ‖z‖ = R :=
    entireFunctionJensenBoundaryCircle_norm hR
  calc
    ‖F ((R : ℂ) * Complex.exp (θ * Complex.I))‖ =
        ‖F z‖ := rfl
    _ = ‖z ^ entireFunctionZeroMultiplicity F hF 0 • G z‖ := by
      exact congrArg norm (hfactor z)
    _ =
        ‖z ^ entireFunctionZeroMultiplicity F hF 0‖ * ‖G z‖ := by
      exact norm_smul (z ^ entireFunctionZeroMultiplicity F hF 0) (G z)
    _ =
        ‖z‖ ^ entireFunctionZeroMultiplicity F hF 0 * ‖G z‖ := by
      exact congrArg
        (fun x : ℝ => x * ‖G z‖)
        (norm_pow z (entireFunctionZeroMultiplicity F hF 0))
    _ =
        R ^ entireFunctionZeroMultiplicity F hF 0 * ‖G z‖ := by
      exact congrArg
        (fun x : ℝ => x ^ entireFunctionZeroMultiplicity F hF 0 * ‖G z‖)
        hz_norm
    _ =
        R ^ entireFunctionZeroMultiplicity F hF 0 *
          ‖G ((R : ℂ) * Complex.exp (θ * Complex.I))‖ := rfl

/-- At boundary samples where the quotient does not vanish and the radius is
positive, the origin Taylor quotient contributes exactly `m log R` to the
Jensen logarithmic integrand. -/
theorem entireFunction_originTaylorFactor_boundaryLogIntegrand_eq_of_quotient_ne
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {R θ : ℝ}
    (hR : 0 < R)
    (hG :
      G ((R : ℂ) * Complex.exp (θ * Complex.I)) ≠ 0) :
    entireFunctionJensenBoundaryLogIntegrand F R θ =
      (entireFunctionZeroMultiplicity F hF 0 : ℝ) * Real.log R +
        entireFunctionJensenBoundaryLogIntegrand G R θ := by
  have hR_nonneg : 0 ≤ R := hR.le
  have hnorm :
      ‖F ((R : ℂ) * Complex.exp (θ * Complex.I))‖ =
        R ^ entireFunctionZeroMultiplicity F hF 0 *
          ‖G ((R : ℂ) * Complex.exp (θ * Complex.I))‖ :=
    entireFunction_originTaylorFactor_boundaryCircle_norm_factorization
      F G hF hfactor hR_nonneg
  have hpow_ne :
      R ^ entireFunctionZeroMultiplicity F hF 0 ≠ 0 :=
    pow_ne_zero (entireFunctionZeroMultiplicity F hF 0) hR.ne'
  have hG_norm_ne :
      ‖G ((R : ℂ) * Complex.exp (θ * Complex.I))‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hG
  unfold entireFunctionJensenBoundaryLogIntegrand
  calc
    Real.log ‖F ((R : ℂ) * Complex.exp (θ * Complex.I))‖ =
        Real.log
          (R ^ entireFunctionZeroMultiplicity F hF 0 *
            ‖G ((R : ℂ) * Complex.exp (θ * Complex.I))‖) := by
      exact congrArg Real.log hnorm
    _ =
        Real.log (R ^ entireFunctionZeroMultiplicity F hF 0) +
          Real.log ‖G ((R : ℂ) * Complex.exp (θ * Complex.I))‖ := by
      exact Real.log_mul hpow_ne hG_norm_ne
    _ =
        (entireFunctionZeroMultiplicity F hF 0 : ℝ) * Real.log R +
          Real.log ‖G ((R : ℂ) * Complex.exp (θ * Complex.I))‖ := by
      exact congrArg
        (fun x : ℝ =>
          x + Real.log ‖G ((R : ℂ) * Complex.exp (θ * Complex.I))‖)
        (Real.log_pow R (entireFunctionZeroMultiplicity F hF 0))

/-- Boundary parameters where the quotient factor vanishes on the Jensen
circle.  These are exactly the finite exceptional parameters for the
origin-factor boundary-integral transport. -/
def entireFunctionJensenQuotientBoundaryZeroParameters
    (G : ℂ → ℂ)
    (R : ℝ) : Set ℝ :=
  {θ : ℝ | θ ∈ Set.Icc 0 (2 * Real.pi) ∧
    G ((R : ℂ) * Complex.exp (θ * Complex.I)) = 0}

/-- Outside the quotient boundary-zero parameter set, the quotient sample is
nonzero. -/
theorem entireFunctionJensenQuotientBoundary_sample_ne_of_not_mem_zeroParameters
    (G : ℂ → ℂ)
    {R θ : ℝ}
    (hθ :
      θ ∉ entireFunctionJensenQuotientBoundaryZeroParameters G R)
    (hθI : θ ∈ Set.Icc 0 (2 * Real.pi)) :
    G ((R : ℂ) * Complex.exp (θ * Complex.I)) ≠ 0 := by
  intro hzero
  exact hθ ⟨hθI, hzero⟩

/-- Off the finite quotient boundary-zero set, the origin Taylor factor gives
the pointwise logarithmic boundary identity. -/
theorem entireFunction_originTaylorFactor_boundaryLogIntegrand_eq_off_quotientZeroParameters
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {R θ : ℝ}
    (hR : 0 < R)
    (hθ :
      θ ∉ entireFunctionJensenQuotientBoundaryZeroParameters G R)
    (hθI : θ ∈ Set.Icc 0 (2 * Real.pi)) :
    entireFunctionJensenBoundaryLogIntegrand F R θ =
      entireFunctionOriginMultiplicityLogRadiusContribution F hF R +
        entireFunctionJensenBoundaryLogIntegrand G R θ := by
  have hG :
      G ((R : ℂ) * Complex.exp (θ * Complex.I)) ≠ 0 :=
    entireFunctionJensenQuotientBoundary_sample_ne_of_not_mem_zeroParameters
      G hθ hθI
  exact
    entireFunction_originTaylorFactor_boundaryLogIntegrand_eq_of_quotient_ne
      F G hF hfactor hR hG

/-- If the boundary parametrization is injective on the fundamental arc and
the circle zero set is finite, then the quotient boundary-zero parameters are
finite. -/
theorem entireFunctionJensenQuotientBoundaryZeroParameters_finite_of_injectiveOn
    (G : ℂ → ℂ)
    (R : ℝ)
    (hR : 0 ≤ R)
    (hInj :
      Set.InjOn
        (fun θ : ℝ => (R : ℂ) * Complex.exp (θ * Complex.I))
        (Set.Ioc 0 (2 * Real.pi)))
    (hCircle : Set.Finite {z : ℂ | ‖z‖ = R ∧ G z = 0}) :
    (entireFunctionJensenQuotientBoundaryZeroParameters G R).Finite := by
  let f : {θ : ℝ // θ ∈ Set.Ioc 0 (2 * Real.pi)} → ℂ :=
    fun θ => (R : ℂ) * Complex.exp (θ * Complex.I)
  have hInjSubtype : Function.Injective f := by
    intro a b hEq
    apply Subtype.ext
    exact hInj a.2 b.2 hEq
  have hpre : (f ⁻¹' {z : ℂ | ‖z‖ = R ∧ G z = 0}).Finite :=
    hCircle.preimage fun _ _ _ _ hEq => hInjSubtype hEq
  have hIocFinite :
      {θ : ℝ | θ ∈ Set.Ioc 0 (2 * Real.pi) ∧
        G ((R : ℂ) * Complex.exp (θ * Complex.I)) = 0}.Finite := by
    simpa [f, Set.preimage, entireFunctionJensenBoundaryCircle_norm hR]
      using hpre
  have hsubset :
      entireFunctionJensenQuotientBoundaryZeroParameters G R ⊆
        insert (0 : ℝ)
          {θ : ℝ | θ ∈ Set.Ioc 0 (2 * Real.pi) ∧
            G ((R : ℂ) * Complex.exp (θ * Complex.I)) = 0} := by
    intro θ hθ
    by_cases hθ0 : θ = 0
    · exact hθ0 ▸ Set.mem_insert (0 : ℝ) _
    · exact Set.mem_insert_iff.mpr
        (Or.inr ⟨⟨lt_of_le_of_ne hθ.1.1 hθ0.symm, hθ.1.2⟩, hθ.2⟩)
  exact (hIocFinite.insert (0 : ℝ)).subset hsubset

/-- The finite-exception data needed by origin Taylor boundary-integral
transport: the quotient-zero exceptional set is finite, and away from it the
boundary logarithmic integrands differ by the constant origin contribution. -/
theorem entireFunction_originTaylorFactor_boundaryLogIntegrand_finiteExceptionCertificate
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {R : ℝ}
    (hR_pos : 0 < R)
    (hInj :
      Set.InjOn
        (fun θ : ℝ => (R : ℂ) * Complex.exp (θ * Complex.I))
        (Set.Ioc 0 (2 * Real.pi)))
    (hCircle : Set.Finite {z : ℂ | ‖z‖ = R ∧ G z = 0}) :
    (entireFunctionJensenQuotientBoundaryZeroParameters G R).Finite ∧
      ∀ θ : ℝ,
        θ ∈ Set.Icc 0 (2 * Real.pi) →
        θ ∉ entireFunctionJensenQuotientBoundaryZeroParameters G R →
        entireFunctionJensenBoundaryLogIntegrand F R θ =
          entireFunctionOriginMultiplicityLogRadiusContribution F hF R +
            entireFunctionJensenBoundaryLogIntegrand G R θ := by
  have hfinite :
      (entireFunctionJensenQuotientBoundaryZeroParameters G R).Finite :=
    entireFunctionJensenQuotientBoundaryZeroParameters_finite_of_injectiveOn
      G R hR_pos.le hInj hCircle
  refine ⟨hfinite, ?_⟩
  intro θ hθI hθnot
  exact
    entireFunction_originTaylorFactor_boundaryLogIntegrand_eq_off_quotientZeroParameters
      F G hF hfactor hR_pos hθnot hθI

/-- A positive-radius Jensen boundary sample is away from the origin. -/
theorem entireFunctionJensenBoundaryCircle_sample_ne_zero_of_pos
    {R θ : ℝ}
    (hR : 0 < R) :
    (R : ℂ) * Complex.exp (θ * Complex.I) ≠ 0 := by
  have hnorm :
      ‖(R : ℂ) * Complex.exp (θ * Complex.I)‖ = R :=
    entireFunctionJensenBoundaryCircle_norm hR.le
  intro hzero
  have hR_zero : R = 0 := by
    calc
      R = ‖(R : ℂ) * Complex.exp (θ * Complex.I)‖ := hnorm.symm
      _ = ‖(0 : ℂ)‖ := congrArg norm hzero
      _ = 0 := norm_zero
  exact hR.ne' hR_zero

/-- On a positive-radius Jensen circle, the origin Taylor quotient has the
same boundary-zero parameters as the original function. -/
theorem entireFunction_originTaylorFactor_boundaryCircle_zero_iff_quotient_zero
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {R θ : ℝ}
    (hR : 0 < R) :
    F ((R : ℂ) * Complex.exp (θ * Complex.I)) = 0 ↔
      G ((R : ℂ) * Complex.exp (θ * Complex.I)) = 0 := by
  exact
    entireFunction_originTaylorFactor_nonzero_zero_iff_quotient_zero
      F G hF hfactor
      (entireFunctionJensenBoundaryCircle_sample_ne_zero_of_pos hR)

/-- A point on a positive-radius circle is away from the origin. -/
theorem complex_ne_zero_of_norm_eq_pos_radius
    {z : ℂ}
    {R : ℝ}
    (hR : 0 < R)
    (hz : ‖z‖ = R) :
    z ≠ 0 := by
  intro hzero
  have hR_zero : R = 0 := by
    calc
      R = ‖z‖ := hz.symm
      _ = ‖(0 : ℂ)‖ := congrArg norm hzero
      _ = 0 := norm_zero
  exact hR.ne' hR_zero

/-- On a positive-radius circle, the origin Taylor quotient has exactly the
same circle-zero set as the original function. -/
theorem entireFunction_originTaylorFactor_circleZeroSet_eq_quotient_circleZeroSet
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {R : ℝ}
    (hR : 0 < R) :
    {z : ℂ | ‖z‖ = R ∧ F z = 0} =
      {z : ℂ | ‖z‖ = R ∧ G z = 0} := by
  ext z
  constructor
  · intro hz
    have hz_ne : z ≠ 0 :=
      complex_ne_zero_of_norm_eq_pos_radius hR hz.1
    exact
      ⟨hz.1,
        (entireFunction_originTaylorFactor_nonzero_zero_iff_quotient_zero
          F G hF hfactor hz_ne).mp hz.2⟩
  · intro hz
    have hz_ne : z ≠ 0 :=
      complex_ne_zero_of_norm_eq_pos_radius hR hz.1
    exact
      ⟨hz.1,
        (entireFunction_originTaylorFactor_nonzero_zero_iff_quotient_zero
          F G hF hfactor hz_ne).mpr hz.2⟩

/-- Finiteness of quotient zeros on a positive-radius circle transports back
through the origin Taylor factor. -/
theorem entireFunction_originTaylorFactor_circleZeroSet_finite_of_quotient
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {R : ℝ}
    (hR : 0 < R)
    (hGfinite : Set.Finite {z : ℂ | ‖z‖ = R ∧ G z = 0}) :
    Set.Finite {z : ℂ | ‖z‖ = R ∧ F z = 0} := by
  exact
    Eq.subst
      (motive := fun S : Set ℂ => Set.Finite S)
      (entireFunction_originTaylorFactor_circleZeroSet_eq_quotient_circleZeroSet
        F G hF hfactor hR).symm
      hGfinite

/-- The boundary logarithmic integrand is bounded by the logarithmic maximum once the
circle log set is known to be bounded above. -/
theorem entireFunctionJensenBoundaryLogIntegrand_le_logMaxOnCircle
    (F : ℂ → ℂ)
    {R : ℝ}
    (hR : 0 ≤ R)
    (hbdd :
      BddAbove {x : ℝ | ∃ z : ℂ, ‖z‖ = R ∧ x = Real.log ‖F z‖})
    (θ : ℝ) :
    entireFunctionJensenBoundaryLogIntegrand F R θ ≤
      entireFunctionLogMaxOnCircle F R := by
  unfold entireFunctionJensenBoundaryLogIntegrand
  unfold entireFunctionLogMaxOnCircle
  exact le_csSup hbdd
    ⟨(R : ℂ) * Complex.exp (θ * Complex.I),
      entireFunctionJensenBoundaryCircle_norm hR,
      rfl⟩

/-- The normalized Jensen boundary average is bounded by the logarithmic maximum. -/
theorem entireFunctionJensenBoundaryLogAverage_le_logMaxOnCircle
    (F : ℂ → ℂ)
    {R : ℝ}
    (hR : 0 ≤ R)
    (hbdd :
      BddAbove {x : ℝ | ∃ z : ℂ, ‖z‖ = R ∧ x = Real.log ‖F z‖})
    (hint :
      IntervalIntegrable
        (entireFunctionJensenBoundaryLogIntegrand F R)
        MeasureTheory.volume
        (0 : ℝ)
        (2 * Real.pi)) :
    entireFunctionJensenBoundaryLogAverage F R ≤
      entireFunctionLogMaxOnCircle F R := by
  unfold entireFunctionJensenBoundaryLogAverage
  have htwo_pi_nonneg : 0 ≤ 2 * Real.pi :=
    le_of_lt Real.two_pi_pos
  have hconst_int :
      IntervalIntegrable
        (fun _ : ℝ => entireFunctionLogMaxOnCircle F R)
        MeasureTheory.volume
        (0 : ℝ)
        (2 * Real.pi) :=
    Continuous.intervalIntegrable continuous_const (0 : ℝ) (2 * Real.pi)
  have hintegral_le :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
          entireFunctionJensenBoundaryLogIntegrand F R θ) ≤
        ∫ _θ in (0 : ℝ)..(2 * Real.pi),
          entireFunctionLogMaxOnCircle F R := by
    exact intervalIntegral.integral_mono_on
      htwo_pi_nonneg
      hint
      hconst_int
      (fun θ _hθ =>
        entireFunctionJensenBoundaryLogIntegrand_le_logMaxOnCircle F hR hbdd θ)
  have hconst_eval :
      (∫ _θ in (0 : ℝ)..(2 * Real.pi),
          entireFunctionLogMaxOnCircle F R) =
        (2 * Real.pi) * entireFunctionLogMaxOnCircle F R := by
    simp [intervalIntegral.integral_const, sub_zero, Algebra.id.smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc]
  have hscale_nonneg : 0 ≤ (2 * Real.pi)⁻¹ :=
    inv_nonneg.mpr htwo_pi_nonneg
  have hscaled :
      (2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            entireFunctionJensenBoundaryLogIntegrand F R θ) ≤
        (2 * Real.pi)⁻¹ *
          ((2 * Real.pi) * entireFunctionLogMaxOnCircle F R) := by
    exact mul_le_mul_of_nonneg_left
      (hintegral_le.trans_eq hconst_eval)
      hscale_nonneg
  have hcollapse :
      (2 * Real.pi)⁻¹ *
          ((2 * Real.pi) * entireFunctionLogMaxOnCircle F R) =
        entireFunctionLogMaxOnCircle F R := by
    calc
      (2 * Real.pi)⁻¹ *
          ((2 * Real.pi) * entireFunctionLogMaxOnCircle F R) =
          ((2 * Real.pi)⁻¹ * (2 * Real.pi)) *
            entireFunctionLogMaxOnCircle F R := by
        ring
      _ = 1 * entireFunctionLogMaxOnCircle F R := by
        exact congrArg
          (fun x : ℝ => x * entireFunctionLogMaxOnCircle F R)
          (inv_mul_cancel₀ Real.two_pi_pos.ne')
      _ = entireFunctionLogMaxOnCircle F R := one_mul _
  exact hscaled.trans_eq hcollapse

/-- Boundary regularity for Jensen's logarithmic average on doubled circles.

For a nontrivial entire function, the boundary logarithm has only isolated
logarithmic singularities on each circle.  Consequently the circle log set is
bounded above and the logarithmic boundary integrand is interval-integrable. -/
theorem entireFunction_jensenBoundaryLogSet_bddAbove
  (F : ℂ → ℂ)
  (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
  (R : ℝ) :
    BddAbove {x : ℝ | ∃ z : ℂ, ‖z‖ = 2 * R ∧ x = Real.log ‖F z‖} := by
  have hcontF : Continuous F :=
    continuous_iff_continuousAt.mpr (fun z => (hF z).continuousAt)
  have hcont_norm : Continuous fun z : ℂ => ‖F z‖ :=
    continuous_norm.comp hcontF
  have hcompact : IsCompact (Metric.closedBall (0 : ℂ) (2 * R)) := by
    simpa [Metric.closedBall, dist_eq_norm] using
      (isCompact_closedBall (0 : ℂ) (2 * R))
  obtain ⟨M, hM⟩ := hcompact.bddAbove_image hcont_norm.continuousOn
  refine ⟨M, ?_⟩
  intro x hx
  rcases hx with ⟨z, hz, rfl⟩
  have hzball : z ∈ Metric.closedBall (0 : ℂ) (2 * R) := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using le_of_eq hz
  have hnorm_le : ‖F z‖ ≤ M := by
    exact hM ⟨z, hzball, rfl⟩
  exact le_trans (Real.log_le_self (norm_nonneg (F z))) hnorm_le

/-- The zero set of a nontrivial entire function meets each doubled Jensen circle
in a finite set. This is the compactness-and-isolated-zeros input behind the
boundary regularity theorem. -/
theorem entireFunction_zeroSet_finite_on_compact_of_discrete
    {S : Set ℂ}
    (hdisc : DiscreteTopology S)
    (hcomp : IsCompact S) :
    S.Finite := by
  haveI : DiscreteTopology S := hdisc
  exact hcomp.finite_of_discrete

/-- The zero set of a nontrivial entire function is discrete on each fixed
Jensen circle. -/
theorem entireFunction_jensenCircleZeros_discreteTopology
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (R : ℝ) :
    DiscreteTopology {z : ℂ | ‖z‖ = 2 * R ∧ F z = 0} := by
  refine (discreteTopology_subtype_iff).2 ?_
  intro x hx
  rcases hx with ⟨hxnorm, hxzero⟩
  have hne : ∀ᶠ w in 𝓝[≠] x, F w ≠ 0 := by
    rcases (hF x).eventually_eq_zero_or_eventually_ne_zero with hzero | hne
    · exfalso
      have hU : AnalyticOnNhd ℂ F (Set.univ : Set ℂ) := fun z _ => hF z
      have hEq : EqOn F 0 (Set.univ : Set ℂ) :=
        hU.eqOn_zero_of_preconnected_of_eventuallyEq_zero
          isPreconnected_univ (by simp) hzero
      rcases hnontrivial with ⟨z0, hz0⟩
      exact hz0 (hEq (by simp))
    · exact hne
  have hScompl :
      ({z : ℂ | ‖z‖ = 2 * R ∧ F z = 0}ᶜ) ∈ 𝓝[≠] x := by
    exact Filter.mem_of_superset hne (by
      intro w hw
      intro hsw
      exact hw hsw.2)
  exact (Filter.disjoint_principal_right).2 hScompl

/-- The zero set of a nontrivial entire function is discrete on each fixed
circle of radius `r`. -/
theorem entireFunction_circleZeros_discreteTopology
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (r : ℝ) :
    DiscreteTopology {z : ℂ | ‖z‖ = r ∧ F z = 0} := by
  refine (discreteTopology_subtype_iff).2 ?_
  intro x hx
  rcases hx with ⟨hxnorm, hxzero⟩
  have hne : ∀ᶠ w in 𝓝[≠] x, F w ≠ 0 := by
    rcases (hF x).eventually_eq_zero_or_eventually_ne_zero with hzero | hne
    · exfalso
      have hU : AnalyticOnNhd ℂ F (Set.univ : Set ℂ) := fun z _ => hF z
      have hEq : EqOn F 0 (Set.univ : Set ℂ) :=
        hU.eqOn_zero_of_preconnected_of_eventuallyEq_zero
          isPreconnected_univ (by simp) hzero
      rcases hnontrivial with ⟨z0, hz0⟩
      exact hz0 (hEq (by simp))
    · exact hne
  have hScompl :
      ({z : ℂ | ‖z‖ = r ∧ F z = 0}ᶜ) ∈ 𝓝[≠] x := by
    exact Filter.mem_of_superset hne (by
      intro w hw
      intro hsw
      exact hw hsw.2)
  exact (Filter.disjoint_principal_right).2 hScompl

/-- The zero set of a nontrivial entire function meets each fixed circle in a
finite set. -/
theorem entireFunction_circleZeros_finite
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (r : ℝ) :
    Set.Finite {z : ℂ | ‖z‖ = r ∧ F z = 0} := by
  have hdisc := entireFunction_circleZeros_discreteTopology F hF hnontrivial r
  have hcircleClosed : IsClosed {z : ℂ | ‖z‖ = r} := by
    change IsClosed ((fun z : ℂ => ‖z‖) ⁻¹' ({r} : Set ℝ))
    exact (continuous_norm : Continuous fun z : ℂ => ‖z‖).isClosed_preimage
      (isClosed_singleton : IsClosed ({r} : Set ℝ))
  have hzeroClosed : IsClosed {z : ℂ | F z = 0} := by
    have hcontF : Continuous F :=
      continuous_iff_continuousAt.mpr (fun z => (hF z).continuousAt)
    change IsClosed (F ⁻¹' ({0} : Set ℂ))
    exact hcontF.isClosed_preimage (isClosed_singleton : IsClosed ({0} : Set ℂ))
  have hclosed : IsClosed {z : ℂ | ‖z‖ = r ∧ F z = 0} := by
    change IsClosed ({z : ℂ | ‖z‖ = r} ∩ {z : ℂ | F z = 0})
    exact hcircleClosed.inter hzeroClosed
  have hsubset :
      {z : ℂ | ‖z‖ = r ∧ F z = 0} ⊆ Metric.closedBall (0 : ℂ) r := by
    intro z hz
    have hnorm_le : ‖(z : ℂ)‖ ≤ r := hz.1.le
    simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm_le
  have hcomp : IsCompact {z : ℂ | ‖z‖ = r ∧ F z = 0} :=
    (isCompact_closedBall (0 : ℂ) r).of_isClosed_subset hclosed hsubset
  exact entireFunction_zeroSet_finite_on_compact_of_discrete
    (S := {z : ℂ | ‖z‖ = r ∧ F z = 0}) hdisc hcomp

/-- The zero set of a nontrivial entire function meets each doubled Jensen circle
in a finite set. This is the compactness-and-isolated-zeros input behind the
boundary regularity theorem. -/
theorem entireFunction_jensenCircleZeros_finite
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (R : ℝ) :
    Set.Finite {z : ℂ | ‖z‖ = 2 * R ∧ F z = 0} := by
  exact entireFunction_circleZeros_finite F hF hnontrivial (2 * R)

/-- The Jensen boundary logarithmic integrand is continuous when the doubled circle
contains no zeros. -/
theorem entireFunction_jensenBoundaryLogIntegrand_continuous_of_circleZeroFree
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
    (hzero : ∀ θ : ℝ, F ((2 * R : ℂ) * Complex.exp (θ * Complex.I)) ≠ 0) :
    Continuous (entireFunctionJensenBoundaryLogIntegrand F (2 * R)) := by
  dsimp [entireFunctionJensenBoundaryLogIntegrand]
  have hmul : Continuous (fun θ : ℝ => θ * Complex.I) := by
    continuity
  have hparam : Continuous (fun θ : ℝ => (2 * R : ℂ) * Complex.exp (θ * Complex.I)) := by
    exact continuous_const.mul (Complex.continuous_exp.comp hmul)
  have hcontF : Continuous F :=
    continuous_iff_continuousAt.mpr (fun z => (hF z).continuousAt)
  have hcont_norm : Continuous (fun θ : ℝ => ‖F ((2 * R : ℂ) * Complex.exp (θ * Complex.I))‖) :=
    continuous_norm.comp (hcontF.comp hparam)
  exact hcont_norm.continuousOn.log fun θ _ => norm_ne_zero_iff.mpr (hzero θ)

/-- If the doubled circle has no zeros, the Jensen boundary logarithmic average
is interval-integrable by continuity. -/
theorem entireFunction_jensenBoundaryLogAverage_intervalIntegrable_of_circleZeroFree
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
    (hzero : ∀ θ : ℝ, F ((2 * R : ℂ) * Complex.exp (θ * Complex.I)) ≠ 0) :
    IntervalIntegrable
      (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
      MeasureTheory.volume
      (0 : ℝ)
      (2 * Real.pi) := by
  exact
    (entireFunction_jensenBoundaryLogIntegrand_continuous_of_circleZeroFree F hF R hzero)
      .intervalIntegrable_of_Icc (show (0 : ℝ) ≤ 2 * Real.pi by exact le_of_lt Real.two_pi_pos)

/-- The boundary sample `θ ↦ F((2R) · exp(iθ))` is analytic as a real-variable
function. This is the owner-level transport input for the Jensen local model. -/
theorem jensenBoundaryLogSample_analyticAt
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
    (θ₀ : ℝ) :
    AnalyticAt ℝ
      (fun θ : ℝ => F ((2 * R : ℂ) * Complex.exp (θ * Complex.I))) θ₀ := by
  have hθI : AnalyticAt ℝ (fun θ : ℝ => θ * Complex.I) θ₀ := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (analyticAt_id.mul (analyticAt_const (v := (Complex.I : ℂ)) (x := θ₀)))
  have hexp : AnalyticAt ℝ (fun θ : ℝ => Complex.exp (θ * Complex.I)) θ₀ := by
    have houter : AnalyticAt ℝ (fun z : ℂ => Complex.exp z) ((θ₀ : ℝ) * Complex.I) :=
      (Complex.analyticAt_cexp (z := (θ₀ : ℝ) * Complex.I)).restrictScalars
    exact houter.comp hθI
  have hsample : AnalyticAt ℝ (fun θ : ℝ => (2 * R : ℂ) * Complex.exp (θ * Complex.I)) θ₀ := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (analyticAt_const.mul hexp)
  have hFreal : AnalyticAt ℝ F ((2 * R : ℂ) * Complex.exp (θ₀ * Complex.I)) :=
    (hF _).restrictScalars
  exact hFreal.comp hsample

/-- If the sampled boundary function is not locally zero at the parameter `θ₀`,
it admits the exact local Taylor factorization needed for the Jensen local model. -/
theorem jensenBoundaryLogSample_exists_eventuallyEq_pow_smul_nonzero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
    (θ₀ : ℝ)
    (hnot :
      ¬ ∀ᶠ θ in 𝓝 θ₀,
        F ((2 * R : ℂ) * Complex.exp (θ * Complex.I)) = 0) :
    ∃ n : ℕ, ∃ u : ℝ → ℂ,
      AnalyticAt ℝ u θ₀ ∧
      u θ₀ ≠ 0 ∧
      ∀ᶠ θ in 𝓝 θ₀,
        F ((2 * R : ℂ) * Complex.exp (θ * Complex.I)) =
          (θ - θ₀) ^ n • u θ := by
  have hsample :=
    jensenBoundaryLogSample_analyticAt F hF R θ₀
  rcases (hsample.exists_eventuallyEq_pow_smul_nonzero_iff).2 hnot with
    ⟨n, u, hu_an, hu_ne, hu_eq⟩
  exact ⟨n, u, hu_an, hu_ne, hu_eq⟩

/-- The local Taylor factorization of the boundary sample yields the expected
log-distance plus continuous remainder identity on the punctured neighborhood. -/
theorem jensenBoundaryLogSample_localLogContribution
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
    (θ₀ : ℝ)
    (hnot :
      ¬ ∀ᶠ θ in 𝓝 θ₀,
        F ((2 * R : ℂ) * Complex.exp (θ * Complex.I)) = 0) :
    ∃ n : ℕ, ∃ g : ℝ → ℝ,
      ContinuousAt g θ₀ ∧
      ∀ᶠ θ in 𝓝[≠] θ₀,
        Real.log ‖F ((2 * R : ℂ) * Complex.exp (θ * Complex.I))‖ =
          (n : ℝ) * Real.log |θ - θ₀| + g θ := by
  rcases
      jensenBoundaryLogSample_exists_eventuallyEq_pow_smul_nonzero F hF R θ₀ hnot with
    ⟨n, u, hu_an, hu_ne, hu_eq⟩
  refine ⟨n, fun θ : ℝ => Real.log ‖u θ‖, ?_, ?_⟩
  · exact (hu_an.continuousAt.norm).log (norm_ne_zero_iff.mpr hu_ne)
  filter_upwards
    [hu_eq.filter_mono nhdsWithin_le_nhds,
      (hu_an.continuousAt.eventually_ne hu_ne).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin]
    with θ hθ huθ_ne hne
  have hsub_ne : θ - θ₀ ≠ 0 := sub_ne_zero.mpr hne
  have hnorm_ne : ‖θ - θ₀‖ ≠ 0 := norm_ne_zero_iff.mpr hsub_ne
  have hpow_ne : ‖θ - θ₀‖ ^ n ≠ 0 := pow_ne_zero n hnorm_ne
  have huθ_ne' : ‖u θ‖ ≠ 0 := norm_ne_zero_iff.mpr huθ_ne
  calc
    Real.log ‖F ((2 * R : ℂ) * Complex.exp (θ * Complex.I))‖ =
        Real.log ‖(θ - θ₀) ^ n • u θ‖ := by
      exact congrArg Real.log (congrArg norm hθ)
    _ = Real.log (‖θ - θ₀‖ ^ n * ‖u θ‖) := by
      rw [norm_smul, norm_pow]
    _ = Real.log (‖θ - θ₀‖ ^ n) + Real.log ‖u θ‖ := by
      exact Real.log_mul hpow_ne huθ_ne'
    _ = (n : ℝ) * Real.log |θ - θ₀| + Real.log ‖u θ‖ := by
      simp [Real.log_pow, norm_eq_abs]

/-- An analytic real-parameter unit has locally interval-integrable log norm.

This is the exact analytic-unit remainder input needed by the Jensen local
model.  Analyticity gives continuity on a neighborhood of `θ₀`; nonvanishing
at `θ₀` shrinks that neighborhood to one where `u` is nonzero; therefore
`θ ↦ Real.log ‖u θ‖` is continuous on a small compact interval and hence
interval-integrable there. -/
theorem analyticAt_log_norm_unit_locally_intervalIntegrable
    (u : ℝ → ℂ)
    {θ₀ : ℝ}
    (hu_an : AnalyticAt ℝ u θ₀)
    (hu_ne : u θ₀ ≠ 0) :
    ∃ a b : ℝ,
      a < θ₀ ∧ θ₀ < b ∧
      IntervalIntegrable
        (fun θ : ℝ => Real.log ‖u θ‖)
        MeasureTheory.volume a b := by
  have hlocal_an : ∀ᶠ θ in 𝓝 θ₀, AnalyticAt ℝ u θ :=
    hu_an.eventually_analyticAt
  have hlocal_ne : ∀ᶠ θ in 𝓝 θ₀, u θ ≠ 0 :=
    hu_an.continuousAt.eventually_ne hu_ne
  have hlocal :
      {θ : ℝ | AnalyticAt ℝ u θ ∧ u θ ≠ 0} ∈ 𝓝 θ₀ := by
    exact hlocal_an.and hlocal_ne
  rcases mem_nhds_iff_exists_Ioo_subset.mp hlocal with
    ⟨a, b, hθ₀, hsubset⟩
  rcases exists_between hθ₀.1 with ⟨a', ha_a', ha'_θ₀⟩
  rcases exists_between hθ₀.2 with ⟨b', hθ₀_b', hb'_b⟩
  have ha'_b' : a' ≤ b' :=
    (ha'_θ₀.trans hθ₀_b').le
  have hIcc_subset : Set.Icc a' b' ⊆ Set.Ioo a b := by
    intro θ hθ
    exact
      ⟨lt_of_lt_of_le ha_a' hθ.1,
        lt_of_le_of_lt hθ.2 hb'_b⟩
  have hcont :
      ContinuousOn
        (fun θ : ℝ => Real.log ‖u θ‖)
        (Set.Icc a' b') := by
    intro θ hθ
    have hθ_data : AnalyticAt ℝ u θ ∧ u θ ≠ 0 :=
      hsubset (hIcc_subset hθ)
    exact
      ((hθ_data.1.continuousAt.norm).log
        (norm_ne_zero_iff.mpr hθ_data.2)).continuousWithinAt
  exact
    ⟨a', b', ha'_θ₀, hθ₀_b',
      hcont.intervalIntegrable_of_Icc ha'_b'⟩

/-- The analytic unit remainder in the local Jensen logarithmic model is
locally interval-integrable near the singular parameter. -/
theorem jensenBoundaryLogSample_localLogContribution_remainder_intervalIntegrable
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
    (θ₀ : ℝ)
    (hnot :
      ¬ ∀ᶠ θ in 𝓝 θ₀,
        F ((2 * R : ℂ) * Complex.exp (θ * Complex.I)) = 0) :
    ∃ n : ℕ, ∃ g : ℝ → ℝ,
      (∃ u v : ℝ,
        u < θ₀ ∧ θ₀ < v ∧
        IntervalIntegrable g MeasureTheory.volume u v) ∧
      ∀ᶠ θ in 𝓝[≠] θ₀,
        Real.log ‖F ((2 * R : ℂ) * Complex.exp (θ * Complex.I))‖ =
          (n : ℝ) * Real.log |θ - θ₀| + g θ := by
  rcases
      jensenBoundaryLogSample_exists_eventuallyEq_pow_smul_nonzero
        F hF R θ₀ hnot with
    ⟨n, u, hu_an, hu_ne, hu_eq⟩
  let g : ℝ → ℝ := fun θ : ℝ => Real.log ‖u θ‖
  have hg :
      ∃ a b : ℝ,
        a < θ₀ ∧ θ₀ < b ∧
        IntervalIntegrable g MeasureTheory.volume a b := by
    exact analyticAt_log_norm_unit_locally_intervalIntegrable u hu_an hu_ne
  have hmodel :
      ∀ᶠ θ in 𝓝[≠] θ₀,
        Real.log ‖F ((2 * R : ℂ) * Complex.exp (θ * Complex.I))‖ =
          (n : ℝ) * Real.log |θ - θ₀| + g θ := by
    filter_upwards
      [hu_eq.filter_mono nhdsWithin_le_nhds,
        (hu_an.continuousAt.eventually_ne hu_ne).filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin]
      with θ hθ huθ_ne hne
    have hsub_ne : θ - θ₀ ≠ 0 := sub_ne_zero.mpr hne
    have hnorm_ne : ‖θ - θ₀‖ ≠ 0 := norm_ne_zero_iff.mpr hsub_ne
    have hpow_ne : ‖θ - θ₀‖ ^ n ≠ 0 := pow_ne_zero n hnorm_ne
    have huθ_ne' : ‖u θ‖ ≠ 0 := norm_ne_zero_iff.mpr huθ_ne
    calc
      Real.log ‖F ((2 * R : ℂ) * Complex.exp (θ * Complex.I))‖ =
          Real.log ‖(θ - θ₀) ^ n • u θ‖ := by
        exact congrArg Real.log (congrArg norm hθ)
      _ = Real.log (‖θ - θ₀‖ ^ n * ‖u θ‖) := by
        rw [norm_smul, norm_pow]
      _ = Real.log (‖θ - θ₀‖ ^ n) + Real.log ‖u θ‖ := by
        exact Real.log_mul hpow_ne huθ_ne'
      _ = (n : ℝ) * Real.log |θ - θ₀| + g θ := by
        simp [g, Real.log_pow, norm_eq_abs]
  exact ⟨n, g, hg, hmodel⟩

/-- The sampled Jensen boundary function is not eventually zero near a singular
parameter once the entire function is nontrivial. -/
theorem jensenBoundaryLogSample_not_eventually_zero_of_nontrivial
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (R : ℝ)
    (hR : 0 < R)
    (θ₀ : ℝ)
    (hθ₀ : θ₀ ∈ Set.Ioc 0 (2 * Real.pi)) :
    ¬ ∀ᶠ θ in 𝓝 θ₀,
      F ((2 * R : ℂ) * Complex.exp (θ * Complex.I)) = 0 := by
  intro hzero
  have hsample :
      AnalyticAt ℝ
        (fun θ : ℝ => F ((2 * R : ℂ) * Complex.exp (θ * Complex.I))) θ₀ :=
    jensenBoundaryLogSample_analyticAt F hF R θ₀
  have hlocal_zero :
      ∀ᶠ θ in 𝓝 θ₀,
        (fun θ : ℝ => F ((2 * R : ℂ) * Complex.exp (θ * Complex.I))) θ = 0 :=
    hzero
  have hpropagate :
      ∀ z : ℂ, F z = 0 := by
    exact entireFunction_eq_zero_of_jensenBoundarySample_eventually_zero
      F hF R hR θ₀ hθ₀ hsample hlocal_zero
  rcases hnontrivial with ⟨z, hz⟩
  exact hz (hpropagate z)

/-- Local remainder extraction for a punctured-neighborhood Jensen boundary
model. -/
theorem jensenBoundaryLogIntegrand_continuousAt_localRemainder
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
    (θ₀ : ℝ)
    (n : ℕ)
    (g : ℝ → ℝ)
    (hg : ContinuousAt g θ₀)
    (hmodel :
      ∀ᶠ θ in 𝓝[≠] θ₀,
        entireFunctionJensenBoundaryLogIntegrand F (2 * R) θ =
          (n : ℝ) * Real.log |θ - θ₀| + g θ) :
    ∃ g' : ℝ → ℝ,
      ContinuousAt g' θ₀ ∧
      ∀ᶠ θ in 𝓝[≠] θ₀,
        entireFunctionJensenBoundaryLogIntegrand F (2 * R) θ =
          (n : ℝ) * Real.log |θ - θ₀| + g' θ := by
  exact
    continuousRemainderExtensionOn_Icc_of_puncturedLocalModel
      (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
      θ₀ n g hg hmodel

/-- The boundary logarithmic integrand has the expected local log-distance plus
continuous expansion near each singular parameter, on the punctured
neighborhood where the logarithmic singularity is modeled. -/
theorem jensenBoundaryLogIntegrand_eventually_eq_logDistance_plus_continuousAt_near_parameterZero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (R : ℝ)
    (hR : 0 < R)
    (θ₀ : ℝ)
    (hθ₀ :
      θ₀ ∈ Set.Ioc 0 (2 * Real.pi) ∧
        F ((2 * R : ℂ) * Complex.exp (θ₀ * Complex.I)) = 0) :
    ∃ n : ℕ, ∃ g : ℝ → ℝ,
      ContinuousAt g θ₀ ∧
      ∀ᶠ θ in 𝓝[≠] θ₀,
        entireFunctionJensenBoundaryLogIntegrand F (2 * R) θ =
          (n : ℝ) * Real.log |θ - θ₀| + g θ := by
  have hnot :
      ¬ ∀ᶠ θ in 𝓝 θ₀,
        F ((2 * R : ℂ) * Complex.exp (θ * Complex.I)) = 0 :=
    jensenBoundaryLogSample_not_eventually_zero_of_nontrivial
      F hF hnontrivial R hR θ₀ hθ₀.1
  rcases
      jensenBoundaryLogSample_localLogContribution F hF R θ₀ hnot with
    ⟨n, g, hg, hmodel⟩
  rcases
      jensenBoundaryLogIntegrand_continuousAt_localRemainder
        F hF R θ₀ n g hg hmodel with
    ⟨g', hg', hg'eventually⟩
  exact ⟨n, g', hg', hg'eventually⟩

/-- The Jensen boundary logarithmic integrand has a punctured local
log-distance model with a locally interval-integrable remainder near each
singular parameter. -/
theorem jensenBoundaryLogIntegrand_eventually_eq_logDistance_plus_intervalIntegrable_near_parameterZero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (R : ℝ)
    (hR : 0 < R)
    (θ₀ : ℝ)
    (hθ₀ :
      θ₀ ∈ Set.Icc 0 (2 * Real.pi) ∧
        F ((2 * R : ℂ) * Complex.exp (θ₀ * Complex.I)) = 0) :
    ∃ n : ℕ, ∃ g : ℝ → ℝ,
      (∃ u v : ℝ,
        u < θ₀ ∧ θ₀ < v ∧
        IntervalIntegrable g MeasureTheory.volume u v) ∧
      ∀ᶠ θ in 𝓝[≠] θ₀,
        entireFunctionJensenBoundaryLogIntegrand F (2 * R) θ =
          (n : ℝ) * Real.log |θ - θ₀| + g θ := by
  have hnot :
      ¬ ∀ᶠ θ in 𝓝 θ₀,
        F ((2 * R : ℂ) * Complex.exp (θ * Complex.I)) = 0 := by
    intro hzero
    have htwoR : 0 < 2 * R := by
      nlinarith
    have hglobal :
        ∀ z : ℂ, F z = 0 :=
      entireFunction_eq_zero_of_eventually_zero_on_positiveRadius_exp_arc
        F hF (2 * R) htwoR θ₀ hzero
    rcases hnontrivial with ⟨z, hz⟩
    exact hz (hglobal z)
  rcases
      jensenBoundaryLogSample_localLogContribution_remainder_intervalIntegrable
        F hF R θ₀ hnot with
    ⟨n, g, hg, hmodel⟩
  exact ⟨n, g, hg, hmodel⟩

/-- The doubled-circle parametrization is injective on the open fundamental arc
`(0, 2π]`. This is the bookkeeping input that turns a finite circle zero set into a
finite parameter singular set. -/
theorem entireFunction_jensenBoundaryCircleParam_injectiveOn_Ioc
    {R : ℝ}
    (hR : 0 < R) :
    Set.InjOn
      (fun θ : ℝ => (2 * R : ℂ) * Complex.exp (θ * Complex.I))
      (Set.Ioc 0 (2 * Real.pi)) := by
  intro θ1 hθ1 θ2 hθ2 hEq
  have hRne : (2 * R : ℂ) ≠ 0 := by
    have h2 : (2 : ℂ) ≠ 0 := by norm_num
    have hR' : (R : ℂ) ≠ 0 := by
      exact_mod_cast hR.ne'
    exact mul_ne_zero h2 hR'
  have hExp : Complex.exp (θ1 * Complex.I) = Complex.exp (θ2 * Complex.I) := by
    apply mul_left_cancel₀ hRne
    simpa [mul_assoc] using hEq
  rcases (Complex.exp_eq_exp_iff_exists_int.mp hExp) with ⟨n, hn⟩
  have hnC :
      (θ1 : ℂ) * Complex.I =
        ((θ2 + n * (2 * Real.pi)) : ℂ) * Complex.I := by
    simpa [mul_add, add_mul, mul_assoc, add_comm, add_left_comm, add_assoc] using hn
  have hθC : (θ1 : ℂ) = ((θ2 + n * (2 * Real.pi)) : ℂ) := by
    apply mul_right_cancel₀ Complex.I_ne_zero
    exact hnC
  have hθ : θ1 = θ2 + n * (2 * Real.pi) := by
    have hθ' := congrArg Complex.re hθC
    simpa using hθ'
  have hlt : (n : ℝ) < 1 := by
    nlinarith [hθ, hθ1.2, hθ2.1, Real.two_pi_pos]
  have hgt : -1 < (n : ℝ) := by
    nlinarith [hθ, hθ1.1, hθ2.2, Real.two_pi_pos]
  have hn0 : n = 0 := by
    by_contra hn0
    have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      exact_mod_cast Int.one_le_abs hn0
    have habs : |(n : ℝ)| < 1 := by
      exact abs_lt.mpr ⟨hgt, hlt⟩
    linarith
  subst hn0
  linarith

/-- The circle parametrization is injective on the open fundamental arc
`(0, 2π]` at an arbitrary positive radius.

This is the radius-normalized form consumed by the finite-exception
origin-factor transport; it is just the doubled Jensen parametrization applied
at half radius. -/
theorem entireFunction_boundaryCircleParam_injectiveOn_Ioc
    {R : ℝ}
    (hR : 0 < R) :
    Set.InjOn
      (fun θ : ℝ => (R : ℂ) * Complex.exp (θ * Complex.I))
      (Set.Ioc 0 (2 * Real.pi)) := by
  have hhalf : 0 < R / 2 :=
    half_pos hR
  have hJensen :
      Set.InjOn
        (fun θ : ℝ => (2 * (R / 2) : ℂ) * Complex.exp (θ * Complex.I))
        (Set.Ioc 0 (2 * Real.pi)) :=
    entireFunction_jensenBoundaryCircleParam_injectiveOn_Ioc hhalf
  intro θ₁ hθ₁ θ₂ hθ₂ hEq
  apply hJensen hθ₁ hθ₂
  have hscaleReal : 2 * (R / 2) = R := by
    calc
      2 * (R / 2) = R / 2 + R / 2 := two_mul (R / 2)
      _ = R := add_halves R
  have hscaleComplex : ((2 * (R / 2) : ℝ) : ℂ) = (R : ℂ) :=
    congrArg (fun x : ℝ => (x : ℂ)) hscaleReal
  calc
    (2 * (R / 2) : ℂ) * Complex.exp (θ₁ * Complex.I) =
        (R : ℂ) * Complex.exp (θ₁ * Complex.I) := by
      exact congrArg
        (fun x : ℂ => x * Complex.exp (θ₁ * Complex.I))
        hscaleComplex
    _ = (R : ℂ) * Complex.exp (θ₂ * Complex.I) :=
      hEq
    _ = (2 * (R / 2) : ℂ) * Complex.exp (θ₂ * Complex.I) := by
      exact congrArg
        (fun x : ℂ => x * Complex.exp (θ₂ * Complex.I))
        hscaleComplex.symm

/-- The finite circle-zero set induces a finite parameter singular set on the
fundamental boundary arc. -/
theorem entireFunction_jensenBoundaryCircleZeroParameters_finite
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (R : ℝ)
    (hR : 0 < R) :
    Set.Finite
      {θ : ℝ // θ ∈ Set.Ioc 0 (2 * Real.pi) ∧
        F ((2 * R : ℂ) * Complex.exp (θ * Complex.I)) = 0} := by
  let f : {θ : ℝ // θ ∈ Set.Ioc 0 (2 * Real.pi)} → ℂ :=
    fun θ => (2 * R : ℂ) * Complex.exp (θ * Complex.I)
  have hCircle : Set.Finite {z : ℂ | ‖z‖ = 2 * R ∧ F z = 0} :=
    entireFunction_jensenCircleZeros_finite F hF hnontrivial R
  have hInj : Function.Injective f := by
    intro a b hEq
    apply Subtype.ext
    exact entireFunction_jensenBoundaryCircleParam_injectiveOn_Ioc hR a.2 b.2 hEq
  have hpre : (f ⁻¹' {z : ℂ | ‖z‖ = 2 * R ∧ F z = 0}).Finite :=
    hCircle.preimage fun _ _ _ _ hEq => hInj hEq
  have h2R_nonneg : 0 ≤ 2 * R := by
    nlinarith [le_of_lt hR]
  simpa [f, Set.preimage, entireFunctionJensenBoundaryCircle_norm h2R_nonneg] using hpre

/-- Away from the singular parameters, the Jensen boundary logarithmic
integrand is continuous on the fundamental arc. -/
theorem entireFunction_jensenBoundaryLogIntegrand_continuousOn_compl_circleZeroParameters
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
    (hzero : ∀ θ : ℝ,
      θ ∈ Set.Ioc 0 (2 * Real.pi) →
        F ((2 * R : ℂ) * Complex.exp (θ * Complex.I)) ≠ 0) :
    ContinuousOn (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
      {θ : ℝ | θ ∈ Set.Ioc 0 (2 * Real.pi) ∧
        F ((2 * R : ℂ) * Complex.exp (θ * Complex.I)) ≠ 0} := by
  dsimp [entireFunctionJensenBoundaryLogIntegrand]
  have hmul : Continuous (fun θ : ℝ => θ * Complex.I) := by
    continuity
  have hparam : Continuous (fun θ : ℝ => (2 * R : ℂ) * Complex.exp (θ * Complex.I)) := by
    exact continuous_const.mul (Complex.continuous_exp.comp hmul)
  have hcontF : Continuous F :=
    continuous_iff_continuousAt.mpr (fun z => (hF z).continuousAt)
  have hcont_norm : Continuous (fun θ : ℝ => ‖F ((2 * R : ℂ) * Complex.exp (θ * Complex.I))‖) :=
    continuous_norm.comp (hcontF.comp hparam)
  exact hcont_norm.continuousOn.log fun θ hθ => norm_ne_zero_iff.mpr (hzero θ hθ.1)

/-- Jensen boundary specialization of finite logarithmic-singularity gluing.

The singular set is the finite set of parameters on the fundamental arc whose
circle samples are zeros.  Each such parameter is handled by the analytic
Taylor/log local model, and the zero-free complement is continuous. -/
theorem intervalIntegrable_jensenBoundaryLogIntegrand_of_finite_log_singularities_core
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (R : ℝ)
    (hR : 0 < R)
    (hzeros : Set.Finite {z : ℂ | ‖z‖ = 2 * R ∧ F z = 0}) :
    IntervalIntegrable
      (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
      MeasureTheory.volume
      (0 : ℝ)
      (2 * Real.pi) := by
  let S : Set ℝ :=
    {θ : ℝ | θ ∈ Set.Icc 0 (2 * Real.pi) ∧
      F ((2 * R : ℂ) * Complex.exp (θ * Complex.I)) = 0}
  have hS : S.Finite := by
    let T : Set ℝ :=
      {θ : ℝ | θ ∈ Set.Ioc 0 (2 * Real.pi) ∧
        F ((2 * R : ℂ) * Complex.exp (θ * Complex.I)) = 0}
    have hT : T.Finite := by
      simpa [T] using
        entireFunction_jensenBoundaryCircleZeroParameters_finite F hF hnontrivial R hR
    have hsubset : S ⊆ insert (0 : ℝ) T := by
      intro θ hθ
      by_cases hθ0 : θ = 0
      · exact hθ0 ▸ Set.mem_insert (0 : ℝ) T
      · exact Set.mem_insert_iff.mpr
          (Or.inr ⟨⟨lt_of_le_of_ne hθ.1.1 hθ0.symm, hθ.1.2⟩, hθ.2⟩)
    exact (hT.insert (0 : ℝ)).subset hsubset
  have hlocal :
      ∀ θ₀ ∈ S, ∃ n : ℕ, ∃ g : ℝ → ℝ,
        (∃ u v : ℝ,
          u < θ₀ ∧ θ₀ < v ∧
          IntervalIntegrable g MeasureTheory.volume u v) ∧
        ∀ᶠ θ in 𝓝[≠] θ₀,
          entireFunctionJensenBoundaryLogIntegrand F (2 * R) θ =
            (n : ℝ) * Real.log |θ - θ₀| + g θ := by
    intro θ₀ hθ₀
    exact
      jensenBoundaryLogIntegrand_eventually_eq_logDistance_plus_intervalIntegrable_near_parameterZero
        F hF hnontrivial R hR θ₀ hθ₀
  have hcont :
      ContinuousOn (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
        ({θ : ℝ | θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi) ∧ θ ∉ S}) := by
    dsimp [entireFunctionJensenBoundaryLogIntegrand]
    have hmul : Continuous (fun θ : ℝ => θ * Complex.I) := by
      continuity
    have hparam : Continuous
        (fun θ : ℝ => (2 * R : ℂ) * Complex.exp (θ * Complex.I)) := by
      exact continuous_const.mul (Complex.continuous_exp.comp hmul)
    have hcontF : Continuous F :=
      continuous_iff_continuousAt.mpr (fun z => (hF z).continuousAt)
    have hcont_norm :
        Continuous
          (fun θ : ℝ => ‖F ((2 * R : ℂ) * Complex.exp (θ * Complex.I))‖) :=
      continuous_norm.comp (hcontF.comp hparam)
    exact hcont_norm.continuousOn.log (by
      intro θ hθ
      exact norm_ne_zero_iff.mpr (by
        intro hzero
        exact hθ.2 ⟨hθ.1, hzero⟩))
  exact
    intervalIntegrable_of_finite_log_singularities_on_compact
      (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
      (0 : ℝ) (2 * Real.pi) S
      (mul_nonneg zero_le_two Real.pi_pos.le)
      hS hlocal hcont

/-- Finite gluing of local logarithmic singularity models on the Jensen
fundamental interval. -/
theorem intervalIntegrable_jensenBoundaryLogIntegrand_of_finite_log_singularities_glue
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (R : ℝ)
    (hR : 0 < R)
    (hzeros : Set.Finite {z : ℂ | ‖z‖ = 2 * R ∧ F z = 0}) :
    IntervalIntegrable
      (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
      MeasureTheory.volume
      (0 : ℝ)
      (2 * Real.pi) := by
  exact
    intervalIntegrable_jensenBoundaryLogIntegrand_of_finite_log_singularities_core
      F hF hnontrivial R hR hzeros

/-- Finite logarithmic singularity gluing for Jensen boundary integrability. -/
theorem intervalIntegrable_jensenBoundaryLogIntegrand_of_finite_log_singularities
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (R : ℝ)
    (hR : 0 < R)
    (hzeros : Set.Finite {z : ℂ | ‖z‖ = 2 * R ∧ F z = 0}) :
    IntervalIntegrable
      (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
      MeasureTheory.volume
      (0 : ℝ)
      (2 * Real.pi) := by
  exact
    intervalIntegrable_jensenBoundaryLogIntegrand_of_finite_log_singularities_glue
      F hF hnontrivial R hR hzeros

/-- The Jensen boundary logarithmic average is interval-integrable once the
circle zero set has been split into finitely many isolated logarithmic
singularities, each handled by the local factorization and logarithmic
contribution API. -/
theorem entireFunction_jensenBoundaryLogAverage_localSingularityModel
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (R : ℝ)
    (hR : 0 < R)
    (hzeros : Set.Finite {z : ℂ | ‖z‖ = 2 * R ∧ F z = 0}) :
    IntervalIntegrable
      (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
      MeasureTheory.volume
      (0 : ℝ)
      (2 * Real.pi) := by
  exact
    intervalIntegrable_jensenBoundaryLogIntegrand_of_finite_log_singularities_core
      F hF hnontrivial R hR hzeros

/-- The Jensen boundary logarithmic average is interval-integrable once the
circle zero set has been split into finitely many isolated logarithmic
singularities, each handled by the local factorization and logarithmic
contribution API. -/
theorem entireFunction_jensenBoundaryLogAverage_intervalIntegrable_of_finiteCircleZeros
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (R : ℝ)
    (hR : 0 < R)
    (hzeros : Set.Finite {z : ℂ | ‖z‖ = 2 * R ∧ F z = 0}) :
    IntervalIntegrable
      (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
      MeasureTheory.volume
      (0 : ℝ)
      (2 * Real.pi) := by
  exact entireFunction_jensenBoundaryLogAverage_localSingularityModel F hF hnontrivial R hR hzeros

theorem entireFunction_jensenBoundaryLogAverage_regularity
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∀ R : ℝ,
      1 ≤ R →
      BddAbove {x : ℝ | ∃ z : ℂ, ‖z‖ = 2 * R ∧ x = Real.log ‖F z‖} ∧
      IntervalIntegrable
        (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
        MeasureTheory.volume
        (0 : ℝ)
        (2 * Real.pi) := by
  intro R hR
    refine ⟨entireFunction_jensenBoundaryLogSet_bddAbove F hF (2 * R), ?_⟩
  exact
    entireFunction_jensenBoundaryLogAverage_intervalIntegrable_of_finiteCircleZeros
      F hF hnontrivial R
      (lt_of_lt_of_le zero_lt_one hR)
      (entireFunction_jensenCircleZeros_finite F hF hnontrivial R)

/-- Interval-integrability of the boundary logarithmic integrand at an arbitrary
positive radius, obtained from the doubled-radius Jensen API by using the
half-radius. -/
theorem entireFunction_boundaryLogIntegrand_intervalIntegrable_of_finiteCircleZeros
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    {r : ℝ}
    (hr : 0 < r)
    (hzeros : Set.Finite {z : ℂ | ‖z‖ = r ∧ F z = 0}) :
    IntervalIntegrable
      (entireFunctionJensenBoundaryLogIntegrand F r)
      MeasureTheory.volume
      (0 : ℝ)
      (2 * Real.pi) := by
  let R : ℝ := r / 2
  have hR : 0 < R :=
    half_pos hr
  have hscale : 2 * R = r := by
    calc
      2 * R = 2 * (r / 2) := rfl
      _ = r / 2 + r / 2 := two_mul (r / 2)
      _ = r := add_halves r
  have hzerosR :
      Set.Finite {z : ℂ | ‖z‖ = 2 * R ∧ F z = 0} := by
    exact Eq.subst
      (motive := fun s : ℝ =>
        Set.Finite {z : ℂ | ‖z‖ = s ∧ F z = 0})
      hscale.symm
      hzeros
  have hIntR :
      IntervalIntegrable
        (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
        MeasureTheory.volume
        (0 : ℝ)
        (2 * Real.pi) :=
    entireFunction_jensenBoundaryLogAverage_intervalIntegrable_of_finiteCircleZeros
      F hF hnontrivial R hR hzerosR
  exact Eq.subst
    (motive := fun s : ℝ =>
      IntervalIntegrable
        (entireFunctionJensenBoundaryLogIntegrand F s)
        MeasureTheory.volume
        (0 : ℝ)
        (2 * Real.pi))
    hscale
    hIntR

/-- Unnormalized boundary-integral transport through the origin Taylor factor,
after deleting the finite quotient boundary-zero exceptional set.

This is the analytic finite-exception congruence root.  The proof belongs to
the logarithmic-singularity layer: off the finite exceptional set the
integrands differ by the constant origin contribution, and the finite
logarithmic singularities do not change the interval integral. -/
theorem entireFunction_originTaylorFactor_boundaryLogIntegral_eq_origin_constant_plus_quotient_of_finiteExceptionCongr
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hG : ∀ z : ℂ, AnalyticAt ℂ G z)
    (hGnontrivial : ∃ z : ℂ, G z ≠ 0)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ) :
    entireFunctionJensenBoundaryLogIntegral F ρ =
      (2 * Real.pi) *
          entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
        entireFunctionJensenBoundaryLogIntegral G ρ := by
  have hρ_pos : 0 < ρ :=
    lt_of_lt_of_le zero_lt_one hρ
  have hInj :
      Set.InjOn
        (fun θ : ℝ => (ρ : ℂ) * Complex.exp (θ * Complex.I))
        (Set.Ioc 0 (2 * Real.pi)) :=
    entireFunction_boundaryCircleParam_injectiveOn_Ioc hρ_pos
  have hCircle :
      Set.Finite {z : ℂ | ‖z‖ = ρ ∧ G z = 0} :=
    entireFunction_circleZeros_finite G hG hGnontrivial ρ
  have hcert :
      (entireFunctionJensenQuotientBoundaryZeroParameters G ρ).Finite ∧
        ∀ θ : ℝ,
          θ ∈ Set.Icc 0 (2 * Real.pi) →
          θ ∉ entireFunctionJensenQuotientBoundaryZeroParameters G ρ →
          entireFunctionJensenBoundaryLogIntegrand F ρ θ =
            entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
              entireFunctionJensenBoundaryLogIntegrand G ρ θ :=
    entireFunction_originTaylorFactor_boundaryLogIntegrand_finiteExceptionCertificate
      F G hF hfactor hρ_pos hInj hCircle
  have hGint :
      IntervalIntegrable
        (entireFunctionJensenBoundaryLogIntegrand G ρ)
        MeasureTheory.volume
        (0 : ℝ)
        (2 * Real.pi) :=
    entireFunction_boundaryLogIntegrand_intervalIntegrable_of_finiteCircleZeros
      G hG hGnontrivial hρ_pos hCircle
  unfold entireFunctionJensenBoundaryLogIntegral
  have htransport :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
          entireFunctionJensenBoundaryLogIntegrand F ρ θ) =
        (2 * Real.pi - 0) •
            entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
          ∫ θ in (0 : ℝ)..(2 * Real.pi),
            entireFunctionJensenBoundaryLogIntegrand G ρ θ :=
    intervalIntegral_finiteException_const_add_eq_twoPi_smul_add
      (entireFunctionJensenBoundaryLogIntegrand F ρ)
      (entireFunctionJensenBoundaryLogIntegrand G ρ)
      (entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ)
      (entireFunctionJensenQuotientBoundaryZeroParameters G ρ)
      hcert.1
      hcert.2
      hGint
  have hlength :
      (2 * Real.pi - 0) •
          entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ =
        (2 * Real.pi) *
          entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ := by
    calc
      (2 * Real.pi - 0) •
          entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ =
          (2 * Real.pi) •
            entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ := by
        exact congrArg
          (fun x : ℝ =>
            x • entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ)
          (sub_zero (2 * Real.pi))
      _ =
          (2 * Real.pi) *
            entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ := rfl
  calc
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
        entireFunctionJensenBoundaryLogIntegrand F ρ θ) =
        (2 * Real.pi - 0) •
            entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
          ∫ θ in (0 : ℝ)..(2 * Real.pi),
            entireFunctionJensenBoundaryLogIntegrand G ρ θ :=
      htransport
    _ =
        (2 * Real.pi) *
            entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
          ∫ θ in (0 : ℝ)..(2 * Real.pi),
            entireFunctionJensenBoundaryLogIntegrand G ρ θ := by
      exact congrArg
        (fun x : ℝ =>
          x +
            ∫ θ in (0 : ℝ)..(2 * Real.pi),
              entireFunctionJensenBoundaryLogIntegrand G ρ θ)
        hlength

/-- Normalized boundary-integral transport through the origin Taylor factor,
after deleting the finite boundary-zero exceptional set.

This is the analytic congruence theorem underneath the boundary-average
transport: off the finite quotient-zero parameter set the logarithmic
integrands differ by the constant origin contribution, and the finite
logarithmic singularities do not change the interval integral. -/
theorem entireFunction_originTaylorFactor_normalizedBoundaryLogIntegral_eq_origin_plus_quotient_of_finiteExceptionCongr
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hG : ∀ z : ℂ, AnalyticAt ℂ G z)
    (hGnontrivial : ∃ z : ℂ, G z ≠ 0)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ) :
    (2 * Real.pi)⁻¹ * entireFunctionJensenBoundaryLogIntegral F ρ =
      entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
        (2 * Real.pi)⁻¹ * entireFunctionJensenBoundaryLogIntegral G ρ := by
  let c : ℝ := (2 * Real.pi)⁻¹
  let d : ℝ := 2 * Real.pi
  have hd_ne : d ≠ 0 :=
    ne_of_gt Real.two_pi_pos
  have hcd : c * d = 1 := by
    exact inv_mul_cancel₀ hd_ne
  have hintegral :
      entireFunctionJensenBoundaryLogIntegral F ρ =
        d * entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
          entireFunctionJensenBoundaryLogIntegral G ρ :=
    entireFunction_originTaylorFactor_boundaryLogIntegral_eq_origin_constant_plus_quotient_of_finiteExceptionCongr
      F G hF hG hGnontrivial hfactor hρ
  calc
    (2 * Real.pi)⁻¹ * entireFunctionJensenBoundaryLogIntegral F ρ =
        c * entireFunctionJensenBoundaryLogIntegral F ρ := rfl
    _ =
        c *
          (d * entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
            entireFunctionJensenBoundaryLogIntegral G ρ) := by
      exact congrArg (fun x : ℝ => c * x) hintegral
    _ =
        c * (d * entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ) +
          c * entireFunctionJensenBoundaryLogIntegral G ρ := by
      exact mul_add c
        (d * entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ)
        (entireFunctionJensenBoundaryLogIntegral G ρ)
    _ =
        (c * d) * entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
          c * entireFunctionJensenBoundaryLogIntegral G ρ := by
      exact congrArg
        (fun x : ℝ =>
          x + c * entireFunctionJensenBoundaryLogIntegral G ρ)
        (mul_assoc c d
          (entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ))
    _ =
        1 * entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
          c * entireFunctionJensenBoundaryLogIntegral G ρ := by
      exact congrArg
        (fun x : ℝ =>
          x * entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
            c * entireFunctionJensenBoundaryLogIntegral G ρ)
        hcd
    _ =
        entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
          c * entireFunctionJensenBoundaryLogIntegral G ρ := by
      exact congrArg
        (fun x : ℝ => x + c * entireFunctionJensenBoundaryLogIntegral G ρ)
        (one_mul (entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ))
    _ =
        entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
          (2 * Real.pi)⁻¹ * entireFunctionJensenBoundaryLogIntegral G ρ := rfl

/-- Boundary-average transport through the origin Taylor factor, stated as the
finite-exception integral theorem it really is.

The pointwise logarithmic identity holds away from the finite parameter set
where the quotient vanishes on the boundary circle.  At those exceptional
parameters `Real.log 0` makes the pointwise formula false, so the owner
statement is an interval-integral transport theorem modulo finite logarithmic
singularities, followed by the constant-integral normalization. -/
theorem entireFunction_originTaylorFactor_boundaryLogAverage_eq_origin_plus_quotient_of_finiteExceptionIntegral
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hG : ∀ z : ℂ, AnalyticAt ℂ G z)
    (hGnontrivial : ∃ z : ℂ, G z ≠ 0)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ) :
    entireFunctionJensenBoundaryLogAverage F ρ =
      entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
        entireFunctionJensenBoundaryLogAverage G ρ := by
  exact
    entireFunction_originTaylorFactor_normalizedBoundaryLogIntegral_eq_origin_plus_quotient_of_finiteExceptionCongr
      F G hF hG hGnontrivial hfactor hρ

/-- Boundary logarithmic averages transport through the global origin Taylor
quotient with the explicit `m log ρ` contribution from the removed origin
factor. -/
theorem entireFunction_originTaylorFactor_boundaryLogAverage_eq_origin_plus_quotient
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hG : ∀ z : ℂ, AnalyticAt ℂ G z)
    (hGnontrivial : ∃ z : ℂ, G z ≠ 0)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ) :
    entireFunctionJensenBoundaryLogAverage F ρ =
      entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
        entireFunctionJensenBoundaryLogAverage G ρ := by
  exact
    entireFunction_originTaylorFactor_boundaryLogAverage_eq_origin_plus_quotient_of_finiteExceptionIntegral
      F G hF hG hGnontrivial hfactor hρ

/-- Origin Taylor-factor transport after the global entire quotient at the
origin has been explicitly constructed.

The hypotheses are exactly the output of the removable-singularity origin
quotient construction.  This theorem owns the comparison between `F` and its
normalized entire quotient: nonzero zeros away from the origin, radial-gap
sums, and boundary logarithmic averages are transported through the global
factorization, while the separated power contributes `m log ρ`. -/
theorem entireFunction_classicalJensenFormula_originTaylorFactor_transport_from_entireQuotient
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (G : ℂ → ℂ)
    (hG_entire : ∀ z : ℂ, AnalyticAt ℂ G z)
    (hG_ne : G 0 ≠ 0)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z) :
    ∃ C : ℝ,
      (∀ R : ℝ,
        1 ≤ R →
        Summable
          (fun z : EntireFunctionZero F =>
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)) ∧
      (∀ ρ : ℝ,
          1 ≤ ρ →
          Summable
            (fun z : EntireFunctionZero F =>
              entireFunctionJensenRadialGapSummand F hF ρ z) ∧
          entireFunctionJensenRadialGapSum F hF ρ +
              entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
              C =
            entireFunctionJensenBoundaryLogAverage F ρ) := by
  rcases
      entireFunction_classicalJensenFormula_nonzeroAtOrigin_radialGapSum_eq_boundaryLogAverage
        G hG_entire hG_ne with
    ⟨C, hclosedG, hidentityG⟩
  refine ⟨C, ?_, ?_⟩
  · intro R hR
    exact
      entireFunction_originTaylorFactor_nonzeroClosedDiskSummable_of_quotient
        F G hF hG_entire hfactor hR (hclosedG R hR)
  · intro ρ hρ
    rcases hidentityG ρ hρ with ⟨hradialG, hGidentity⟩
    rcases
        entireFunction_originTaylorFactor_radialGapSum_eq_quotient_radialGapSum
          F G hF hG_entire hfactor hρ hradialG with
      ⟨hradialF, hradial_eq⟩
    refine ⟨hradialF, ?_⟩
    have hboundary :
        entireFunctionJensenBoundaryLogAverage F ρ =
          entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
            entireFunctionJensenBoundaryLogAverage G ρ :=
      entireFunction_originTaylorFactor_boundaryLogAverage_eq_origin_plus_quotient
        F G hF hG_entire ⟨0, hG_ne⟩ hfactor hρ
    calc
      entireFunctionJensenRadialGapSum F hF ρ +
          entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ + C =
          entireFunctionJensenRadialGapSum G hG_entire ρ +
            entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ + C := by
        exact congrArg
          (fun x : ℝ =>
            x + entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ + C)
          hradial_eq
      _ =
          entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
            (entireFunctionJensenRadialGapSum G hG_entire ρ + C) := by
        calc
          entireFunctionJensenRadialGapSum G hG_entire ρ +
              entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ + C =
              (entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
                entireFunctionJensenRadialGapSum G hG_entire ρ) + C := by
            exact congrArg
              (fun x : ℝ => x + C)
              (add_comm
                (entireFunctionJensenRadialGapSum G hG_entire ρ)
                (entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ))
          _ =
              entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
                (entireFunctionJensenRadialGapSum G hG_entire ρ + C) := by
            exact
              (add_assoc
                (entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ)
                (entireFunctionJensenRadialGapSum G hG_entire ρ)
                C).symm
      _ =
          entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
            entireFunctionJensenBoundaryLogAverage G ρ := by
        exact congrArg
          (fun x : ℝ =>
            entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ + x)
          hGidentity
      _ =
          entireFunctionJensenBoundaryLogAverage F ρ :=
        hboundary.symm

/-- Origin Taylor-factor transport in the genuine origin-zero case.

This is the remaining transport step after the nonzero-origin case is removed:
factor the origin zero by `AnalyticAt.order_eq_nat_iff`, apply the nonzero
Jensen formula to the analytic unit, and compare nonzero zero multisets and
boundary averages. -/
theorem entireFunction_classicalJensenFormula_originTaylorFactor_transport_of_zeroAtOrigin
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 = 0)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ C : ℝ,
      (∀ R : ℝ,
        1 ≤ R →
        Summable
          (fun z : EntireFunctionZero F =>
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)) ∧
      (∀ ρ : ℝ,
          1 ≤ ρ →
          Summable
            (fun z : EntireFunctionZero F =>
              entireFunctionJensenRadialGapSummand F hF ρ z) ∧
          entireFunctionJensenRadialGapSum F hF ρ +
              entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
              C =
            entireFunctionJensenBoundaryLogAverage F ρ) := by
  rcases entireFunction_originTaylorFactor_entireQuotient F hF hnontrivial with
    ⟨G, hG_entire, hG_ne, hfactor⟩
  exact
    entireFunction_classicalJensenFormula_originTaylorFactor_transport_from_entireQuotient
      F hF hnontrivial G hG_entire hG_ne hfactor

/-- Transport of the nonzero-at-origin Jensen identity through the origin
Taylor factor.

If `F(z) = z^m G(z)` near the origin and `G 0 ≠ 0`, the boundary average gains
the explicit term `m log ρ`, while the nonzero radial-gap and closed-disk
summability data are transported unchanged from the normalized factor.  This is
the exact owner theorem that separates the algebraic origin factor from the
classical Jensen identity for a function nonzero at the origin. -/
theorem entireFunction_classicalJensenFormula_originTaylorFactor_transport
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ C : ℝ,
      (∀ R : ℝ,
        1 ≤ R →
        Summable
          (fun z : EntireFunctionZero F =>
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)) ∧
      (∀ ρ : ℝ,
          1 ≤ ρ →
          Summable
            (fun z : EntireFunctionZero F =>
              entireFunctionJensenRadialGapSummand F hF ρ z) ∧
          entireFunctionJensenRadialGapSum F hF ρ +
              entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
              C =
            entireFunctionJensenBoundaryLogAverage F ρ) := by
  -- Factor `F` by its origin order and apply the nonzero-at-origin Jensen
  -- identity to the analytic unit.  The origin power contributes exactly
  -- `m * log ρ` to the boundary average.
  by_cases hF0 : F 0 = 0
  · exact
      entireFunction_classicalJensenFormula_originTaylorFactor_transport_of_zeroAtOrigin
        F hF hF0 hnontrivial
  · exact
      entireFunction_classicalJensenFormula_originTaylorFactor_transport_of_nonzeroAtOrigin
        F hF hF0

/-- Origin-factored classical Jensen formula as an exact radial-gap identity.

This is the genuinely analytic theorem: for a nontrivial entire function,
after separating the origin Taylor factor, Jensen's formula identifies the
boundary logarithmic average with the non-origin multiplicity-weighted radial
gap sum plus the origin radius term and one fixed normalization constant. -/
theorem entireFunction_classicalJensenFormula_originFactoredRadialGapSum_eq_boundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ C : ℝ,
      (∀ R : ℝ,
        1 ≤ R →
        Summable
          (fun z : EntireFunctionZero F =>
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)) ∧
      (∀ ρ : ℝ,
          1 ≤ ρ →
          Summable
            (fun z : EntireFunctionZero F =>
              entireFunctionJensenRadialGapSummand F hF ρ z) ∧
          entireFunctionJensenRadialGapSum F hF ρ +
              entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
              C =
            entireFunctionJensenBoundaryLogAverage F ρ) := by
  exact
    entireFunction_classicalJensenFormula_originTaylorFactor_transport
      F hF hnontrivial

/-- Origin-factored classical Jensen formula in radial-gap bound form.

For large radii, the origin radius term is nonnegative, so the exact Jensen
identity implies a radial-gap upper bound with one absolute-value constant. -/
theorem entireFunction_classicalJensenFormula_originFactoredRadialGapSum_le_boundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ J : ℝ,
      (∀ R : ℝ,
        1 ≤ R →
        Summable
          (fun z : EntireFunctionZero F =>
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)) ∧
      (∀ ρ : ℝ,
          1 ≤ ρ →
          Summable
            (fun z : EntireFunctionZero F =>
              entireFunctionJensenRadialGapSummand F hF ρ z) ∧
          entireFunctionJensenRadialGapSum F hF ρ ≤
            J + entireFunctionJensenBoundaryLogAverage F ρ) := by
  rcases
      entireFunction_classicalJensenFormula_originFactoredRadialGapSum_eq_boundaryLogAverage
        F hF hnontrivial with
    ⟨C, hclosed, hidentity⟩
  refine ⟨|C|, hclosed, ?_⟩
  intro ρ hρ
  rcases hidentity ρ hρ with ⟨hgap, hJensen⟩
  refine ⟨hgap, ?_⟩
  have horigin_nonneg :
      0 ≤ entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ := by
    unfold entireFunctionOriginMultiplicityLogRadiusContribution
    exact mul_nonneg
      (Nat.cast_nonneg (entireFunctionZeroMultiplicity F hF 0))
      (Real.log_nonneg hρ)
  have hC_nonneg : 0 ≤ |C| + C := by
    have hneg : -C ≤ |C| := neg_le_abs C
    have hsub : 0 ≤ |C| - (-C) := sub_nonneg.mpr hneg
    have hsub_eq : |C| - (-C) = |C| + C := by
      ring
    exact Eq.subst (motive := fun x : ℝ => 0 ≤ x) hsub_eq hsub
  have htail_nonneg :
      0 ≤
        entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
          (|C| + C) :=
    add_nonneg horigin_nonneg hC_nonneg
  have hle_add :
      entireFunctionJensenRadialGapSum F hF ρ ≤
        entireFunctionJensenRadialGapSum F hF ρ +
          (entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
            (|C| + C)) :=
    le_add_of_nonneg_right htail_nonneg
  have htarget :
      entireFunctionJensenRadialGapSum F hF ρ +
          (entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
            (|C| + C)) =
        |C| + entireFunctionJensenBoundaryLogAverage F ρ := by
    calc
      entireFunctionJensenRadialGapSum F hF ρ +
          (entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
            (|C| + C)) =
          |C| +
            (entireFunctionJensenRadialGapSum F hF ρ +
              entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
              C) := by
        ring
      _ = |C| + entireFunctionJensenBoundaryLogAverage F ρ := by
        exact congrArg (fun x : ℝ => |C| + x) hJensen
  exact Eq.subst
    (motive := fun x : ℝ =>
      entireFunctionJensenRadialGapSum F hF ρ ≤ x)
    htarget
    hle_add

/-- Classical Jensen formula in radial-gap form, with multiplicities and with
the first nonzero Taylor factor at the origin absorbed into an additive
constant.

This is the precise large-radius analytic input after removing the origin
factor: Jensen's formula identifies the multiplicity-weighted radial gap sum
with the boundary logarithmic average up to a fixed additive normalization
constant. The restriction `1 ≤ ρ` is the exact place where the origin-radius
term is nonnegative and can be absorbed. -/
theorem entireFunction_classicalJensenFormula_radialGapSum_le_boundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ J : ℝ,
      (∀ R : ℝ,
        1 ≤ R →
        Summable
          (fun z : EntireFunctionZero F =>
            entireFunctionZeroMultiplicityClosedDiskSummand F hF R z)) ∧
      (∀ ρ : ℝ,
          1 ≤ ρ →
          Summable
            (fun z : EntireFunctionZero F =>
              entireFunctionJensenRadialGapSummand F hF ρ z) ∧
          entireFunctionJensenRadialGapSum F hF ρ ≤
            J + entireFunctionJensenBoundaryLogAverage F ρ) ∧
      (∀ R : ℝ,
          1 ≤ R →
          entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2 ≤
            J + entireFunctionJensenRadialGapSum F hF (2 * R)) := by
  rcases
      entireFunction_classicalJensenFormula_originFactoredRadialGapSum_le_boundaryLogAverage
        F hF hnontrivial with
    ⟨J, hclosed_nonzero, hradial⟩
  refine
    ⟨entireFunctionOriginMultiplicityLogContribution F hF + |J|, ?_, ?_, ?_⟩
  · intro R hR
    exact
      entireFunctionZeroMultiplicityClosedDiskSummable_of_nonzeroClosedDiskSummable
        F hF (hclosed_nonzero R hR)
  · intro ρ hρ
    rcases hradial ρ hρ with ⟨hgap, hbound⟩
    refine ⟨hgap, ?_⟩
    have hJ_le :
        J + entireFunctionJensenBoundaryLogAverage F ρ ≤
          entireFunctionOriginMultiplicityLogContribution F hF + |J| +
            entireFunctionJensenBoundaryLogAverage F ρ := by
      have hJ_abs : J ≤ |J| := le_abs_self J
      have horigin_nonneg : 0 ≤ entireFunctionOriginMultiplicityLogContribution F hF := by
        unfold entireFunctionOriginMultiplicityLogContribution
        exact mul_nonneg
          (Nat.cast_nonneg (entireFunctionZeroMultiplicity F hF 0))
          real_log_two_pos.le
      have hJ_shift :
          J + entireFunctionJensenBoundaryLogAverage F ρ ≤
            |J| + entireFunctionJensenBoundaryLogAverage F ρ :=
        add_le_add_right hJ_abs
          (entireFunctionJensenBoundaryLogAverage F ρ)
      have horigin_shift :
          |J| + entireFunctionJensenBoundaryLogAverage F ρ ≤
            entireFunctionOriginMultiplicityLogContribution F hF +
              (|J| + entireFunctionJensenBoundaryLogAverage F ρ) :=
        le_add_of_nonneg_left horigin_nonneg
      have hassoc :
          entireFunctionOriginMultiplicityLogContribution F hF +
              (|J| + entireFunctionJensenBoundaryLogAverage F ρ) =
            entireFunctionOriginMultiplicityLogContribution F hF + |J| +
              entireFunctionJensenBoundaryLogAverage F ρ :=
        (add_assoc
          (entireFunctionOriginMultiplicityLogContribution F hF)
          |J|
          (entireFunctionJensenBoundaryLogAverage F ρ)).symm
      exact le_trans hJ_shift (Eq.subst
        (motive := fun x : ℝ =>
          |J| + entireFunctionJensenBoundaryLogAverage F ρ ≤ x)
        hassoc
        horigin_shift)
    exact le_trans hbound hJ_le
  · intro R hR
    have hρ : 1 ≤ 2 * R :=
      one_le_doubled_radius_of_one_le hR
    rcases hradial (2 * R) hρ with ⟨hgap, hbound⟩
    have hcount :
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2 ≤
          entireFunctionOriginMultiplicityLogContribution F hF +
            entireFunctionJensenRadialGapSum F hF (2 * R) :=
      entireFunctionZeroMultiplicityCountingInClosedDisk_mul_log_two_le_originContribution_plus_radialGapSum
        F hF hR (hclosed_nonzero R hR) hgap
    have habs_nonneg : 0 ≤ |J| := abs_nonneg J
    have hshift :
        entireFunctionOriginMultiplicityLogContribution F hF +
            entireFunctionJensenRadialGapSum F hF (2 * R) ≤
          entireFunctionOriginMultiplicityLogContribution F hF +
            (|J| + entireFunctionJensenRadialGapSum F hF (2 * R)) :=
      add_le_add_left
        (le_add_of_nonneg_left habs_nonneg)
        (entireFunctionOriginMultiplicityLogContribution F hF)
    have hassoc :
        entireFunctionOriginMultiplicityLogContribution F hF +
            (|J| + entireFunctionJensenRadialGapSum F hF (2 * R)) =
          entireFunctionOriginMultiplicityLogContribution F hF + |J| +
            entireFunctionJensenRadialGapSum F hF (2 * R) :=
      (add_assoc
        (entireFunctionOriginMultiplicityLogContribution F hF)
        |J|
        (entireFunctionJensenRadialGapSum F hF (2 * R))).symm
    exact le_trans hcount (Eq.subst
      (motive := fun x : ℝ =>
        entireFunctionOriginMultiplicityLogContribution F hF +
          entireFunctionJensenRadialGapSum F hF (2 * R) ≤ x)
      hassoc
      hshift)

/-- Jensen's radial-gap formula supplies summability of closed-disk
multiplicity summands. -/
theorem entireFunction_classicalJensenFormula_closedDiskMultiplicitySummable
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∀ R : ℝ,
      1 ≤ R →
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionZeroMultiplicityClosedDiskSummand F hF R z) := by
  intro R hR
  rcases entireFunction_classicalJensenFormula_radialGapSum_le_boundaryLogAverage
      F hF hnontrivial with ⟨J, hclosed, hradial, hcount⟩
  exact hclosed R hR

/-- The doubled-radius algebra converting the weighted Jensen radial-gap bound
into the closed-disk zero-counting estimate. -/
theorem entireFunction_zeroMultiplicityCounting_closedDisk_le_scaledBoundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hweighted :
      ∃ J : ℝ,
        ∀ R : ℝ,
          1 ≤ R →
          entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2 ≤
            J + entireFunctionJensenBoundaryLogAverage F (2 * R)) :
    ∃ J : ℝ,
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
          J + (Real.log 2)⁻¹ *
            entireFunctionJensenBoundaryLogAverage F (2 * R) := by
  rcases hweighted with ⟨J, hJ⟩
  refine ⟨(Real.log 2)⁻¹ * J, ?_⟩
  intro R hR
  have hlog_pos : 0 < Real.log 2 :=
    real_log_two_pos
  have hscaled :
      (Real.log 2)⁻¹ *
          (entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2) ≤
        (Real.log 2)⁻¹ *
          (J + entireFunctionJensenBoundaryLogAverage F (2 * R)) := by
    exact mul_le_mul_of_nonneg_left (hJ R hR) real_log_two_inv_nonneg
  have hleft :
      (Real.log 2)⁻¹ *
          (entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2) =
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R := by
    calc
      (Real.log 2)⁻¹ *
          (entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2) =
          ((Real.log 2)⁻¹ * Real.log 2) *
            entireFunctionZeroMultiplicityCountingInClosedDisk F hF R := by
        ring
      _ = 1 * entireFunctionZeroMultiplicityCountingInClosedDisk F hF R := by
        exact congrArg
          (fun x : ℝ => x *
            entireFunctionZeroMultiplicityCountingInClosedDisk F hF R)
          (inv_mul_cancel₀ hlog_pos.ne')
      _ = entireFunctionZeroMultiplicityCountingInClosedDisk F hF R := by
        exact one_mul _
  have hright :
      (Real.log 2)⁻¹ *
          (J + entireFunctionJensenBoundaryLogAverage F (2 * R)) =
        (Real.log 2)⁻¹ * J +
          (Real.log 2)⁻¹ * entireFunctionJensenBoundaryLogAverage F (2 * R) := by
    ring
  exact hleft ▸ hright ▸ hscaled

/-- Classical Jensen formula in the weighted doubled-radius counting form.

This is the genuine classical Jensen formula input after factoring the first
nonzero Taylor term at the origin: the Jensen radial-gap sum on the circle of
radius `2R` dominates the multiplicity count in `closedDisk R` by the uniform
gap `log 2`, with a constant absorbing the origin factor; cf. Titchmarsh, *The
Theory of Functions*, §5. -/
theorem entireFunction_classicalJensenFormula_weighted_doubledRadius_zeroMultiplicityCounting_closedDisk_le_boundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ J : ℝ,
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2 ≤
          J + entireFunctionJensenBoundaryLogAverage F (2 * R) := by
  rcases
    entireFunction_classicalJensenFormula_radialGapSum_le_boundaryLogAverage
      F hF hnontrivial with
    ⟨J, hclosed, hradial, hcount⟩
  refine ⟨J + J, ?_⟩
  intro R hR
  have hρ : 1 ≤ 2 * R :=
    one_le_doubled_radius_of_one_le hR
  rcases hradial (2 * R) hρ with ⟨hgap_summable, hgap_bound⟩
  have hcount_gap :
      entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2 ≤
        J + entireFunctionJensenRadialGapSum F hF (2 * R) :=
    hcount R hR
  have hbound :
      J + entireFunctionJensenRadialGapSum F hF (2 * R) ≤
        J + (J + entireFunctionJensenBoundaryLogAverage F (2 * R)) :=
    add_le_add_left hgap_bound J
  have htarget :
      J + (J + entireFunctionJensenBoundaryLogAverage F (2 * R)) =
        J + J + entireFunctionJensenBoundaryLogAverage F (2 * R) := by
    ring
  exact Eq.subst
    (motive := fun x : ℝ =>
      entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2 ≤ x)
    htarget
    (le_trans hcount_gap hbound)

/-- Classical weighted Jensen zero-counting estimate on the doubled disk. -/
theorem entireFunction_classicalJensenFormula_weighted_zeroMultiplicityCounting_closedDisk_le_boundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ J : ℝ,
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2 ≤
          J + entireFunctionJensenBoundaryLogAverage F (2 * R) := by
  exact
    entireFunction_classicalJensenFormula_weighted_doubledRadius_zeroMultiplicityCounting_closedDisk_le_boundaryLogAverage
      F hF hnontrivial

/-- Standard Jensen formula with multiplicity counting on the doubled disk.

After factoring the first nonzero Taylor term at the origin, Jensen's formula
gives the weighted sum of logarithmic radial gaps for zeros in the doubled
disk.  Since every zero in `closedDisk R` contributes at least `log 2` to that
sum when the boundary radius is `2R`, the stated inequality follows with a
constant absorbing the origin factor. -/
theorem entireFunction_classicalJensenFormula_standardRoot_zeroMultiplicityCounting_closedDisk_le_scaledBoundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ J : ℝ,
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
          J + (Real.log 2)⁻¹ *
            entireFunctionJensenBoundaryLogAverage F (2 * R) := by
  have hweighted :
      ∃ J : ℝ,
        ∀ R : ℝ,
          1 ≤ R →
          entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2 ≤
            J + entireFunctionJensenBoundaryLogAverage F (2 * R) := by
    exact
      entireFunction_classicalJensenFormula_weighted_zeroMultiplicityCounting_closedDisk_le_boundaryLogAverage
        F hF hnontrivial
  exact
    entireFunction_zeroMultiplicityCounting_closedDisk_le_scaledBoundaryLogAverage
      F hF hweighted

/-- Classical Jensen formula zero-counting estimate, including the doubled-radius
`log 2` loss.

This is the deepest remaining analytic input: Jensen's formula for a nonzero
entire function, with multiplicities, after comparing zeros in `closedDisk R`
to the boundary integral on the circle of radius `2R`; cf. Titchmarsh, *The
Theory of Functions*, §5. -/
theorem entireFunction_classicalJensenFormula_zeroMultiplicityCounting_closedDisk_le_scaledBoundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ J : ℝ,
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
          J + (Real.log 2)⁻¹ *
            entireFunctionJensenBoundaryLogAverage F (2 * R) := by
  exact
    entireFunction_classicalJensenFormula_standardRoot_zeroMultiplicityCounting_closedDisk_le_scaledBoundaryLogAverage
      F hF hnontrivial

/-- Standard Jensen zero-counting estimate for nontrivial entire functions,
including the algebraic doubled-radius `log 2` loss. -/
theorem entireFunction_standardJensen_zeroMultiplicityCounting_closedDisk_le_scaledBoundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ J : ℝ,
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
          J + (Real.log 2)⁻¹ *
            entireFunctionJensenBoundaryLogAverage F (2 * R) := by
  exact
    entireFunction_classicalJensenFormula_zeroMultiplicityCounting_closedDisk_le_scaledBoundaryLogAverage
      F hF hnontrivial

/-- Classical Jensen zero-counting estimate for nontrivial entire functions,
with the doubled-radius `log 2` loss. -/
theorem entireFunction_jensen_formula_zeroMultiplicityCounting_closedDisk_le_scaledBoundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ J : ℝ,
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
          J + (Real.log 2)⁻¹ *
            entireFunctionJensenBoundaryLogAverage F (2 * R) := by
  exact
    entireFunction_standardJensen_zeroMultiplicityCounting_closedDisk_le_scaledBoundaryLogAverage
      F hF hnontrivial


/-- Jensen's formula relates multiplicity-aware closed-disk zero counting to the
normalized logarithmic boundary average on the doubled circle, with the standard
`log 2` loss.

This is the classical analytic root: after factoring the first nonzero Taylor
term at the origin, Jensen's formula bounds zeros in `closedDisk R` by the
boundary average of `log ‖F‖` on the circle of radius `2R`, divided by
`log 2`; cf. Titchmarsh, *The Theory of Functions*, §5. -/
theorem entireFunction_jensenFormula_zeroMultiplicityCounting_closedDisk_le_scaledBoundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ J : ℝ,
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
          J + (Real.log 2)⁻¹ *
            entireFunctionJensenBoundaryLogAverage F (2 * R) := by
  exact entireFunction_jensen_formula_zeroMultiplicityCounting_closedDisk_le_scaledBoundaryLogAverage
    F hF hnontrivial

/-- Multiplicity-aware closed-disk zero counting is bounded by the doubled-circle
boundary logarithmic average with the standard `log 2` factor. -/
theorem entireFunctionZeroMultiplicityCounting_closedDisk_le_boundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ J : ℝ,
      ∀ R : ℝ,
        1 ≤ R →
        BddAbove {x : ℝ | ∃ z : ℂ, ‖z‖ = 2 * R ∧ x = Real.log ‖F z‖} ∧
        IntervalIntegrable
          (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
          MeasureTheory.volume
          (0 : ℝ)
          (2 * Real.pi) ∧
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
          J + (Real.log 2)⁻¹ *
            entireFunctionJensenBoundaryLogAverage F (2 * R) := by
  match
    entireFunction_jensenFormula_zeroMultiplicityCounting_closedDisk_le_scaledBoundaryLogAverage
      F hF hnontrivial with
  | ⟨J, hcount⟩ =>
      refine ⟨J, ?_⟩
      intro R hR
      match entireFunction_jensenBoundaryLogAverage_regularity F hF hnontrivial R hR with
      | ⟨hbdd, hint⟩ =>
          exact ⟨hbdd, hint, hcount R hR⟩

/-- Jensen's formula converts the boundary-log-average estimate into the log-max
closed-disk zero-counting bound. -/
theorem entireFunction_jensenFormula_zeroMultiplicityCounting_closedDisk_le_logMax
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ J : ℝ,
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
          J + (Real.log 2)⁻¹ * entireFunctionLogMaxOnCircle F (2 * R) := by
  match
    entireFunctionZeroMultiplicityCounting_closedDisk_le_boundaryLogAverage
      F hF hnontrivial with
  | ⟨J, hJ⟩ =>
      refine ⟨J, ?_⟩
      intro R hR
      have hR_nonneg : 0 ≤ R :=
        le_trans zero_le_one hR
      have htwoR_nonneg : 0 ≤ 2 * R :=
        mul_nonneg zero_le_two hR_nonneg
      match hJ R hR with
      | ⟨hbdd, hint, hcount⟩ =>
          have havg :
              entireFunctionJensenBoundaryLogAverage F (2 * R) ≤
                entireFunctionLogMaxOnCircle F (2 * R) :=
            entireFunctionJensenBoundaryLogAverage_le_logMaxOnCircle
              F
              htwoR_nonneg
              hbdd
              hint
          have hlog_two_nonneg : 0 ≤ (Real.log 2)⁻¹ :=
            inv_nonneg.mpr (le_of_lt (Real.log_pos one_lt_two))
          have hwith_constant :
              J + (Real.log 2)⁻¹ *
                  entireFunctionJensenBoundaryLogAverage F (2 * R) ≤
                J + (Real.log 2)⁻¹ *
                  entireFunctionLogMaxOnCircle F (2 * R) :=
            add_le_add_left
              (mul_le_mul_of_nonneg_left havg hlog_two_nonneg)
              J
          exact le_trans hcount hwith_constant

end


end
end LFunctions
end Boundary

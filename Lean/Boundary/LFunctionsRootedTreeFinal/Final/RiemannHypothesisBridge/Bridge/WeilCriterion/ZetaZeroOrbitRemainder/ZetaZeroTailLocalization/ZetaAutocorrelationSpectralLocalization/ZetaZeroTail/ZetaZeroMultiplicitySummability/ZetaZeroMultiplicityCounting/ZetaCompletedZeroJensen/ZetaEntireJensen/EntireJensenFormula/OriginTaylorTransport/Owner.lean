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
  exact
    Exists.elim
      (entireFunction_classicalJensenFormula_nonzeroAtOrigin_radialGapSum_eq_boundaryLogAverage
        F hF hF0)
      (fun C hC =>
        Exists.intro C
          (And.intro hC.1
            (fun ρ hρ =>
              match hC.2 ρ hρ with
              | ⟨hsum, hradial⟩ =>
                  let horigin :
                      entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ = 0 :=
                    entireFunctionOriginMultiplicityLogRadiusContribution_eq_zero_of_ne_zero
                      F hF hF0 ρ
                  let hzero_insert :
                      entireFunctionJensenRadialGapSum F hF ρ +
                          entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ + C =
                        entireFunctionJensenRadialGapSum F hF ρ + 0 + C :=
                    congrArg
                      (fun x : ℝ =>
                        entireFunctionJensenRadialGapSum F hF ρ + x + C)
                      horigin
                  let hzero_drop :
                      entireFunctionJensenRadialGapSum F hF ρ + 0 + C =
                        entireFunctionJensenRadialGapSum F hF ρ + C :=
                    congrArg
                      (fun x : ℝ => x + C)
                      (add_zero (entireFunctionJensenRadialGapSum F hF ρ))
                  And.intro hsum
                    (Eq.trans hzero_insert (Eq.trans hzero_drop hradial)))))

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
  let hmodel :
      ∃ g : ℂ → ℂ,
        AnalyticAt ℂ g 0 ∧
          g 0 ≠ 0 ∧
            ∀ᶠ z in 𝓝 0, F z = (z - 0) ^ m • g z :=
    (hF 0).order_eq_nat_iff m |>.mp horder
  let g : ℂ → ℂ := Classical.choose hmodel
  have hg_spec :
      AnalyticAt ℂ g 0 ∧
        g 0 ≠ 0 ∧
          ∀ᶠ z in 𝓝 0, F z = (z - 0) ^ m • g z :=
    Classical.choose_spec hmodel
  have hg_an : AnalyticAt ℂ g 0 :=
    hg_spec.1
  have hg_ne : g 0 ≠ 0 :=
    hg_spec.2.1
  have hg_factor :
      ∀ᶠ z in 𝓝 0, F z = (z - 0) ^ m • g z :=
    hg_spec.2.2
  have hg_factor_power :
      ∀ᶠ z in 𝓝 0, F z = z ^ m • g z :=
    hg_factor.mono
      (fun z hz =>
        Eq.trans hz
          (congrArg
            (fun w : ℂ => w ^ m • g z)
            (sub_zero z)))
  let G : ℂ → ℂ :=
    fun z =>
      if z = 0 then
        g 0
      else
        entireFunction_originTaylorPuncturedQuotient F hF z
  have hG_eq_g_nhds : G =ᶠ[𝓝 (0 : ℂ)] g := by
    exact
      hg_factor_power.mono
        (fun z hz_factor =>
          match eq_or_ne z 0 with
          | Or.inl hz =>
              calc
                G z = g 0 := by
                  exact if_pos hz
                _ = g z := by
                  exact congrArg g hz.symm
          | Or.inr hz =>
              have hpow : z ^ m ≠ 0 :=
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
                  exact one_smul ℂ (g z))
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
    have hne_event : ∀ᶠ w in 𝓝 z, w ≠ 0 :=
      isOpen_ne.mem_nhds hz
    exact
      hquot_an.congr
        (hne_event.mono
          (fun w hw =>
              calc
                (w ^ m)⁻¹ * F w =
                    (w ^ m)⁻¹ • F w := by
                  rfl
              _ = entireFunction_originTaylorPuncturedQuotient F hF w := rfl
              _ = G w := by
                exact (if_neg hw).symm))
  have hG_an : ∀ z : ℂ, AnalyticAt ℂ G z := by
    intro z
    exact
      match eq_or_ne z 0 with
      | Or.inl hz =>
          Eq.subst (motive := fun w : ℂ => AnalyticAt ℂ G w) hz.symm hG_origin_an
      | Or.inr hz =>
          hG_off_origin_an z hz
  have hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z := by
    intro z
    exact
      match eq_or_ne z 0 with
        | Or.inl hz =>
            have hlocal_at_origin : F 0 = (0 : ℂ) ^ m • g 0 :=
              hg_factor_power.self_of_nhds
            have hGz : G z = g 0 :=
              if_pos hz
            have hzpow : z ^ m = (0 : ℂ) ^ m :=
              congrArg (fun w : ℂ => w ^ m) hz
            calc
              F z = F 0 := by
                exact congrArg F hz
              _ = (0 : ℂ) ^ m • g 0 :=
                hlocal_at_origin
              _ = z ^ m • G z := by
                calc
                  (0 : ℂ) ^ m • g 0 = z ^ m • g 0 := by
                    exact congrArg (fun a : ℂ => a • g 0) hzpow.symm
                  _ = z ^ m • G z := by
                    exact congrArg (fun x : ℂ => z ^ m • x) hGz.symm
        | Or.inr hz =>
            calc
              F z =
                  z ^ entireFunctionZeroMultiplicity F hF 0 •
                    entireFunction_originTaylorPuncturedQuotient F hF z :=
                entireFunction_originTaylorPuncturedQuotient_factorization_of_ne_zero
                  F hF hz
              _ = z ^ entireFunctionZeroMultiplicity F hF 0 • G z := by
                exact congrArg
                  (fun x : ℂ =>
                    z ^ entireFunctionZeroMultiplicity F hF 0 • x)
                  (if_neg hz).symm
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
          rfl
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
      rfl
    _ = (a * b) * c := (mul_assoc a b c).symm
    _ = (b * a) * c := by
      exact congrArg (fun x : ℂ => x * c) (mul_comm a b)
    _ = b * (a * c) := mul_assoc b a c
    _ = b • (a * c) := by
      rfl

theorem analyticAt_order_eq_of_eventually_eq_unit_smul
    (F G u : ℂ → ℂ)
    {z : ℂ}
    (hF : AnalyticAt ℂ F z)
    (hG : AnalyticAt ℂ G z)
    (hu : AnalyticAt ℂ u z)
    (hu_ne : u z ≠ 0)
    (hfactor : ∀ᶠ w in 𝓝 z, F w = u w • G w) :
    hF.order = hG.order := by
  exact
    match eq_or_ne hG.order ⊤ with
    | Or.inl hG_top =>
        let hG_zero : ∀ᶠ w in 𝓝 z, G w = 0 :=
          (hG.order_eq_top_iff).mp hG_top
        let hF_zero : ∀ᶠ w in 𝓝 z, F w = 0 :=
          (hfactor.and hG_zero).mono
            (fun w hw =>
              calc
                F w = u w • G w := hw.1
                _ = u w • 0 := congrArg (fun x : ℂ => u w • x) hw.2
                _ = 0 := smul_zero (u w))
        Eq.trans ((hF.order_eq_top_iff).mpr hF_zero) hG_top.symm
    | Or.inr hG_top_ne =>
        let n : ℕ := hG.order.untop hG_top_ne
        let hG_order : hG.order = (n : ENat) :=
          (WithTop.coe_untop hG.order hG_top_ne).symm
        let hF_order : hF.order = (n : ENat) :=
          Exists.elim
            ((hG.order_eq_nat_iff n).mp hG_order)
            (fun g hg =>
              let hmodel :
                  ∀ᶠ w in 𝓝 z,
                    F w = (w - z) ^ n • (u w * g w) :=
                (hfactor.and hg.2.2).mono
                  (fun w hw =>
                    calc
                      F w = u w • G w := hw.1
                      _ = u w • ((w - z) ^ n • g w) := by
                        exact congrArg (fun x : ℂ => u w • x) hw.2
                      _ = (w - z) ^ n • (u w * g w) :=
                        complex_smul_smul_eq_smul_mul
                          (u w) ((w - z) ^ n) (g w))
              (hF.order_eq_nat_iff n).mpr
                ⟨fun w : ℂ => u w * g w,
                  hu.mul hg.1,
                  mul_ne_zero hu_ne hg.2.1,
                  hmodel⟩)
        Eq.trans hF_order hG_order.symm

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
  calc
    entireFunctionZeroMultiplicity F hF z = (hF z).order.toNat := rfl
    _ = (hG z).order.toNat := by
      exact congrArg (fun e : ENat => e.toNat)
        (analyticAt_order_eq_of_eventually_eq_unit_smul
          F G u (hF z) (hG z) hu hu_ne hfactor)
    _ = entireFunctionZeroMultiplicity G hG z := rfl

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
      (Filter.Eventually.of_forall hfactor)

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
  have hmult :
      entireFunctionZeroMultiplicity G hG (z : ℂ) =
        entireFunctionZeroMultiplicity F hF (z : ℂ) :=
    (entireFunction_originTaylorFactor_multiplicity_eq_quotient_of_ne_zero
      F G hF hG hfactor z.property.2).symm
  calc
    entireFunctionNonzeroZeroClosedDiskSummand G hG R
        (entireFunction_originTaylorFactor_nonzeroZeroEquiv F G hF hfactor z) =
        if ‖(z : ℂ)‖ ≤ R then
          (entireFunctionZeroMultiplicity G hG (z : ℂ) : ℝ)
        else
          0 := rfl
    _ =
        if ‖(z : ℂ)‖ ≤ R then
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ)
        else
          0 := by
        exact
          if_congr
            Iff.rfl
            (congrArg (fun n : ℕ => (n : ℝ)) hmult)
            rfl
    _ = entireFunctionNonzeroZeroClosedDiskSummand F hF R z := rfl

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
  have hmult :
      entireFunctionZeroMultiplicity G hG (z : ℂ) =
        entireFunctionZeroMultiplicity F hF (z : ℂ) :=
    (entireFunction_originTaylorFactor_multiplicity_eq_quotient_of_ne_zero
      F G hF hG hfactor z.property.2).symm
  calc
    entireFunctionNonzeroZeroRadialGapSummand G hG ρ
        (entireFunction_originTaylorFactor_nonzeroZeroEquiv F G hF hfactor z) =
        if ‖(z : ℂ)‖ < ρ then
          (entireFunctionZeroMultiplicity G hG (z : ℂ) : ℝ) *
            Real.log (ρ / ‖(z : ℂ)‖)
        else
          0 := rfl
    _ =
        if ‖(z : ℂ)‖ < ρ then
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            Real.log (ρ / ‖(z : ℂ)‖)
        else
          0 := by
        exact
          if_congr
            Iff.rfl
            (congrArg
              (fun n : ℕ =>
                (n : ℝ) * Real.log (ρ / ‖(z : ℂ)‖))
              hmult)
            rfl
    _ = entireFunctionNonzeroZeroRadialGapSummand F hF ρ z := rfl

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
    hGsum.comp_injective e.injective
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
    hGsum.comp_injective e.injective
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
      exact
        match eq_or_ne (z : ℂ) 0 with
        | Or.inl hz => hz
        | Or.inr hz_ne =>
            False.elim
              (hz_not_range
                ((EntireFunctionNonzeroZero.mem_range_toZero_iff F z).mpr
                  hz_ne))
    calc
      entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z =
          if (z : ℂ) = 0 then
            0
          else
            entireFunctionZeroMultiplicityClosedDiskSummand F hF R z := rfl
      _ = 0 := if_pos hz_zero
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
    exact
      funext
        (fun z =>
          have hz_ne : ((i z : EntireFunctionZero F) : ℂ) ≠ 0 := z.property.2
          calc
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R (i z) =
                if ((i z : EntireFunctionZero F) : ℂ) = 0 then
                  0
                else
                  entireFunctionZeroMultiplicityClosedDiskSummand F hF R (i z) := rfl
            _ = entireFunctionZeroMultiplicityClosedDiskSummand F hF R (i z) :=
              if_neg hz_ne
            _ =
                if ‖((i z : EntireFunctionZero F) : ℂ)‖ ≤ R then
                  (entireFunctionZeroMultiplicity F hF
                    ((i z : EntireFunctionZero F) : ℂ) : ℝ)
                else
                  0 := rfl
            _ = entireFunctionNonzeroZeroClosedDiskSummand F hF R z := rfl)
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
      exact
        match eq_or_ne (z : ℂ) 0 with
        | Or.inl hz => hz
        | Or.inr hz_ne =>
            False.elim
              (hz_not_range
                ((EntireFunctionNonzeroZero.mem_range_toZero_iff F z).mpr
                  hz_ne))
    calc
      entireFunctionJensenRadialGapSummand F hF ρ z =
          if (z : ℂ) = 0 then
            0
          else if ‖(z : ℂ)‖ < ρ then
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              Real.log (ρ / ‖(z : ℂ)‖)
          else
            0 := rfl
      _ = 0 := if_pos hz_zero
  have hsupport :
      Function.support
          (entireFunctionJensenRadialGapSummand F hF ρ) ⊆
        Set.range i :=
    fun z hz_support =>
      match eq_or_ne (z : ℂ) 0 with
      | Or.inr hz_ne =>
          (EntireFunctionNonzeroZero.mem_range_toZero_iff F z).mpr hz_ne
      | Or.inl hz_zero =>
          False.elim
            (hz_support
              (houtside z
                (fun hz_range =>
                  ((EntireFunctionNonzeroZero.mem_range_toZero_iff F z).mp
                    hz_range)
                    hz_zero)))
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
    exact
      funext
        (fun z =>
          have hz_ne : ((i z : EntireFunctionZero F) : ℂ) ≠ 0 := z.property.2
          calc
            entireFunctionJensenRadialGapSummand F hF ρ (i z) =
                if ((i z : EntireFunctionZero F) : ℂ) = 0 then
                  0
                else if ‖((i z : EntireFunctionZero F) : ℂ)‖ < ρ then
                  (entireFunctionZeroMultiplicity F hF
                    ((i z : EntireFunctionZero F) : ℂ) : ℝ) *
                    Real.log (ρ / ‖((i z : EntireFunctionZero F) : ℂ)‖)
                else
                  0 := rfl
            _ =
                if ‖((i z : EntireFunctionZero F) : ℂ)‖ < ρ then
                  (entireFunctionZeroMultiplicity F hF
                    ((i z : EntireFunctionZero F) : ℂ) : ℝ) *
                    Real.log (ρ / ‖((i z : EntireFunctionZero F) : ℂ)‖)
                else
                  0 := if_neg hz_ne
            _ = entireFunctionNonzeroZeroRadialGapSummand F hF ρ z := rfl)
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
      exact
        match eq_or_ne (z : ℂ) 0 with
        | Or.inl hz => hz
        | Or.inr hz_ne =>
            False.elim
              (hz_not_range
                ((EntireFunctionNonzeroZero.mem_range_toZero_iff F z).mpr
                  hz_ne))
    calc
      entireFunctionJensenRadialGapSummand F hF ρ z =
          if (z : ℂ) = 0 then
            0
          else if ‖(z : ℂ)‖ < ρ then
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              Real.log (ρ / ‖(z : ℂ)‖)
          else
            0 := rfl
      _ = 0 := if_pos hz_zero
  have hpoint :
      (fun z : EntireFunctionNonzeroZero F =>
          entireFunctionJensenRadialGapSummand F hF ρ (i z)) =
        (fun z : EntireFunctionNonzeroZero F =>
          entireFunctionNonzeroZeroRadialGapSummand F hF ρ z) := by
    exact
      funext
        (fun z =>
          have hz_ne : ((i z : EntireFunctionZero F) : ℂ) ≠ 0 := z.property.2
          calc
            entireFunctionJensenRadialGapSummand F hF ρ (i z) =
                if ((i z : EntireFunctionZero F) : ℂ) = 0 then
                  0
                else if ‖((i z : EntireFunctionZero F) : ℂ)‖ < ρ then
                  (entireFunctionZeroMultiplicity F hF
                    ((i z : EntireFunctionZero F) : ℂ) : ℝ) *
                    Real.log (ρ / ‖((i z : EntireFunctionZero F) : ℂ)‖)
                  else
                    0 := rfl
            _ =
                  if ‖((i z : EntireFunctionZero F) : ℂ)‖ < ρ then
                    (entireFunctionZeroMultiplicity F hF
                      ((i z : EntireFunctionZero F) : ℂ) : ℝ) *
                      Real.log (ρ / ‖((i z : EntireFunctionZero F) : ℂ)‖)
                  else
                    0 := by
                exact if_neg hz_ne
              _ = entireFunctionNonzeroZeroRadialGapSummand F hF ρ z := rfl)
  have hsupport :
        Function.support
            (entireFunctionJensenRadialGapSummand F hF ρ) ⊆
          Set.range i :=
      fun z hz_support =>
        match eq_or_ne (z : ℂ) 0 with
        | Or.inr hz_ne =>
            (EntireFunctionNonzeroZero.mem_range_toZero_iff F z).mpr hz_ne
        | Or.inl hz_zero =>
            False.elim
              (hz_support
                (houtside z
                  (fun hz_range =>
                    ((EntireFunctionNonzeroZero.mem_range_toZero_iff F z).mp
                      hz_range)
                      hz_zero)))
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
      hi.tsum_eq hsupport

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
  have hsum_eq :
      entireFunctionJensenRadialGapSum F hF ρ =
        entireFunctionJensenRadialGapSum G hG ρ := by
    calc
      entireFunctionJensenRadialGapSum F hF ρ =
          ∑' z : EntireFunctionZero F,
            entireFunctionJensenRadialGapSummand F hF ρ z := rfl
      _ =
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
      _ = entireFunctionJensenRadialGapSum G hG ρ := rfl
  exact And.intro hFsum hsum_eq

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
  have hAeNotMem :
      ∀ᵐ θ ∂MeasureTheory.volume, θ ∉ S :=
    hS.countable.ae_not_mem MeasureTheory.volume
  exact
    intervalIntegral.integral_congr_ae
      (hAeNotMem.mono
        (fun θ hθ_not_mem hθ_interval =>
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
          hcongr θ hθ_Icc hθ_not_mem))

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
  calc
    entireFunctionJensenBoundaryLogIntegrand F R θ =
        Real.log ‖F ((R : ℂ) * Complex.exp (θ * Complex.I))‖ := rfl
    _ =
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
    _ =
        (entireFunctionZeroMultiplicity F hF 0 : ℝ) * Real.log R +
          entireFunctionJensenBoundaryLogIntegrand G R θ := rfl

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
  exact
    And.intro
      hfinite
      (fun θ hθI hθnot =>
        entireFunction_originTaylorFactor_boundaryLogIntegrand_eq_off_quotientZeroParameters
          F G hF hfactor hR_pos hθnot hθI)

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
  calc
    entireFunctionJensenBoundaryLogIntegrand F R θ =
        Real.log ‖F ((R : ℂ) * Complex.exp (θ * Complex.I))‖ := rfl
    _ ≤ sSup {x : ℝ | ∃ z : ℂ, ‖z‖ = R ∧ x = Real.log ‖F z‖} :=
      le_csSup hbdd
        ⟨(R : ℂ) * Complex.exp (θ * Complex.I),
          entireFunctionJensenBoundaryCircle_norm hR,
          rfl⟩
    _ = entireFunctionLogMaxOnCircle F R := rfl

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
    calc
      (∫ _θ in (0 : ℝ)..(2 * Real.pi),
          entireFunctionLogMaxOnCircle F R) =
          (2 * Real.pi - 0) • entireFunctionLogMaxOnCircle F R := by
        exact intervalIntegral.integral_const
          (entireFunctionLogMaxOnCircle F R)
      _ = (2 * Real.pi) • entireFunctionLogMaxOnCircle F R := by
        exact congrArg
          (fun x : ℝ => x • entireFunctionLogMaxOnCircle F R)
          (sub_zero (2 * Real.pi))
      _ = (2 * Real.pi) * entireFunctionLogMaxOnCircle F R := rfl
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
        exact
          (mul_assoc
            (2 * Real.pi)⁻¹
            (2 * Real.pi)
            (entireFunctionLogMaxOnCircle F R)).symm
      _ = 1 * entireFunctionLogMaxOnCircle F R := by
        exact congrArg
          (fun x : ℝ => x * entireFunctionLogMaxOnCircle F R)
          (inv_mul_cancel₀ Real.two_pi_pos.ne')
      _ = entireFunctionLogMaxOnCircle F R := one_mul _
  calc
    entireFunctionJensenBoundaryLogAverage F R =
        (2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            entireFunctionJensenBoundaryLogIntegrand F R θ) := rfl
    _ ≤
        (2 * Real.pi)⁻¹ *
          ((2 * Real.pi) * entireFunctionLogMaxOnCircle F R) :=
      hscaled
    _ = entireFunctionLogMaxOnCircle F R :=
      hcollapse

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
    exact isCompact_closedBall (0 : ℂ) (2 * R)
  exact
    Exists.elim
      (hcompact.bddAbove_image (hcont_norm.continuousOn))
      (fun M hM =>
        Exists.intro M
          (fun x hx =>
            Exists.elim hx
              (fun z hz_data =>
                  match hz_data with
                  | ⟨hz, hx_eq⟩ =>
                      have hzball : z ∈ Metric.closedBall (0 : ℂ) (2 * R) :=
                        have hdist_norm : dist z 0 = ‖z‖ := by
                          calc
                            dist z 0 = ‖z - 0‖ :=
                              dist_eq_norm z 0
                            _ = ‖z‖ := by
                              exact congrArg norm (sub_zero z)
                        Metric.mem_closedBall.2
                          (Eq.subst
                            (motive := fun x : ℝ => x ≤ 2 * R)
                            hdist_norm.symm
                            (le_of_eq hz))
                    have hnorm_le : ‖F z‖ ≤ M :=
                      hM ⟨z, hzball, rfl⟩
                    have hlog_le : Real.log ‖F z‖ ≤ M :=
                      le_trans (Real.log_le_self (norm_nonneg (F z))) hnorm_le
                    Eq.subst
                      (motive := fun y : ℝ => y ≤ M)
                      hx_eq.symm
                      hlog_le)))

/-- The Jensen boundary logarithmic integrand is continuous when the doubled circle
contains no zeros. -/
theorem entireFunction_jensenBoundaryLogIntegrand_continuous_of_circleZeroFree
    (F : ℂ → ℂ)
      (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
      (R : ℝ)
      (hzero : ∀ θ : ℝ,
        F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ≠ 0) :
      Continuous (entireFunctionJensenBoundaryLogIntegrand F (2 * R)) := by
    have hmul : Continuous (fun θ : ℝ => (θ : ℂ) * Complex.I) := by
      exact Complex.continuous_ofReal.mul continuous_const
    have hparam :
        Continuous
          (fun θ : ℝ =>
            (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) := by
      exact continuous_const.mul (Complex.continuous_exp.comp hmul)
    have hcontF : Continuous F :=
      continuous_iff_continuousAt.mpr (fun z => (hF z).continuousAt)
    have hcont_norm :
        Continuous
          (fun θ : ℝ =>
            ‖F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖) :=
      continuous_norm.comp (hcontF.comp hparam)
    exact hcont_norm.log (fun θ => norm_ne_zero_iff.mpr (hzero θ))

/-- If the doubled circle has no zeros, the Jensen boundary logarithmic average
is interval-integrable by continuity. -/
theorem entireFunction_jensenBoundaryLogAverage_intervalIntegrable_of_circleZeroFree
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
      (hzero : ∀ θ : ℝ,
        F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ≠ 0) :
    IntervalIntegrable
      (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
      MeasureTheory.volume
      (0 : ℝ)
      (2 * Real.pi) := by
    exact
      Continuous.intervalIntegrable
        (entireFunction_jensenBoundaryLogIntegrand_continuous_of_circleZeroFree F hF R hzero)
        (0 : ℝ)
        (2 * Real.pi)

/-- The local Taylor factorization of the boundary sample yields the expected
log-distance plus continuous remainder identity on the punctured neighborhood. -/
theorem jensenBoundaryLogSample_localLogContribution
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
      (R : ℝ)
      (θ₀ : ℝ)
      (hnot :
        ¬ ∀ᶠ (θ : ℝ) in 𝓝 θ₀,
          F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = 0) :
    ∃ n : ℕ, ∃ g : ℝ → ℝ,
        ContinuousAt g θ₀ ∧
        ∀ᶠ (θ : ℝ) in 𝓝[≠] θ₀,
          Real.log ‖F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ =
            (n : ℝ) * Real.log |θ - θ₀| + g θ := by
  exact
    Exists.elim
      (jensenBoundaryLogSample_exists_eventuallyEq_pow_smul_nonzero F hF R θ₀ hnot)
      (fun n hn =>
        Exists.elim hn
          (fun u hu =>
            match hu with
            | ⟨hu_an, hu_tail⟩ =>
                match hu_tail with
                | ⟨hu_ne, hu_eq⟩ =>
                    have hcont :
                        ContinuousAt (fun θ : ℝ => Real.log ‖u θ‖) θ₀ :=
                      (hu_an.continuousAt.norm).log (norm_ne_zero_iff.mpr hu_ne)
                    have hmodel :
                        ∀ᶠ (θ : ℝ) in 𝓝[≠] θ₀,
                          Real.log ‖F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ =
                            (n : ℝ) * Real.log |θ - θ₀| +
                              Real.log ‖u θ‖ :=
                      (((hu_eq.filter_mono nhdsWithin_le_nhds).and
                          ((hu_an.continuousAt.eventually_ne hu_ne).filter_mono
                            nhdsWithin_le_nhds)).and
                        self_mem_nhdsWithin).mono
                        (fun θ hθ_all =>
                          have hθ : F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
                              (θ - θ₀) ^ n • u θ :=
                            hθ_all.1.1
                          have huθ_ne : u θ ≠ 0 :=
                            hθ_all.1.2
                          have hne : θ ≠ θ₀ :=
                            hθ_all.2
                          have hsub_ne : θ - θ₀ ≠ 0 :=
                            sub_ne_zero.mpr hne
                          have hnorm_ne : ‖θ - θ₀‖ ≠ 0 :=
                            norm_ne_zero_iff.mpr hsub_ne
                          have hpow_ne : ‖θ - θ₀‖ ^ n ≠ 0 :=
                            pow_ne_zero n hnorm_ne
                          have huθ_ne' : ‖u θ‖ ≠ 0 :=
                            norm_ne_zero_iff.mpr huθ_ne
                          have hpoint :
                              Real.log ‖F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ =
                                (n : ℝ) * Real.log |θ - θ₀| + Real.log ‖u θ‖ := by
                            calc
                              Real.log ‖F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ =
                                  Real.log ‖(θ - θ₀) ^ n • u θ‖ := by
                                exact congrArg Real.log (congrArg norm hθ)
                              _ = Real.log (‖θ - θ₀‖ ^ n * ‖u θ‖) := by
                                have hnorm_product :
                                    ‖(θ - θ₀) ^ n • u θ‖ =
                                      ‖θ - θ₀‖ ^ n * ‖u θ‖ := by
                                  calc
                                    ‖(θ - θ₀) ^ n • u θ‖ =
                                        ‖(θ - θ₀) ^ n‖ * ‖u θ‖ := by
                                      exact norm_smul _ _
                                    _ = ‖θ - θ₀‖ ^ n * ‖u θ‖ := by
                                      exact congrArg
                                        (fun t : ℝ => t * ‖u θ‖)
                                        (norm_pow _ _)
                                exact congrArg Real.log hnorm_product
                              _ = Real.log (‖θ - θ₀‖ ^ n) + Real.log ‖u θ‖ := by
                                exact Real.log_mul hpow_ne huθ_ne'
                              _ = (n : ℝ) * Real.log |θ - θ₀| + Real.log ‖u θ‖ := by
                                have hnormabs : ‖θ - θ₀‖ = |θ - θ₀| := by
                                  exact Real.norm_eq_abs _
                                have hpowlog :
                                    Real.log (‖θ - θ₀‖ ^ n) =
                                      (n : ℝ) * Real.log |θ - θ₀| := by
                                  calc
                                    Real.log (‖θ - θ₀‖ ^ n) =
                                        (n : ℝ) * Real.log ‖θ - θ₀‖ := by
                                      exact Real.log_pow _ _
                                    _ = (n : ℝ) * Real.log |θ - θ₀| := by
                                      exact congrArg
                                        (fun t : ℝ => (n : ℝ) * Real.log t)
                                        hnormabs
                                exact congrArg
                                  (fun x : ℝ => x + Real.log ‖u θ‖)
                                  hpowlog
                          hpoint)
                    Exists.intro n
                      (Exists.intro
                        (fun θ : ℝ => Real.log ‖u θ‖)
                        (And.intro hcont hmodel))))

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
    ¬ ∀ᶠ (θ : ℝ) in 𝓝 θ₀,
      F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = 0 := by
  intro hzero
  have hsample :
      AnalyticAt ℝ
        (fun θ : ℝ =>
          F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) θ₀ :=
    jensenBoundaryLogSample_analyticAt F hF R θ₀
  have hlocal_zero :
      ∀ᶠ (θ : ℝ) in 𝓝 θ₀,
        (fun θ : ℝ =>
          F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) θ = 0 :=
    hzero
  have hradius_eq : (((2 * R : ℝ) : ℂ)) = (2 * R : ℂ) :=
    Complex.ofReal_mul 2 R
  have hsample_product :
      AnalyticAt ℝ
        (fun θ : ℝ =>
          F ((2 * R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) θ₀ :=
    Eq.subst
      (motive := fun c : ℂ =>
        AnalyticAt ℝ
          (fun θ : ℝ => F (c * Complex.exp ((θ : ℂ) * Complex.I))) θ₀)
      hradius_eq
      hsample
  have hlocal_zero_product :
      ∀ᶠ (θ : ℝ) in 𝓝 θ₀,
        (fun θ : ℝ =>
          F ((2 * R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) θ = 0 :=
    Eq.subst
      (motive := fun c : ℂ =>
        ∀ᶠ (θ : ℝ) in 𝓝 θ₀,
          (fun θ : ℝ => F (c * Complex.exp ((θ : ℂ) * Complex.I))) θ = 0)
      hradius_eq
      hlocal_zero
  have hpropagate :
      ∀ z : ℂ, F z = 0 := by
    exact entireFunction_eq_zero_of_jensenBoundarySample_eventually_zero
      F hF R hR θ₀ hθ₀ hsample_product hlocal_zero_product
  exact
    Exists.elim hnontrivial
      (fun z hz => hz (hpropagate z))

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
theorem jensenBoundaryLogIntegrand_punctured_logDistance_plus_continuousAt_near_parameterZero
    (F : ℂ → ℂ)
      (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
      (hnontrivial : ∃ z : ℂ, F z ≠ 0)
      (R : ℝ)
      (hR : 0 < R)
      (θ₀ : ℝ)
      (hθ₀ :
        θ₀ ∈ Set.Ioc 0 (2 * Real.pi) ∧
          F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I)) = 0) :
    ∃ n : ℕ, ∃ g : ℝ → ℝ,
      ContinuousAt g θ₀ ∧
      ∀ᶠ θ in 𝓝[≠] θ₀,
        entireFunctionJensenBoundaryLogIntegrand F (2 * R) θ =
          (n : ℝ) * Real.log |θ - θ₀| + g θ := by
  have hnot :
        ¬ ∀ᶠ (θ : ℝ) in 𝓝 θ₀,
          F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = 0 :=
      jensenBoundaryLogSample_not_eventually_zero_of_nontrivial
        F hF hnontrivial R hR θ₀ hθ₀.1
  exact
    match jensenBoundaryLogSample_localLogContribution F hF R θ₀ hnot with
    | ⟨n, g, hg, hmodel⟩ =>
        match jensenBoundaryLogIntegrand_continuousAt_localRemainder
            F hF R θ₀ n g hg hmodel with
        | ⟨g', hg', hg'eventually⟩ =>
            Exists.intro n
              (Exists.intro g'
                (And.intro hg' hg'eventually))

/-- Away from the singular parameters, the Jensen boundary logarithmic
integrand is continuous on the fundamental arc. -/
theorem entireFunction_jensenBoundaryLogIntegrand_continuousOn_compl_circleZeroParameters
      (F : ℂ → ℂ)
      (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
      (R : ℝ)
      (hzero : ∀ θ : ℝ,
        θ ∈ Set.Ioc 0 (2 * Real.pi) →
          F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ≠ 0) :
      ContinuousOn (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
        {θ : ℝ | θ ∈ Set.Ioc 0 (2 * Real.pi) ∧
          F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ≠ 0} := by
    have hmul : Continuous (fun θ : ℝ => (θ : ℂ) * Complex.I) := by
      exact Complex.continuous_ofReal.mul continuous_const
    have hparam :
        Continuous
          (fun θ : ℝ =>
            (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) := by
      exact continuous_const.mul (Complex.continuous_exp.comp hmul)
    have hcontF : Continuous F :=
      continuous_iff_continuousAt.mpr (fun z => (hF z).continuousAt)
    have hcont_norm :
        Continuous
          (fun θ : ℝ =>
            ‖F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖) :=
      continuous_norm.comp (hcontF.comp hparam)
    exact hcont_norm.continuousOn.log
      (fun θ hθ => norm_ne_zero_iff.mpr (hzero θ hθ.1))

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
  exact
      And.intro
        (entireFunction_jensenBoundaryLogSet_bddAbove F hF R)
      (entireFunction_jensenBoundaryLogAverage_intervalIntegrable_of_finiteCircleZeros
        F hF hnontrivial R
        (lt_of_lt_of_le zero_lt_one hR)
        (entireFunction_jensenCircleZeros_finite F hF hnontrivial R))

/-- Unnormalized boundary-integral transport through the origin Taylor factor,
after deleting the finite quotient boundary-zero exceptional set.

This is the analytic finite-exception congruence root.  The proof belongs to
the logarithmic-singularity layer: off the finite exceptional set the
integrands differ by the constant origin contribution, and the finite
logarithmic singularities do not alter the interval integral. -/
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
    entireFunctionJensenBoundaryLogIntegral F ρ =
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          entireFunctionJensenBoundaryLogIntegrand F ρ θ := rfl
    _ =
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
    _ =
        (2 * Real.pi) *
            entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
          entireFunctionJensenBoundaryLogIntegral G ρ := rfl

/-- Normalized boundary-integral transport through the origin Taylor factor,
after deleting the finite boundary-zero exceptional set.

This is the analytic congruence theorem underneath the boundary-average
transport: off the finite quotient-zero parameter set the logarithmic
integrands differ by the constant origin contribution, and the finite
logarithmic singularities do not alter the interval integral. -/
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
            (entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ)).symm
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
  exact
    Exists.elim
      (entireFunction_classicalJensenFormula_nonzeroAtOrigin_radialGapSum_eq_boundaryLogAverage
        G hG_entire hG_ne)
      (fun C hC =>
        match hC with
        | ⟨hclosedG, hidentityG⟩ =>
            Exists.intro C
              (And.intro
                (fun R hR =>
                  entireFunction_originTaylorFactor_nonzeroClosedDiskSummable_of_quotient
                    F G hF hG_entire hfactor hR (hclosedG R hR))
                (fun ρ hρ =>
                  match hidentityG ρ hρ with
                  | ⟨hradialG, hGidentity⟩ =>
                      match
                        entireFunction_originTaylorFactor_radialGapSum_eq_quotient_radialGapSum
                          F G hF hG_entire hfactor hρ hradialG with
                      | ⟨hradialF, hradial_eq⟩ =>
                          have hboundary :
                              entireFunctionJensenBoundaryLogAverage F ρ =
                                entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
                                  entireFunctionJensenBoundaryLogAverage G ρ :=
                            entireFunction_originTaylorFactor_boundaryLogAverage_eq_origin_plus_quotient
                              F G hF hG_entire ⟨0, hG_ne⟩ hfactor hρ
                          have hidentityF :
                              entireFunctionJensenRadialGapSum F hF ρ +
                                  entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ + C =
                                entireFunctionJensenBoundaryLogAverage F ρ := by
                            calc
                              entireFunctionJensenRadialGapSum F hF ρ +
                                  entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ + C =
                                  entireFunctionJensenRadialGapSum G hG_entire ρ +
                                    entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ + C := by
                                exact congrArg
                                  (fun x : ℝ =>
                                    x +
                                      entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ + C)
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
                                        C)
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
                          And.intro hradialF hidentityF)))

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
  exact
    Exists.elim
      (entireFunction_originTaylorFactor_entireQuotient F hF hnontrivial)
      (fun G hG_data =>
        match hG_data with
        | ⟨hG_entire, hG_tail⟩ =>
            match hG_tail with
            | ⟨hG_ne, hfactor⟩ =>
                entireFunction_classicalJensenFormula_originTaylorFactor_transport_from_entireQuotient
                  F hF hnontrivial G hG_entire hG_ne hfactor)

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
  exact
    match eq_or_ne (F 0) 0 with
    | Or.inl hF0 =>
        entireFunction_classicalJensenFormula_originTaylorFactor_transport_of_zeroAtOrigin
          F hF hF0 hnontrivial
    | Or.inr hF0 =>
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
  exact
    Exists.elim
      (entireFunction_classicalJensenFormula_originFactoredRadialGapSum_eq_boundaryLogAverage
        F hF hnontrivial)
      (fun C hC =>
        match hC with
        | ⟨hclosed, hidentity⟩ =>
            Exists.intro |C|
              (And.intro hclosed
                (fun ρ hρ =>
                  match hidentity ρ hρ with
                  | ⟨hgap, hJensen⟩ =>
                      have horigin_nonneg :
                          0 ≤ entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ := by
                        calc
                          0 ≤
                              (entireFunctionZeroMultiplicity F hF 0 : ℝ) * Real.log ρ :=
                            mul_nonneg
                              (Nat.cast_nonneg (entireFunctionZeroMultiplicity F hF 0))
                              (Real.log_nonneg hρ)
                          _ = entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ := rfl
                      have hC_nonneg : 0 ≤ |C| + C := by
                        have hneg : -C ≤ |C| := neg_le_abs C
                        have hsub : 0 ≤ |C| - (-C) := sub_nonneg.mpr hneg
                        have hsub_eq : |C| - (-C) = |C| + C := by
                          calc
                            |C| - (-C) = |C| + -(-C) :=
                              sub_eq_add_neg |C| (-C)
                            _ = |C| + C := by
                              exact congrArg (fun x : ℝ => |C| + x) (neg_neg C)
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
                            let A : ℝ := entireFunctionJensenRadialGapSum F hF ρ
                            let B : ℝ := entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ
                            let D : ℝ := |C|
                            calc
                              A + (B + (D + C)) = A + ((B + D) + C) := by
                                exact congrArg (fun x : ℝ => A + x) (add_assoc B D C).symm
                              _ = (A + (B + D)) + C := by
                                exact (add_assoc A (B + D) C).symm
                              _ = ((B + D) + A) + C := by
                                exact congrArg (fun x : ℝ => x + C) (add_comm A (B + D))
                              _ = ((D + B) + A) + C := by
                                exact congrArg
                                  (fun x : ℝ => (x + A) + C)
                                  (add_comm B D)
                              _ = (D + (B + A)) + C := by
                                exact congrArg (fun x : ℝ => x + C) (add_assoc D B A)
                              _ = (D + (A + B)) + C := by
                                exact congrArg
                                  (fun x : ℝ => (D + x) + C)
                                  (add_comm B A)
                              _ = D + ((A + B) + C) := by
                                exact add_assoc D (A + B) C
                              _ =
                                  |C| +
                                    (entireFunctionJensenRadialGapSum F hF ρ +
                                      entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
                                      C) := rfl
                          _ = |C| + entireFunctionJensenBoundaryLogAverage F ρ := by
                            exact congrArg (fun x : ℝ => |C| + x) hJensen
                      And.intro hgap
                        (Eq.subst
                          (motive := fun x : ℝ =>
                            entireFunctionJensenRadialGapSum F hF ρ ≤ x)
                          htarget
                          hle_add))))

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
  exact
    Exists.elim
      (entireFunction_classicalJensenFormula_originFactoredRadialGapSum_le_boundaryLogAverage
        F hF hnontrivial)
      (fun J hJ =>
        have hclosed :
            ∀ R : ℝ,
              1 ≤ R →
              Summable
                (fun z : EntireFunctionZero F =>
                  entireFunctionZeroMultiplicityClosedDiskSummand F hF R z) :=
          fun R hR =>
            entireFunctionZeroMultiplicityClosedDiskSummable_of_nonzeroClosedDiskSummable
              F hF (hJ.1 R hR)
        have hradial :
            ∀ ρ : ℝ,
              1 ≤ ρ →
              Summable
                  (fun z : EntireFunctionZero F =>
                    entireFunctionJensenRadialGapSummand F hF ρ z) ∧
                entireFunctionJensenRadialGapSum F hF ρ ≤
                  entireFunctionOriginMultiplicityLogContribution F hF + |J| +
                    entireFunctionJensenBoundaryLogAverage F ρ :=
          fun ρ hρ =>
            match hJ.2 ρ hρ with
            | ⟨hgap, hbound⟩ =>
                have hJ_le :
                    J + entireFunctionJensenBoundaryLogAverage F ρ ≤
                      entireFunctionOriginMultiplicityLogContribution F hF + |J| +
                        entireFunctionJensenBoundaryLogAverage F ρ := by
                  have hJ_abs : J ≤ |J| := le_abs_self J
                  have horigin_nonneg :
                      0 ≤ entireFunctionOriginMultiplicityLogContribution F hF := by
                    calc
                      0 ≤ (entireFunctionZeroMultiplicity F hF 0 : ℝ) * Real.log 2 :=
                        mul_nonneg
                          (Nat.cast_nonneg (entireFunctionZeroMultiplicity F hF 0))
                          real_log_two_pos.le
                      _ = entireFunctionOriginMultiplicityLogContribution F hF := rfl
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
                  have horigin_target :
                      |J| + entireFunctionJensenBoundaryLogAverage F ρ ≤
                        entireFunctionOriginMultiplicityLogContribution F hF + |J| +
                          entireFunctionJensenBoundaryLogAverage F ρ :=
                    Eq.subst
                      (motive := fun x : ℝ =>
                        |J| + entireFunctionJensenBoundaryLogAverage F ρ ≤ x)
                      hassoc
                      horigin_shift
                  exact le_trans hJ_shift horigin_target
                And.intro hgap (le_trans hbound hJ_le)
        have hcounting :
            ∀ R : ℝ,
              1 ≤ R →
              entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2 ≤
                entireFunctionOriginMultiplicityLogContribution F hF + |J| +
                  entireFunctionJensenRadialGapSum F hF (2 * R) :=
          fun R hR =>
            have hρ : 1 ≤ 2 * R :=
              one_le_doubled_radius_of_one_le hR
            have hradial_at :
                Summable
                    (fun z : EntireFunctionZero F =>
                      entireFunctionJensenRadialGapSummand F hF (2 * R) z) ∧
                  entireFunctionJensenRadialGapSum F hF (2 * R) ≤
                    J + entireFunctionJensenBoundaryLogAverage F (2 * R) :=
              hJ.2 (2 * R) hρ
            have hgap :
                Summable
                  (fun z : EntireFunctionZero F =>
                    entireFunctionJensenRadialGapSummand F hF (2 * R) z) :=
              hradial_at.1
            have hcount :
                entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2 ≤
                  entireFunctionOriginMultiplicityLogContribution F hF +
                    entireFunctionJensenRadialGapSum F hF (2 * R) :=
              entireFunctionZeroMultiplicityCountingInClosedDisk_mul_log_two_le_originContribution_plus_radialGapSum
                F hF hR (hJ.1 R hR) hgap
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
            le_trans hcount
              (Eq.subst
                (motive := fun x : ℝ =>
                  entireFunctionOriginMultiplicityLogContribution F hF +
                    entireFunctionJensenRadialGapSum F hF (2 * R) ≤ x)
                hassoc
                hshift)
        Exists.intro
          (entireFunctionOriginMultiplicityLogContribution F hF + |J|)
          (And.intro hclosed (And.intro hradial hcounting)))

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
  exact
    Exists.elim
      (entireFunction_classicalJensenFormula_radialGapSum_le_boundaryLogAverage
        F hF hnontrivial)
      (fun _J hJ =>
        hJ.1 R hR)

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
  exact
    Exists.elim hweighted
      (fun J hJ =>
        Exists.intro ((Real.log 2)⁻¹ * J)
          (fun R hR =>
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
                    (Real.log 2)⁻¹ *
                      (Real.log 2 * entireFunctionZeroMultiplicityCountingInClosedDisk F hF R) := by
                  exact congrArg
                    (fun x : ℝ => (Real.log 2)⁻¹ * x)
                    (mul_comm
                      (entireFunctionZeroMultiplicityCountingInClosedDisk F hF R)
                      (Real.log 2))
                _ =
                    ((Real.log 2)⁻¹ * Real.log 2) *
                      entireFunctionZeroMultiplicityCountingInClosedDisk F hF R := by
                  exact
                    (mul_assoc
                      (Real.log 2)⁻¹
                      (Real.log 2)
                      (entireFunctionZeroMultiplicityCountingInClosedDisk F hF R)).symm
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
              exact mul_add
                (Real.log 2)⁻¹
                J
                (entireFunctionJensenBoundaryLogAverage F (2 * R))
            hleft ▸ hright ▸ hscaled))

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
  exact
    Exists.elim
      (entireFunction_classicalJensenFormula_radialGapSum_le_boundaryLogAverage
        F hF hnontrivial)
      (fun J hJ =>
        Exists.intro (J + J)
          (fun R hR =>
            have hρ : 1 ≤ 2 * R :=
              one_le_doubled_radius_of_one_le hR
            have hradial_at :
                Summable
                    (fun z : EntireFunctionZero F =>
                      entireFunctionJensenRadialGapSummand F hF (2 * R) z) ∧
                  entireFunctionJensenRadialGapSum F hF (2 * R) ≤
                    J + entireFunctionJensenBoundaryLogAverage F (2 * R) :=
              hJ.2.1 (2 * R) hρ
            have hgap_bound :
                entireFunctionJensenRadialGapSum F hF (2 * R) ≤
                  J + entireFunctionJensenBoundaryLogAverage F (2 * R) :=
              hradial_at.2
            have hcount_gap :
                entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2 ≤
                  J + entireFunctionJensenRadialGapSum F hF (2 * R) :=
              hJ.2.2 R hR
            have hbound :
                J + entireFunctionJensenRadialGapSum F hF (2 * R) ≤
                  J + (J + entireFunctionJensenBoundaryLogAverage F (2 * R)) :=
              add_le_add_left hgap_bound J
            have htarget :
                J + (J + entireFunctionJensenBoundaryLogAverage F (2 * R)) =
                  J + J + entireFunctionJensenBoundaryLogAverage F (2 * R) := by
              exact
                (add_assoc J J
                  (entireFunctionJensenBoundaryLogAverage F (2 * R))).symm
            Eq.subst
              (motive := fun x : ℝ =>
                entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2 ≤ x)
              htarget
              (le_trans hcount_gap hbound)))

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
  exact
    match
      entireFunction_jensenFormula_zeroMultiplicityCounting_closedDisk_le_scaledBoundaryLogAverage
        F hF hnontrivial with
    | ⟨J, hcount⟩ =>
        Exists.intro J
          (fun R hR =>
            match entireFunction_jensenBoundaryLogAverage_regularity F hF hnontrivial R hR with
            | ⟨hbdd, hint⟩ =>
                ⟨hbdd, hint, hcount R hR⟩)

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
  exact
    match
      entireFunctionZeroMultiplicityCounting_closedDisk_le_boundaryLogAverage
        F hF hnontrivial with
    | ⟨J, hJ⟩ =>
        Exists.intro J
          (fun R hR =>
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
                le_trans hcount hwith_constant)

end

end LFunctions
end Boundary

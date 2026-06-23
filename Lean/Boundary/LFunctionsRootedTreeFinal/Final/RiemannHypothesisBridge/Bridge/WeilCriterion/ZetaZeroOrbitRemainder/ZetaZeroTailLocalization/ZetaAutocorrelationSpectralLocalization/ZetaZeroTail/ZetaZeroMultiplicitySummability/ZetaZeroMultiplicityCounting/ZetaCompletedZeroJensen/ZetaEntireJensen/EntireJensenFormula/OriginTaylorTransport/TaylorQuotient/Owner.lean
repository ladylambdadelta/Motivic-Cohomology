import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.OriginTaylorTransport.NonzeroAtOrigin.Owner

/-!
# Origin Taylor transport and zero-counting consequences

This owner layer was split from `OriginTaylorTransport.Owner` without changing public declaration names.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

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
  let ⟨g, hg_spec⟩ := hmodel
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

end
end LFunctions
end Boundary

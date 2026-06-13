import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Analytic order lemmas for zeta-side zero multiplicities

This file owns the local analytic-order facts used by the zeta zero-side
multiplicity bookkeeping.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Eventual equality transports eventual zero-ness from the left germ to the
right germ. -/
theorem eventually_zero_of_eventuallyEq_left
    {f g : ℂ → ℂ} {z : ℂ}
    (hfg : f =ᶠ[𝓝 z] g)
    (hfzero : ∀ᶠ w in 𝓝 z, f w = 0) :
    ∀ᶠ w in 𝓝 z, g w = 0 := by
  filter_upwards [hfg, hfzero] with w hfgw hfzerow
  exact hfgw.symm.trans hfzerow

/-- Eventual equality transports a local Weierstrass-style finite order
factorization from the left germ to the right germ. -/
theorem eventuallyEq_pow_smul_nonzero_factor_right
    {f g a : ℂ → ℂ} {z : ℂ} {n : ℕ}
    (hfg : f =ᶠ[𝓝 z] g)
    (hfactor :
      ∀ᶠ w in 𝓝 z, f w = (w - z) ^ n • a w) :
    ∀ᶠ w in 𝓝 z, g w = (w - z) ^ n • a w := by
  filter_upwards [hfg, hfactor] with w hfgw hfactorw
  exact hfgw.symm.trans hfactorw

/-- The finite factorization witness transported by eventual equality. -/
theorem analyticAt_order_nat_factor_of_eventuallyEq
    {f g : ℂ → ℂ} {z : ℂ} {n : ℕ}
    (hf : AnalyticAt ℂ f z)
    (hfg : f =ᶠ[𝓝 z] g)
    (hforder : hf.order = (n : ℕ∞)) :
    ∃ a : ℂ → ℂ,
      AnalyticAt ℂ a z ∧
      a z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, g w = (w - z) ^ n • a w := by
  match (AnalyticAt.order_eq_nat_iff hf n).mp hforder with
  | ⟨a, ha, haz, hfactor⟩ =>
      exact ⟨a, ha, haz,
        eventuallyEq_pow_smul_nonzero_factor_right hfg hfactor⟩

/-- Local eventual equality preserves analytic order. -/
theorem analyticAt_order_eq_of_eventuallyEq
    {f g : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z)
    (hg : AnalyticAt ℂ g z)
    (hfg : f =ᶠ[𝓝 z] g) :
    hf.order = hg.order := by
  by_cases htop : hf.order = ⊤
  · have hfzero : ∀ᶠ w in 𝓝 z, f w = 0 :=
      (AnalyticAt.order_eq_top_iff hf).mp htop
    have hgzero : ∀ᶠ w in 𝓝 z, g w = 0 :=
      eventually_zero_of_eventuallyEq_left hfg hfzero
    have hgorder : hg.order = ⊤ :=
      (AnalyticAt.order_eq_top_iff hg).mpr hgzero
    exact htop.trans hgorder.symm
  · let n : ℕ := hf.order.toNat
    have hforder : hf.order = (n : ℕ∞) :=
      (ENat.coe_toNat htop).symm
    have hgfactor :
        ∃ a : ℂ → ℂ,
          AnalyticAt ℂ a z ∧
          a z ≠ 0 ∧
          ∀ᶠ w in 𝓝 z, g w = (w - z) ^ n • a w :=
      analyticAt_order_nat_factor_of_eventuallyEq hf hfg hforder
    have hgorder : hg.order = (n : ℕ∞) :=
      (AnalyticAt.order_eq_nat_iff hg n).mpr hgfactor
    exact hforder.trans hgorder.symm

/-- Multiplication by a nonzero scalar-valued analytic germ preserves a finite
local factorization witness. -/
theorem analyticAt_unit_mul_pow_smul_factor
    {u a : ℂ → ℂ} {z : ℂ} {n : ℕ}
    (hu : AnalyticAt ℂ u z)
    (ha : AnalyticAt ℂ a z)
    (huz : u z ≠ 0)
    (haz : a z ≠ 0) :
    ∃ b : ℂ → ℂ,
      AnalyticAt ℂ b z ∧
      b z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z,
        u w * ((w - z) ^ n • a w) = (w - z) ^ n • b w := by
  let b : ℂ → ℂ := fun w : ℂ => u w * a w
  have hb : AnalyticAt ℂ b z :=
    hu.mul ha
  have hbz : b z ≠ 0 :=
    mul_ne_zero huz haz
  have heq :
      ∀ᶠ w in 𝓝 z,
        u w * ((w - z) ^ n • a w) = (w - z) ^ n • b w := by
    filter_upwards [] with w
    change u w * (((w - z) ^ n) * a w) =
      ((w - z) ^ n) * (u w * a w)
    exact mul_left_comm (u w) ((w - z) ^ n) (a w)
  exact ⟨b, hb, hbz, heq⟩

/-- Multiplication by an analytic unit transports a finite order factorization
of a germ to the product germ. -/
theorem analyticAt_order_mul_left_finite_factor
    {u f : ℂ → ℂ} {z : ℂ} {n : ℕ}
    (hu : AnalyticAt ℂ u z)
    (huz : u z ≠ 0)
    (hf : AnalyticAt ℂ f z)
    (hforder : hf.order = (n : ℕ∞)) :
    ∃ b : ℂ → ℂ,
      AnalyticAt ℂ b z ∧
      b z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, u w * f w = (w - z) ^ n • b w := by
  match (AnalyticAt.order_eq_nat_iff hf n).mp hforder with
  | ⟨a, ha, haz, hfactor⟩ =>
      match analyticAt_unit_mul_pow_smul_factor hu ha huz haz with
      | ⟨b, hb, hbz, hunitFactor⟩ =>
          have hproductFactor :
              ∀ᶠ w in 𝓝 z, u w * f w = (w - z) ^ n • b w := by
            filter_upwards [hfactor, hunitFactor] with w hfactorw hunitw
            exact (congrArg (fun y : ℂ => u w * y) hfactorw).trans hunitw
          exact ⟨b, hb, hbz, hproductFactor⟩

/-- Multiplication by an analytic unit on the left preserves analytic order. -/
theorem analyticAt_order_mul_left_eq
    {u f : ℂ → ℂ} {z : ℂ}
    (hu : AnalyticAt ℂ u z)
    (huz : u z ≠ 0)
    (hf : AnalyticAt ℂ f z) :
    (hu.mul hf).order = hf.order := by
  by_cases htop : hf.order = ⊤
  · have hfzero : ∀ᶠ w in 𝓝 z, f w = 0 :=
      (AnalyticAt.order_eq_top_iff hf).mp htop
    have hproductZero :
        ∀ᶠ w in 𝓝 z, u w * f w = 0 := by
      filter_upwards [hfzero] with w hfw
      exact (congrArg (fun y : ℂ => u w * y) hfw).trans (mul_zero (u w))
    have hproductOrder : (hu.mul hf).order = ⊤ :=
      (AnalyticAt.order_eq_top_iff (hu.mul hf)).mpr hproductZero
    exact hproductOrder.trans htop.symm
  · let n : ℕ := hf.order.toNat
    have hforder : hf.order = (n : ℕ∞) :=
      (ENat.coe_toNat htop).symm
    have hproductFactor :
        ∃ b : ℂ → ℂ,
          AnalyticAt ℂ b z ∧
          b z ≠ 0 ∧
          ∀ᶠ w in 𝓝 z, u w * f w = (w - z) ^ n • b w :=
      analyticAt_order_mul_left_finite_factor hu huz hf hforder
    have hproductOrder : (hu.mul hf).order = (n : ℕ∞) :=
      (AnalyticAt.order_eq_nat_iff (hu.mul hf) n).mpr hproductFactor
    exact hproductOrder.trans hforder.symm

/-- If one analytic germ is locally a unit multiple of another, their analytic orders agree. -/
theorem analyticAt_order_eq_of_eventuallyEq_mul_left
    {f g u : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z)
    (hg : AnalyticAt ℂ g z)
    (hu : AnalyticAt ℂ u z)
    (huz : u z ≠ 0)
    (hfg : f =ᶠ[𝓝 z] fun w => u w * g w) :
    hf.order = hg.order := by
  have hmul : AnalyticAt ℂ (fun w : ℂ => u w * g w) z :=
    hu.mul hg
  have hfirst : hf.order = hmul.order :=
    analyticAt_order_eq_of_eventuallyEq hf hmul hfg
  have hsecond : hmul.order = hg.order :=
    analyticAt_order_mul_left_eq hu huz hg
  exact hfirst.trans hsecond

/-- An analytic zero which is not locally identically zero has positive finite
order. -/
theorem analyticAt_order_toNat_pos_of_zero_not_eventually_zero
    {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z)
    (hz : f z = 0)
    (hnot : ¬ ∀ᶠ w in 𝓝 z, f w = 0) :
    0 < hf.order.toNat := by
  have horder_ne_top : hf.order ≠ ⊤ := by
    intro horder_top
    exact hnot ((AnalyticAt.order_eq_top_iff hf).mp horder_top)
  exact Nat.pos_iff_ne_zero.mpr
    (fun horder_toNat_zero =>
      match ENat.toNat_eq_zero.mp horder_toNat_zero with
      | Or.inl horder_zero =>
          let hfactor := (AnalyticAt.order_eq_nat_iff hf 0).mp horder_zero
          match hfactor with
          | ⟨g, _hg_analytic, hg_nonzero, hg_eventually⟩ =>
              have hcenter :
                  g z = f z := by
                have hcenter_eventual :
                    f z = (z - z) ^ 0 • g z :=
                  hg_eventually.self_of_nhds
                have hpow : (z - z) ^ 0 = (1 : ℂ) :=
                  pow_zero (z - z)
                have hsmul_one :
                    (z - z) ^ 0 • g z = (1 : ℂ) • g z :=
                  congrArg (fun a : ℂ => a • g z) hpow
                have hone_smul :
                    (1 : ℂ) • g z = g z :=
                  one_smul ℂ (g z)
                have hsmul :
                    (z - z) ^ 0 • g z = g z :=
                  Eq.trans hsmul_one hone_smul
                exact Eq.trans hsmul.symm hcenter_eventual.symm
              have hg_zero : g z = 0 :=
                Eq.trans hcenter hz
              hg_nonzero hg_zero
      | Or.inr horder_top =>
          horder_ne_top horder_top)

end

end LFunctions
end Boundary

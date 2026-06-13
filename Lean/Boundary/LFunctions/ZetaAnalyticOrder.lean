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

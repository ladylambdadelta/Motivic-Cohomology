import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaBoundaryPL.DampedFamily.SubcriticalAbsorbers

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Filter Topology
local notation "π" => Real.pi

/-- The universal positive coefficient in the explicit upper-tail damping
factor. -/
theorem upperTailDamping_sqrtTwo_half_pos :
    0 < Real.sqrt 2 / 2 := by
  exact div_pos (Real.sqrt_pos.mpr zero_lt_two) zero_lt_two

/-- Right-boundary upper-tail eventual constant bound for the holomorphic
upper-tail damped family. -/
theorem verticalStripUpperTailDampedFamily_rightBoundary_eventually_upperTail_bound
    (f : ℂ → ℂ)
    {a b ε A B : ℝ}
    {m : ℕ}
    (hab : a < b)
    (hε_pos : 0 < ε)
    (hA : 0 < A)
    (hB : 0 < B)
    (hright :
      ∀ z : ℂ,
        z.re = b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m)) :
    ∀ᶠ T in Filter.atTop,
      ∀ z : ℂ,
        z.re = b →
        z.im = T →
        ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤ 1 := by
  let K : ℝ := Real.sqrt 2 / 2
  let s : ℝ := verticalStripUpperTailDampingScale a b
  let M : ℝ := |a| + |b| + 2
  have hK_pos : 0 < K :=
    upperTailDamping_sqrtTwo_half_pos
  have hs_pos : 0 < s :=
    verticalStripUpperTailDampingScale_pos a b
  have htail :
      ∀ᶠ T : ℝ in Filter.atTop,
        A * Real.exp (B * (1 + T) ^ m) *
            Real.exp (-(ε * (K * Real.exp (s * (M + T))))) ≤ 1 :=
    finiteOrder_exp_mul_shifted_upperTail_absorber_eventually_le_one
      A B K s M ε m hA hB hK_pos hs_pos hε_pos
  have hlarge : ∀ᶠ T : ℝ in Filter.atTop, 1 ≤ T :=
    eventually_ge_atTop (1 : ℝ)
  exact
    (htail.and hlarge).mono
      fun T hT z hz_re hz_im =>
        have hz_im_tail : 1 ≤ z.im :=
          Eq.subst
            (motive := fun x : ℝ => 1 ≤ x)
            hz_im.symm
            hT.2
        have him_nonneg : 0 ≤ z.im :=
          le_trans zero_le_one hz_im_tail
        have him_norm : ‖z.im‖ = z.im :=
          Real.norm_of_nonneg him_nonneg
        have hboundary :
            ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m) :=
          hright z hz_re
            (Eq.subst
              (motive := fun x : ℝ => 1 ≤ x)
              him_norm.symm
              hz_im_tail)
        let g : ℂ :=
          Complex.exp
            (-((ε : ℝ) : ℂ) *
              verticalStripUpperTailDampingKernel a b z)
        have hfactor :
            ‖g‖ ≤
              Real.exp
                (-(ε * (Real.sqrt 2 / 2) *
                  Real.exp
                    (verticalStripUpperTailDampingScale a b *
                      (|a| + |b| + 2 + z.im)))) :=
          verticalStripUpperTailDampingFactor_norm_le_exp_explicit
            a b ε (le_of_lt hε_pos) z
            (le_trans (le_of_lt hab) (le_of_eq hz_re.symm))
            (le_of_eq hz_re)
        have hmul_eq :
            ‖verticalStripUpperTailDampedFamily f a b ε z‖ = ‖f z‖ * ‖g‖ := by
          calc
            ‖verticalStripUpperTailDampedFamily f a b ε z‖ =
                ‖f z * g‖ := by
              rfl
            _ = ‖f z‖ * ‖g‖ := by
              exact norm_mul (f z) g
        have hraw :
            ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤
              (A * Real.exp (B * (1 + ‖z.im‖) ^ m)) *
                Real.exp
                  (-(ε * (Real.sqrt 2 / 2) *
                    Real.exp
                      (verticalStripUpperTailDampingScale a b *
                        (|a| + |b| + 2 + z.im)))) := by
          have hfactor_nonneg : 0 ≤ ‖g‖ :=
            norm_nonneg g
          have hfirst :
              ‖f z‖ * ‖g‖ ≤
                (A * Real.exp (B * (1 + ‖z.im‖) ^ m)) * ‖g‖ :=
            mul_le_mul_of_nonneg_right hboundary hfactor_nonneg
          have henvelope_nonneg :
              0 ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m) :=
            mul_nonneg (le_of_lt hA)
              (le_of_lt (Real.exp_pos (B * (1 + ‖z.im‖) ^ m)))
          have hsecond :
              (A * Real.exp (B * (1 + ‖z.im‖) ^ m)) * ‖g‖ ≤
                (A * Real.exp (B * (1 + ‖z.im‖) ^ m)) *
                  Real.exp
                    (-(ε * (Real.sqrt 2 / 2) *
                      Real.exp
                        (verticalStripUpperTailDampingScale a b *
                          (|a| + |b| + 2 + z.im)))) :=
            mul_le_mul_of_nonneg_left hfactor henvelope_nonneg
          exact
            Eq.subst
              (motive := fun x : ℝ =>
                x ≤
                  (A * Real.exp (B * (1 + ‖z.im‖) ^ m)) *
                    Real.exp
                      (-(ε * (Real.sqrt 2 / 2) *
                        Real.exp
                          (verticalStripUpperTailDampingScale a b *
                            (|a| + |b| + 2 + z.im)))))
              hmul_eq.symm
              (le_trans hfirst hsecond)
        have htarget_eq :
            (A * Real.exp (B * (1 + ‖z.im‖) ^ m)) *
                Real.exp
                  (-(ε * (Real.sqrt 2 / 2) *
                    Real.exp
                      (verticalStripUpperTailDampingScale a b *
                        (|a| + |b| + 2 + z.im)))) =
              A * Real.exp (B * (1 + T) ^ m) *
                Real.exp (-(ε * (K * Real.exp (s * (M + T))))) := by
          have hheight :
              ‖z.im‖ = T :=
            Eq.trans him_norm hz_im
          have hshift :
              |a| + |b| + 2 + z.im = M + T := by
            calc
              |a| + |b| + 2 + z.im = M + z.im := rfl
              _ = M + T := congrArg (fun x : ℝ => M + x) hz_im
          have hfactor_arg :
              ε * (Real.sqrt 2 / 2) *
                    Real.exp
                      (verticalStripUpperTailDampingScale a b *
                        (|a| + |b| + 2 + z.im)) =
                ε * (K * Real.exp (s * (M + T))) := by
            calc
              ε * (Real.sqrt 2 / 2) *
                    Real.exp
                      (verticalStripUpperTailDampingScale a b *
                        (|a| + |b| + 2 + z.im)) =
                  (ε * K) * Real.exp (s * (M + T)) := by
                exact congrArg₂ (fun x y : ℝ => (ε * x) * Real.exp (s * y)) rfl hshift
              _ = ε * (K * Real.exp (s * (M + T))) := by
                exact mul_assoc ε K (Real.exp (s * (M + T)))
          exact congrArg₂ (fun x y : ℝ => x * y)
            (congrArg
              (fun x : ℝ => A * Real.exp (B * (1 + x) ^ m))
              hheight)
            (congrArg Real.exp (congrArg Neg.neg hfactor_arg))
        le_trans hraw
          (Eq.subst
            (motive := fun x : ℝ => x ≤ 1)
            htarget_eq.symm
            hT.1)

/-- Left-boundary upper-tail eventual constant bound for the holomorphic
upper-tail damped family. -/
theorem verticalStripUpperTailDampedFamily_leftBoundary_eventually_upperTail_bound
    (f : ℂ → ℂ)
    {a b ε A B : ℝ}
    {m : ℕ}
    (hab : a < b)
    (hε_pos : 0 < ε)
    (hA : 0 < A)
    (hB : 0 < B)
    (hleft :
      ∀ z : ℂ,
        z.re = a →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m)) :
    ∀ᶠ T in Filter.atTop,
      ∀ z : ℂ,
        z.re = a →
        z.im = T →
        ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤ 1 := by
  let K : ℝ := Real.sqrt 2 / 2
  let s : ℝ := verticalStripUpperTailDampingScale a b
  let M : ℝ := |a| + |b| + 2
  have hK_pos : 0 < K :=
    upperTailDamping_sqrtTwo_half_pos
  have hs_pos : 0 < s :=
    verticalStripUpperTailDampingScale_pos a b
  have htail :
      ∀ᶠ T : ℝ in Filter.atTop,
        A * Real.exp (B * (1 + T) ^ m) *
            Real.exp (-(ε * (K * Real.exp (s * (M + T))))) ≤ 1 :=
    finiteOrder_exp_mul_shifted_upperTail_absorber_eventually_le_one
      A B K s M ε m hA hB hK_pos hs_pos hε_pos
  have hlarge : ∀ᶠ T : ℝ in Filter.atTop, 1 ≤ T :=
    eventually_ge_atTop (1 : ℝ)
  exact
    (htail.and hlarge).mono
      fun T hT z hz_re hz_im =>
        have hz_im_tail : 1 ≤ z.im :=
          Eq.subst
            (motive := fun x : ℝ => 1 ≤ x)
            hz_im.symm
            hT.2
        have him_nonneg : 0 ≤ z.im :=
          le_trans zero_le_one hz_im_tail
        have him_norm : ‖z.im‖ = z.im :=
          Real.norm_of_nonneg him_nonneg
        have hboundary :
            ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m) :=
          hleft z hz_re
            (Eq.subst
              (motive := fun x : ℝ => 1 ≤ x)
              him_norm.symm
              hz_im_tail)
        let g : ℂ :=
          Complex.exp
            (-((ε : ℝ) : ℂ) *
              verticalStripUpperTailDampingKernel a b z)
        have hfactor :
            ‖g‖ ≤
              Real.exp
                (-(ε * (Real.sqrt 2 / 2) *
                  Real.exp
                    (verticalStripUpperTailDampingScale a b *
                      (|a| + |b| + 2 + z.im)))) :=
          verticalStripUpperTailDampingFactor_norm_le_exp_explicit
            a b ε (le_of_lt hε_pos) z
            (le_of_eq hz_re.symm)
            (le_trans (le_of_eq hz_re) (le_of_lt hab))
        have hmul_eq :
            ‖verticalStripUpperTailDampedFamily f a b ε z‖ = ‖f z‖ * ‖g‖ := by
          calc
            ‖verticalStripUpperTailDampedFamily f a b ε z‖ =
                ‖f z * g‖ := by
              rfl
            _ = ‖f z‖ * ‖g‖ := by
              exact norm_mul (f z) g
        have hraw :
            ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤
              (A * Real.exp (B * (1 + ‖z.im‖) ^ m)) *
                Real.exp
                  (-(ε * (Real.sqrt 2 / 2) *
                    Real.exp
                      (verticalStripUpperTailDampingScale a b *
                        (|a| + |b| + 2 + z.im)))) := by
          have hfactor_nonneg : 0 ≤ ‖g‖ :=
            norm_nonneg g
          have hfirst :
              ‖f z‖ * ‖g‖ ≤
                (A * Real.exp (B * (1 + ‖z.im‖) ^ m)) * ‖g‖ :=
            mul_le_mul_of_nonneg_right hboundary hfactor_nonneg
          have henvelope_nonneg :
              0 ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m) :=
            mul_nonneg (le_of_lt hA)
              (le_of_lt (Real.exp_pos (B * (1 + ‖z.im‖) ^ m)))
          have hsecond :
              (A * Real.exp (B * (1 + ‖z.im‖) ^ m)) * ‖g‖ ≤
                (A * Real.exp (B * (1 + ‖z.im‖) ^ m)) *
                  Real.exp
                    (-(ε * (Real.sqrt 2 / 2) *
                      Real.exp
                        (verticalStripUpperTailDampingScale a b *
                          (|a| + |b| + 2 + z.im)))) :=
            mul_le_mul_of_nonneg_left hfactor henvelope_nonneg
          exact
            Eq.subst
              (motive := fun x : ℝ =>
                x ≤
                  (A * Real.exp (B * (1 + ‖z.im‖) ^ m)) *
                    Real.exp
                      (-(ε * (Real.sqrt 2 / 2) *
                        Real.exp
                          (verticalStripUpperTailDampingScale a b *
                            (|a| + |b| + 2 + z.im)))))
              hmul_eq.symm
              (le_trans hfirst hsecond)
        have htarget_eq :
            (A * Real.exp (B * (1 + ‖z.im‖) ^ m)) *
                Real.exp
                  (-(ε * (Real.sqrt 2 / 2) *
                    Real.exp
                      (verticalStripUpperTailDampingScale a b *
                        (|a| + |b| + 2 + z.im)))) =
              A * Real.exp (B * (1 + T) ^ m) *
                Real.exp (-(ε * (K * Real.exp (s * (M + T))))) := by
          have hheight :
              ‖z.im‖ = T :=
            Eq.trans him_norm hz_im
          have hshift :
              |a| + |b| + 2 + z.im = M + T := by
            calc
              |a| + |b| + 2 + z.im = M + z.im := rfl
              _ = M + T := congrArg (fun x : ℝ => M + x) hz_im
          have hfactor_arg :
              ε * (Real.sqrt 2 / 2) *
                    Real.exp
                      (verticalStripUpperTailDampingScale a b *
                        (|a| + |b| + 2 + z.im)) =
                ε * (K * Real.exp (s * (M + T))) := by
            calc
              ε * (Real.sqrt 2 / 2) *
                    Real.exp
                      (verticalStripUpperTailDampingScale a b *
                        (|a| + |b| + 2 + z.im)) =
                  (ε * K) * Real.exp (s * (M + T)) := by
                exact congrArg₂ (fun x y : ℝ => (ε * x) * Real.exp (s * y)) rfl hshift
              _ = ε * (K * Real.exp (s * (M + T))) := by
                exact mul_assoc ε K (Real.exp (s * (M + T)))
          exact congrArg₂ (fun x y : ℝ => x * y)
            (congrArg
              (fun x : ℝ => A * Real.exp (B * (1 + x) ^ m))
              hheight)
            (congrArg Real.exp (congrArg Neg.neg hfactor_arg))
        le_trans hraw
          (Eq.subst
            (motive := fun x : ℝ => x ≤ 1)
            htarget_eq.symm
            hT.1)

/-- The subcritical holomorphic damping factor is bounded by one on the
open-strip Phragmen-Lindelöf filter. -/
theorem verticalStripSubcriticalCosineDampingFactor_isBigO_one_on_openStrip
    {a b d ε : ℝ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε : 0 ≤ ε) :
    (fun z : ℂ =>
      Complex.exp
        (-((ε : ℝ) : ℂ) *
          verticalStripSubcriticalCosineBarrierKernel a b d z)) =O[
        Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
          𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
      (fun _ : ℂ => (1 : ℝ)) := by
  let strip : Set ℂ := Complex.re ⁻¹' Set.Ioo a b
  let heightFilter : Filter ℂ :=
    Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop
  have hbound :
      ∀ᶠ z in heightFilter ⊓ 𝓟 strip,
        ‖Complex.exp
            (-((ε : ℝ) : ℂ) *
              verticalStripSubcriticalCosineBarrierKernel a b d z)‖ ≤
          ‖(1 : ℝ)‖ := by
    exact
      (Filter.eventually_inf_principal).2
        (Filter.Eventually.of_forall
          fun z hz =>
            Eq.subst
              (motive := fun r : ℝ =>
                ‖Complex.exp
                    (-((ε : ℝ) : ℂ) *
                      verticalStripSubcriticalCosineBarrierKernel a b d z)‖ ≤ r)
              (norm_one : ‖(1 : ℝ)‖ = 1).symm
              (verticalStripSubcriticalCosineDampingFactor_norm_le_one_on_closedStrip
                hab hd_pos hd_threshold hε z
                (le_of_lt hz.1)
                (le_of_lt hz.2)))
  exact
    Asymptotics.IsBigO.of_bound'
      hbound

/-- Big-O multiplication transport for the subcritical cosine-damped family
once the damping factor is bounded by one on the strip filter. -/
theorem verticalStripSubcriticalCosineDampedFamily_subcritical_growth_of_dampingFactor_isBigO_one
    (f : ℂ → ℂ)
    (a b d ε : ℝ)
    (hdamp :
      (fun z : ℂ =>
        Complex.exp
          (-((ε : ℝ) : ℂ) *
            verticalStripSubcriticalCosineBarrierKernel a b d z)) =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
        (fun _ : ℂ => (1 : ℝ)))
    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          f =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|))) :
    ∃ c : ℝ,
      c < Real.pi / (b - a) ∧
      ∃ D : ℝ,
        verticalStripSubcriticalCosineDampedFamily f a b d ε =O[
            Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
              𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  match hfinite with
  | ⟨c, hc, D, hD⟩ =>
      let g : ℂ → ℂ :=
        fun z : ℂ =>
          Complex.exp
            (-((ε : ℝ) : ℂ) *
              verticalStripSubcriticalCosineBarrierKernel a b d z)
      have hproduct :
          (fun z : ℂ => g z * f z) =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => (1 : ℝ) *
              Real.exp (D * Real.exp (c * |z.im|)) :=
        hdamp.mul hD
      have htarget :
          verticalStripSubcriticalCosineDampedFamily f a b d ε =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) :=
        hproduct.congr
          (fun z : ℂ =>
            calc
              g z * f z = f z * g z := mul_comm (g z) (f z)
              _ = verticalStripSubcriticalCosineDampedFamily f a b d ε z := rfl)
          (fun z : ℂ =>
            one_mul (Real.exp (D * Real.exp (c * |z.im|))))
      exact ⟨c, hc, D, htarget⟩

/-- Subcritical double-exponential Phragmen-Lindelöf growth is preserved by
the subcritical holomorphic cosine damping factor. -/
theorem verticalStripSubcriticalCosineDampedFamily_subcritical_growth
    (f : ℂ → ℂ)
    {a b d ε : ℝ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε : 0 ≤ ε)
    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          f =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|))) :
    ∃ c : ℝ,
      c < Real.pi / (b - a) ∧
      ∃ D : ℝ,
        verticalStripSubcriticalCosineDampedFamily f a b d ε =O[
            Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
              𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  have hdamp :
      (fun z : ℂ =>
        Complex.exp
          (-((ε : ℝ) : ℂ) *
            verticalStripSubcriticalCosineBarrierKernel a b d z)) =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
        (fun _ : ℂ => (1 : ℝ)) :=
    verticalStripSubcriticalCosineDampingFactor_isBigO_one_on_openStrip
      hab hd_pos hd_threshold hε
  exact
    verticalStripSubcriticalCosineDampedFamily_subcritical_growth_of_dampingFactor_isBigO_one
      f a b d ε hdamp hfinite

/-- The subcritical cosine-damped family preserves the two analytic inputs used
by bounded-boundary vertical-strip Phragmen-Lindelöf. -/
theorem verticalStripSubcriticalCosineDampedFamily_analytic_growth_package
    (f : ℂ → ℂ)
    {a b d ε : ℝ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε : 0 ≤ ε)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          f =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|))) :
    DiffContOnCl ℂ (verticalStripSubcriticalCosineDampedFamily f a b d ε)
        (Complex.re ⁻¹' Set.Ioo a b) ∧
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          verticalStripSubcriticalCosineDampedFamily f a b d ε =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  exact
    ⟨verticalStripSubcriticalCosineDampedFamily_diffContOnCl
        f a b d ε hhol,
      verticalStripSubcriticalCosineDampedFamily_subcritical_growth
        f hab hd_pos hd_threshold hε hfinite⟩

/-- The exponential cosine damping factor has norm at most one at each point
of the open strip.

This is just `‖exp u‖ = exp u.re`, applied to
`u = -ε * verticalStripCosineDampingKernel a b z`, together with the preceding
real-part nonnegativity lemma. -/
theorem verticalStripCosineDampingFactor_norm_le_one_on_openStrip
    (a b ε : ℝ)
    (hab : a < b)
    (hε : 0 ≤ ε)
    (z : ℂ)
    (hz : z ∈ Complex.re ⁻¹' Set.Ioo a b) :
    ‖Complex.exp
        (-((ε : ℝ) : ℂ) *
          verticalStripCosineDampingKernel a b z)‖ ≤ 1 := by
  let w : ℂ :=
    -((ε : ℝ) : ℂ) *
      verticalStripCosineDampingKernel a b z
  have hre_nonpos : w.re ≤ 0 :=
    verticalStripCosineDampingExponent_re_nonpos_on_openStrip
      a b ε hab hε z hz
  have hexp_le_one : Real.exp w.re ≤ 1 :=
    Real.exp_le_one_iff.mpr hre_nonpos
  have hnorm : ‖Complex.exp w‖ = Real.exp w.re :=
    complexNorm_exp_eq_realExp_re w
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ 1)
      hnorm.symm
      hexp_le_one

/-- The cosine damping factor is bounded by a constant on the open-strip
Phragmen-Lindelöf filter.

This is the real analytic estimate behind the growth transport: on each
open-strip point the real part of the cosine kernel is nonnegative, so the
factor `exp (-ε K)` has norm at most one.  No boundary decay is asserted here:
on the boundary lines the kernel has real part zero. -/
theorem verticalStripCosineDampingFactor_isBigO_one_on_openStrip
    (a b ε : ℝ)
    (hab : a < b)
    (hε : 0 < ε) :
    (fun z : ℂ =>
      Complex.exp
        (-((ε : ℝ) : ℂ) *
          verticalStripCosineDampingKernel a b z)) =O[
        Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
          𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
      (fun _ : ℂ => (1 : ℝ)) := by
  have hε_nonneg : 0 ≤ ε := le_of_lt hε
  let strip : Set ℂ := Complex.re ⁻¹' Set.Ioo a b
  let heightFilter : Filter ℂ :=
    Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop
  have hbound :
      ∀ᶠ z in heightFilter ⊓ 𝓟 strip,
        ‖Complex.exp
            (-((ε : ℝ) : ℂ) *
              verticalStripCosineDampingKernel a b z)‖ ≤
          ‖(1 : ℝ)‖ := by
    exact
      (Filter.eventually_inf_principal).2
        (Filter.Eventually.of_forall
          fun z hz =>
            Eq.subst
              (motive := fun r : ℝ =>
                ‖Complex.exp
                    (-((ε : ℝ) : ℂ) *
                      verticalStripCosineDampingKernel a b z)‖ ≤ r)
              (norm_one : ‖(1 : ℝ)‖ = 1).symm
              (verticalStripCosineDampingFactor_norm_le_one_on_openStrip
                a b ε hab hε_nonneg z hz))
  refine
    Asymptotics.IsBigO.of_bound'
      hbound

/-- Big-O multiplication transport for the cosine-damped family once the
damping factor is known to be bounded by a constant on the strip filter. -/
theorem verticalStripCosineDampedFamily_subcritical_growth_of_dampingFactor_isBigO_one
    (f : ℂ → ℂ)
    (a b ε : ℝ)
    (hdamp :
      (fun z : ℂ =>
        Complex.exp
          (-((ε : ℝ) : ℂ) *
            verticalStripCosineDampingKernel a b z)) =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
        (fun _ : ℂ => (1 : ℝ)))
    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          f =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|))) :
    ∃ c : ℝ,
      c < Real.pi / (b - a) ∧
      ∃ D : ℝ,
        verticalStripCosineDampedFamily f a b ε =O[
            Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
              𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  match hfinite with
  | ⟨c, hc, D, hD⟩ =>
      let g : ℂ → ℂ :=
        fun z : ℂ =>
          Complex.exp
            (-((ε : ℝ) : ℂ) *
              verticalStripCosineDampingKernel a b z)
      have hproduct :
          (fun z : ℂ => g z * f z) =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => (1 : ℝ) *
              Real.exp (D * Real.exp (c * |z.im|)) :=
        hdamp.mul hD
      have htarget :
          verticalStripCosineDampedFamily f a b ε =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) :=
        hproduct.congr
          (fun z : ℂ =>
            calc
              g z * f z = f z * g z := mul_comm (g z) (f z)
              _ = verticalStripCosineDampedFamily f a b ε z := rfl)
          (fun z : ℂ =>
            one_mul (Real.exp (D * Real.exp (c * |z.im|))))
      exact ⟨c, hc, D, htarget⟩

/-- Subcritical double-exponential Phragmen-Lindelöf growth is preserved by
multiplication by the cosine damping factor. -/
theorem verticalStripCosineDampedFamily_subcritical_growth
    (f : ℂ → ℂ)
    (a b ε : ℝ)
    (hab : a < b)
    (hε : 0 < ε)
    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          f =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|))) :
    ∃ c : ℝ,
      c < Real.pi / (b - a) ∧
      ∃ D : ℝ,
        verticalStripCosineDampedFamily f a b ε =O[
            Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
              𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  match hfinite with
  | ⟨c, hc, D, hD⟩ =>
      have hdamp :
          (fun z : ℂ =>
            Complex.exp
              (-((ε : ℝ) : ℂ) *
                verticalStripCosineDampingKernel a b z)) =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            (fun _ : ℂ => (1 : ℝ)) :=
        verticalStripCosineDampingFactor_isBigO_one_on_openStrip
          a b ε hab hε
      exact
        verticalStripCosineDampedFamily_subcritical_growth_of_dampingFactor_isBigO_one
          f a b ε hdamp ⟨c, hc, D, hD⟩

/-- The cosine-damped family preserves the strip holomorphy and subcritical
Phragmen-Lindelöf growth package needed by the bounded-boundary theorem. -/
theorem verticalStripCosineDampedFamily_analytic_growth_package
    (f : ℂ → ℂ)
    (a b ε : ℝ)
    (hab : a < b)
    (hε : 0 < ε)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          f =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|))) :
    DiffContOnCl ℂ (verticalStripCosineDampedFamily f a b ε)
        (Complex.re ⁻¹' Set.Ioo a b) ∧
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          verticalStripCosineDampedFamily f a b ε =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  exact
    ⟨verticalStripCosineDampedFamily_diffContOnCl f a b ε hab hhol,
      verticalStripCosineDampedFamily_subcritical_growth
        f a b ε hab hε hfinite⟩

/-- The upper-tail damping factor is bounded by a constant on the open-strip
Phragmen-Lindelöf filter. -/
theorem verticalStripUpperTailDampingFactor_isBigO_one_on_openStrip
    (a b ε : ℝ)
    (hε : 0 ≤ ε) :
    (fun z : ℂ =>
      Complex.exp
        (-((ε : ℝ) : ℂ) *
          verticalStripUpperTailDampingKernel a b z)) =O[
        Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
          𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
      (fun _ : ℂ => (1 : ℝ)) := by
  let strip : Set ℂ := Complex.re ⁻¹' Set.Ioo a b
  let heightFilter : Filter ℂ :=
    Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop
  have hbound :
      ∀ᶠ z in heightFilter ⊓ 𝓟 strip,
        ‖Complex.exp
            (-((ε : ℝ) : ℂ) *
              verticalStripUpperTailDampingKernel a b z)‖ ≤
          ‖(1 : ℝ)‖ := by
    exact
      (Filter.eventually_inf_principal).2
        (Filter.Eventually.of_forall
          fun z hz =>
            Eq.subst
              (motive := fun r : ℝ =>
                ‖Complex.exp
                    (-((ε : ℝ) : ℂ) *
                      verticalStripUpperTailDampingKernel a b z)‖ ≤ r)
              (norm_one : ‖(1 : ℝ)‖ = 1).symm
              (verticalStripUpperTailDampingFactor_norm_le_one_on_closedStrip
                a b ε hε z (le_of_lt hz.1) (le_of_lt hz.2)))
  exact
    Asymptotics.IsBigO.of_bound'
      hbound

/-- Big-O multiplication transport for the upper-tail damped family once the
damping factor is known to be bounded by one on the strip filter. -/
theorem verticalStripUpperTailDampedFamily_subcritical_growth_of_dampingFactor_isBigO_one
    (f : ℂ → ℂ)
    (a b ε : ℝ)
    (hdamp :
      (fun z : ℂ =>
        Complex.exp
          (-((ε : ℝ) : ℂ) *
            verticalStripUpperTailDampingKernel a b z)) =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
        (fun _ : ℂ => (1 : ℝ)))
    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          f =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|))) :
    ∃ c : ℝ,
      c < Real.pi / (b - a) ∧
      ∃ D : ℝ,
        verticalStripUpperTailDampedFamily f a b ε =O[
            Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
              𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  match hfinite with
  | ⟨c, hc, D, hD⟩ =>
      let g : ℂ → ℂ :=
        fun z : ℂ =>
          Complex.exp
            (-((ε : ℝ) : ℂ) *
              verticalStripUpperTailDampingKernel a b z)
      have hproduct :
          (fun z : ℂ => g z * f z) =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => (1 : ℝ) *
              Real.exp (D * Real.exp (c * |z.im|)) :=
        hdamp.mul hD
      have htarget :
          verticalStripUpperTailDampedFamily f a b ε =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) :=
        hproduct.congr
          (fun z : ℂ =>
            calc
              g z * f z = f z * g z := mul_comm (g z) (f z)
              _ = verticalStripUpperTailDampedFamily f a b ε z := rfl)
          (fun z : ℂ =>
            one_mul (Real.exp (D * Real.exp (c * |z.im|))))
      exact ⟨c, hc, D, htarget⟩

/-- Subcritical double-exponential Phragmen-Lindelöf growth is preserved by
multiplication by the upper-tail damping factor. -/
theorem verticalStripUpperTailDampedFamily_subcritical_growth
    (f : ℂ → ℂ)
    (a b ε : ℝ)
    (hε : 0 ≤ ε)
    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          f =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|))) :
    ∃ c : ℝ,
      c < Real.pi / (b - a) ∧
      ∃ D : ℝ,
        verticalStripUpperTailDampedFamily f a b ε =O[
            Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
              𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  have hdamp :
      (fun z : ℂ =>
        Complex.exp
          (-((ε : ℝ) : ℂ) *
            verticalStripUpperTailDampingKernel a b z)) =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
        (fun _ : ℂ => (1 : ℝ)) :=
    verticalStripUpperTailDampingFactor_isBigO_one_on_openStrip
      a b ε hε
  exact
    verticalStripUpperTailDampedFamily_subcritical_growth_of_dampingFactor_isBigO_one
      f a b ε hdamp hfinite

/-- The upper-tail damped family preserves the strip holomorphy and subcritical
growth package needed by the bounded-boundary theorem. -/
theorem verticalStripUpperTailDampedFamily_analytic_growth_package
    (f : ℂ → ℂ)
    (a b ε : ℝ)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          f =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
    (hε : 0 ≤ ε) :
    DiffContOnCl ℂ (verticalStripUpperTailDampedFamily f a b ε)
        (Complex.re ⁻¹' Set.Ioo a b) ∧
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          verticalStripUpperTailDampedFamily f a b ε =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  exact
    ⟨verticalStripUpperTailDampedFamily_diffContOnCl f a b ε hhol,
      verticalStripUpperTailDampedFamily_subcritical_growth
        f a b ε hε hfinite⟩




end
end LFunctions
end Boundary

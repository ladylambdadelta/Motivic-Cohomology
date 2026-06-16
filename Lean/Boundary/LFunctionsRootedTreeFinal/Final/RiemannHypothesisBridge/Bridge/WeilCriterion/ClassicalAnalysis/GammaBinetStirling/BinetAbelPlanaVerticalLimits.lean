import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetKernelBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaUpperResidual
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.SetIntegral

/-!
# Vertical-side improper limits for Abel-Plana

This file owns the vertical-side limit inputs for the finite Abel-Plana
principal-value contour formula.  `BinetAbelPlanaCore` owns the concrete
integrands and local integer residues; this file isolates the remaining
improper-integral convergence and splitting facts needed to turn finite-height
vertical sides into the named full Abel-Plana boundary terms.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open Filter MeasureTheory

/-- Lower vertical logarithmic-jump integrand equals twice the Binet
arctangent kernel on the positive half-line. -/
theorem Complex.finiteAbelPlana_log_lowerVerticalIntegrand_eq_two_arctanKernel
    {w : ℂ}
    {t : ℝ}
    (hw : 0 < w.re)
    (ht : 0 < t) :
    Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t =
      2 *
        (Complex.arctan ((t : ℂ) / w) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)) := by
  exact
    Eq.trans
      (Complex.finiteAbelPlana_log_lowerVerticalIntegrand_eq_binet w t)
      (Complex.binetAbelPlana_logJump_integrand_eq_two_arctanKernel
        hw ht)

/-- Lower vertical logarithmic-jump integrability on `(0,∞)`, transported
from the owner arctangent-kernel integrability theorem. -/
theorem Complex.finiteAbelPlana_log_lowerVerticalIntegrand_integrableOn_Ioi
    {w : ℂ}
    (hw : 0 < w.re) :
    IntegrableOn
      (fun t : ℝ => Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)
      (Set.Ioi (0 : ℝ)) := by
  let K : ℝ → ℂ := fun t : ℝ =>
    Complex.arctan ((t : ℂ) / w) /
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
  have hK :
      IntegrableOn K (Set.Ioi (0 : ℝ)) :=
    Complex.binetSecondFormula_arctanKernel_integrable_owner hw
  have htwoK :
      IntegrableOn (fun t : ℝ => 2 * K t) (Set.Ioi (0 : ℝ)) :=
    hK.const_mul 2
  have hpointwise :
      (fun t : ℝ => Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)
        =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun t : ℝ => 2 * K t) :=
    (ae_restrict_mem measurableSet_Ioi).mono
      (fun t ht =>
        Complex.finiteAbelPlana_log_lowerVerticalIntegrand_eq_two_arctanKernel
          hw ht)
  exact htwoK.congr hpointwise.symm

/-- Real-parameter truncation of an integrable positive-half-line function. -/
theorem Complex.tendsto_integral_Ioc_real_of_integrableOn_Ioi
    {f : ℝ → ℂ}
    (hf : IntegrableOn f (Set.Ioi (0 : ℝ))) :
    Tendsto
      (fun T : ℝ => ∫ t : ℝ in Set.Ioc (0 : ℝ) T, f t)
      atTop
      (𝓝 (∫ t : ℝ in Set.Ioi (0 : ℝ), f t)) := by
  let s : ℝ → Set ℝ := fun T : ℝ => Set.Ioc (0 : ℝ) T
  have hs_measurable :
      ∀ T : ℝ, MeasurableSet (s T) := by
    intro T
    exact measurableSet_Ioc
  have hs_monotone : Monotone s := by
    intro T U hTU
    intro x hx
    exact ⟨hx.1, le_trans hx.2 hTU⟩
  have hs_union :
      (⋃ T : ℝ, s T) = Set.Ioi (0 : ℝ) := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨T, hT⟩
      exact hT.1
    · intro hx
      exact Set.mem_iUnion.mpr ⟨x, ⟨hx, le_rfl⟩⟩
  have h_integrable_union :
      IntegrableOn f (⋃ T : ℝ, s T) := by
    exact hs_union.symm ▸ hf
  have h_tendsto :
      Tendsto
        (fun T : ℝ => ∫ t in s T, f t)
        atTop
        (𝓝 (∫ t in ⋃ T : ℝ, s T, f t)) :=
    tendsto_setIntegral_of_monotone
      hs_measurable hs_monotone h_integrable_union
  exact hs_union ▸ h_tendsto

/-- The moving lower-cutoff finite window is contained in the fixed window. -/
theorem Complex.Ioc_lower_cutoff_subset_Ioc_zero_right
    {ε T : ℝ}
    (hε : 0 ≤ ε) :
    Set.Ioc ε T ⊆ Set.Ioc (0 : ℝ) T := by
  intro t ht
  exact ⟨lt_of_le_of_lt hε ht.1, ht.2⟩

/-- The lower initial sliver is contained in the fixed window. -/
theorem Complex.Ioc_zero_lower_cutoff_subset_Ioc_zero_right
    {ε T : ℝ}
    (hεT : ε ≤ T) :
    Set.Ioc (0 : ℝ) ε ⊆ Set.Ioc (0 : ℝ) T := by
  intro t ht
  exact ⟨ht.1, le_trans ht.2 hεT⟩

/-- Integrability on the fixed finite window restricts to a moving
lower-cutoff window. -/
theorem Complex.integrableOn_Ioc_lower_cutoff_of_integrableOn_Ioc_zero_right
    {f : ℝ → ℂ}
    {ε T : ℝ}
    (hf : IntegrableOn f (Set.Ioc (0 : ℝ) T))
    (hε : 0 ≤ ε) :
    IntegrableOn f (Set.Ioc ε T) := by
  exact
    hf.mono_set
      (Complex.Ioc_lower_cutoff_subset_Ioc_zero_right hε)

/-- Integrability on the fixed finite window restricts to the lower initial
sliver. -/
theorem Complex.integrableOn_Ioc_zero_lower_cutoff_of_integrableOn_Ioc_zero_right
    {f : ℝ → ℂ}
    {ε T : ℝ}
    (hf : IntegrableOn f (Set.Ioc (0 : ℝ) T))
    (hεT : ε ≤ T) :
    IntegrableOn f (Set.Ioc (0 : ℝ) ε) := by
  exact
    hf.mono_set
      (Complex.Ioc_zero_lower_cutoff_subset_Ioc_zero_right hεT)

/-- The Lebesgue measure of the lower initial sliver `(0, ε]` tends to zero
as `ε → 0+`. -/
theorem Complex.tendsto_volume_Ioc_zero_lower_cutoff_nhdsWithin_zero_right :
    Tendsto
      (fun ε : ℝ => volume (Set.Ioc (0 : ℝ) ε))
      (𝓝[>] (0 : ℝ))
      (𝓝 (0 : ENNReal)) := by
  have hvolume :
      (fun ε : ℝ => volume (Set.Ioc (0 : ℝ) ε)) =
        fun ε : ℝ => ENNReal.ofReal ε := by
    funext ε
    calc
      volume (Set.Ioc (0 : ℝ) ε) =
          ENNReal.ofReal (ε - 0) :=
        Real.volume_Ioc
      _ = ENNReal.ofReal ε := by
        exact congrArg ENNReal.ofReal (sub_zero ε)
  exact hvolume.symm ▸
    ENNReal.ofReal_zero ▸
      ENNReal.continuous_ofReal.continuousWithinAt.tendsto

/-- The integral over the lower initial sliver tends to zero for a function
integrable on the fixed finite window. -/
theorem Complex.tendsto_integral_Ioc_zero_lower_cutoff_real_of_integrableOn_Ioc
    {f : ℝ → ℂ}
    {T : ℝ}
    (hf : IntegrableOn f (Set.Ioc (0 : ℝ) T))
    (hT : 0 < T) :
    Tendsto
      (fun ε : ℝ => ∫ t : ℝ in Set.Ioc (0 : ℝ) ε, f t)
      (𝓝[>] (0 : ℝ))
      (𝓝 (0 : ℂ)) := by
  have hmeasure :
      Tendsto
        (volume ∘ fun ε : ℝ => Set.Ioc (0 : ℝ) ε)
        (𝓝[>] (0 : ℝ))
        (𝓝 (0 : ENNReal)) :=
    Complex.tendsto_volume_Ioc_zero_lower_cutoff_nhdsWithin_zero_right
  let f₀ : ℝ → ℂ := (Set.Ioc (0 : ℝ) T).indicator f
  have hf₀ : Integrable f₀ :=
    hf.integrable_indicator measurableSet_Ioc
  have hzero :
      Tendsto
        (fun ε : ℝ => ∫ t : ℝ in Set.Ioc (0 : ℝ) ε, f₀ t)
        (𝓝[>] (0 : ℝ))
        (𝓝 (0 : ℂ)) :=
    hf₀.tendsto_setIntegral_nhds_zero hmeasure
  have heq_eventually :
      (fun ε : ℝ => ∫ t : ℝ in Set.Ioc (0 : ℝ) ε, f t) =ᶠ[𝓝[>] (0 : ℝ)]
        fun ε : ℝ => ∫ t : ℝ in Set.Ioc (0 : ℝ) ε, f₀ t := by
    have hε_lt_T_eventually :
        ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < T :=
      Filter.mem_of_superset
        (Filter.mem_inf_of_left (Iio_mem_nhds hT))
        (fun ε hε => hε)
    filter_upwards [hε_lt_T_eventually] with ε hεT
    exact
      setIntegral_congr_fun measurableSet_Ioc
        (fun t ht =>
          Eq.symm
            (Set.indicator_of_mem
              (show t ∈ Set.Ioc (0 : ℝ) T from ⟨ht.1, le_trans ht.2 hεT.le⟩)
              f))
  exact hzero.congr' heq_eventually.symm

/-- For `0 ≤ ε ≤ T`, the fixed window `(0,T]` is the disjoint union of
the initial sliver `(0,ε]` and the lower-cutoff window `(ε,T]`. -/
theorem Complex.integral_Ioc_zero_right_eq_integral_Ioc_zero_lower_cutoff_add_integral_Ioc_lower_cutoff
    {f : ℝ → ℂ}
    {ε T : ℝ}
    (hf : IntegrableOn f (Set.Ioc (0 : ℝ) T))
    (hε_nonneg : 0 ≤ ε)
    (hεT : ε ≤ T) :
    ∫ t : ℝ in Set.Ioc (0 : ℝ) T, f t =
      (∫ t : ℝ in Set.Ioc (0 : ℝ) ε, f t) +
        ∫ t : ℝ in Set.Ioc ε T, f t := by
  have hsliver :
      IntegrableOn f (Set.Ioc (0 : ℝ) ε) :=
    Complex.integrableOn_Ioc_zero_lower_cutoff_of_integrableOn_Ioc_zero_right
      hf hεT
  have hcutoff :
      IntegrableOn f (Set.Ioc ε T) :=
    Complex.integrableOn_Ioc_lower_cutoff_of_integrableOn_Ioc_zero_right
      hf hε_nonneg
  have hdisjoint :
      Disjoint (Set.Ioc (0 : ℝ) ε) (Set.Ioc ε T) := by
    exact Set.disjoint_left.mpr
      (fun t ht_sliver ht_cutoff =>
        not_lt_of_ge ht_sliver.2 ht_cutoff.1)
  have hunion :
      Set.Ioc (0 : ℝ) ε ∪ Set.Ioc ε T = Set.Ioc (0 : ℝ) T := by
    ext t
    constructor
    · intro ht
      rcases ht with ht | ht
      · exact ⟨ht.1, le_trans ht.2 hεT⟩
      · exact ⟨lt_of_le_of_lt hε_nonneg ht.1, ht.2⟩
    · intro ht
      by_cases htε : t ≤ ε
      · exact Or.inl ⟨ht.1, htε⟩
      · exact Or.inr ⟨lt_of_not_ge htε, ht.2⟩
  have hsplit :
      ∫ t : ℝ in Set.Ioc (0 : ℝ) ε ∪ Set.Ioc ε T, f t =
        (∫ t : ℝ in Set.Ioc (0 : ℝ) ε, f t) +
          ∫ t : ℝ in Set.Ioc ε T, f t :=
    setIntegral_union hdisjoint measurableSet_Ioc hsliver hcutoff
  exact Eq.trans (congrArg (fun s : Set ℝ => ∫ t : ℝ in s, f t) hunion.symm) hsplit

/-- The lower-cutoff window integral is the fixed-window integral minus the
initial sliver integral. -/
theorem Complex.integral_Ioc_lower_cutoff_eq_integral_Ioc_zero_right_sub_integral_Ioc_zero_lower_cutoff
    {f : ℝ → ℂ}
    {ε T : ℝ}
    (hf : IntegrableOn f (Set.Ioc (0 : ℝ) T))
    (hε_nonneg : 0 ≤ ε)
    (hεT : ε ≤ T) :
    ∫ t : ℝ in Set.Ioc ε T, f t =
      (∫ t : ℝ in Set.Ioc (0 : ℝ) T, f t) -
        ∫ t : ℝ in Set.Ioc (0 : ℝ) ε, f t := by
  have hsum :
      ∫ t : ℝ in Set.Ioc (0 : ℝ) T, f t =
        (∫ t : ℝ in Set.Ioc (0 : ℝ) ε, f t) +
          ∫ t : ℝ in Set.Ioc ε T, f t :=
    Complex.integral_Ioc_zero_right_eq_integral_Ioc_zero_lower_cutoff_add_integral_Ioc_lower_cutoff
      hf hε_nonneg hεT
  exact eq_sub_iff_add_eq'.mpr hsum.symm

/-- Deep measure-theory root: removing a lower initial sliver from a fixed
finite window preserves the integral in the one-sided lower-cutoff limit. -/
theorem Complex.tendsto_integral_Ioc_lower_cutoff_real_of_integrableOn_Ioc_root
    {f : ℝ → ℂ}
    {T : ℝ}
    (hf : IntegrableOn f (Set.Ioc (0 : ℝ) T))
    (hT : 0 < T) :
    Tendsto
      (fun ε : ℝ => ∫ t : ℝ in Set.Ioc ε T, f t)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ t : ℝ in Set.Ioc (0 : ℝ) T, f t)) := by
  have hsliver :
      Tendsto
        (fun ε : ℝ => ∫ t : ℝ in Set.Ioc (0 : ℝ) ε, f t)
        (𝓝[>] (0 : ℝ))
        (𝓝 (0 : ℂ)) :=
    Complex.tendsto_integral_Ioc_zero_lower_cutoff_real_of_integrableOn_Ioc hf
      hT
  have hsub :
      Tendsto
        (fun ε : ℝ =>
          (∫ t : ℝ in Set.Ioc (0 : ℝ) T, f t) -
            ∫ t : ℝ in Set.Ioc (0 : ℝ) ε, f t)
        (𝓝[>] (0 : ℝ))
        (𝓝 ((∫ t : ℝ in Set.Ioc (0 : ℝ) T, f t) - 0)) :=
    tendsto_const_nhds.sub hsliver
  have htarget :
      (∫ t : ℝ in Set.Ioc (0 : ℝ) T, f t) - 0 =
        ∫ t : ℝ in Set.Ioc (0 : ℝ) T, f t := by
    exact sub_zero _
  have heq_eventually :
      (fun ε : ℝ => ∫ t : ℝ in Set.Ioc ε T, f t) =ᶠ[𝓝[>] (0 : ℝ)]
        fun ε : ℝ =>
          (∫ t : ℝ in Set.Ioc (0 : ℝ) T, f t) -
            ∫ t : ℝ in Set.Ioc (0 : ℝ) ε, f t := by
    have hε_pos_eventually :
        ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε :=
      self_mem_nhdsWithin
    have hε_lt_T_eventually :
        ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < T :=
      Filter.mem_of_superset
        (Filter.mem_inf_of_left (Iio_mem_nhds hT))
        (fun ε hε => hε)
    filter_upwards [hε_pos_eventually, hε_lt_T_eventually] with ε hε_pos hεT_lt
    exact
      Complex.integral_Ioc_lower_cutoff_eq_integral_Ioc_zero_right_sub_integral_Ioc_zero_lower_cutoff
        hf hε_pos.le hεT_lt.le
  exact (htarget ▸ hsub).congr' heq_eventually.symm

/-- Finite-window lower-cutoff convergence for an integrable function on
`(0,T]`. -/
theorem Complex.tendsto_integral_Ioc_lower_cutoff_real_of_integrableOn_Ioc
    {f : ℝ → ℂ}
    {T : ℝ}
    (hf : IntegrableOn f (Set.Ioc (0 : ℝ) T))
    (hT : 0 < T) :
    Tendsto
      (fun ε : ℝ => ∫ t : ℝ in Set.Ioc ε T, f t)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ t : ℝ in Set.Ioc (0 : ℝ) T, f t)) := by
  exact
    Complex.tendsto_integral_Ioc_lower_cutoff_real_of_integrableOn_Ioc_root
      hf hT

/-- The positive half-line is the disjoint union of the lower finite window
and lower tail at `N`. -/
theorem Complex.Ioi_zero_eq_Ioc_zero_natCast_union_Ioi_natCast
    (N : ℕ) :
    Set.Ioi (0 : ℝ) =
      Set.Ioc (0 : ℝ) (N : ℝ) ∪ Set.Ioi (N : ℝ) := by
  ext t
  constructor
  · intro ht
    by_cases htN : t ≤ (N : ℝ)
    · exact Or.inl ⟨ht, htN⟩
    · exact Or.inr (lt_of_not_ge htN)
  · intro ht
    rcases ht with ht | ht
    · exact ht.1
    · exact lt_of_le_of_lt (Nat.cast_nonneg N) ht

/-- Lower vertical full integral splits over `(0,N]` and `(N,∞)`. -/
theorem Complex.finiteAbelPlana_log_lowerVerticalFullIntegral_eq_window_add_tail
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w =
      (∫ t : ℝ in Set.Ioc (0 : ℝ) (N : ℝ),
        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) +
        ∫ t : ℝ in Set.Ioi (N : ℝ),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t := by
  let L : ℝ → ℂ := fun t : ℝ =>
    Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t
  have hL :
      IntegrableOn L (Set.Ioi (0 : ℝ)) :=
    Complex.finiteAbelPlana_log_lowerVerticalIntegrand_integrableOn_Ioi hw
  have hwindow :
      IntegrableOn L (Set.Ioc (0 : ℝ) (N : ℝ)) :=
    hL.mono_set
      (by
        intro t ht
        exact ht.1)
  have htail :
      IntegrableOn L (Set.Ioi (N : ℝ)) :=
    hL.mono_set
      (by
        intro t ht
        exact lt_of_le_of_lt (Nat.cast_nonneg N) ht)
  have hdisjoint :
      Disjoint (Set.Ioc (0 : ℝ) (N : ℝ)) (Set.Ioi (N : ℝ)) := by
    exact Set.disjoint_left.mpr
      (fun t ht_window ht_tail =>
        not_lt_of_ge ht_window.2 ht_tail)
  have hunion :
      Set.Ioc (0 : ℝ) (N : ℝ) ∪ Set.Ioi (N : ℝ) =
        Set.Ioi (0 : ℝ) :=
    (Complex.Ioi_zero_eq_Ioc_zero_natCast_union_Ioi_natCast N).symm
  have hsplit :
      ∫ t : ℝ in
          Set.Ioc (0 : ℝ) (N : ℝ) ∪ Set.Ioi (N : ℝ), L t =
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (N : ℝ), L t) +
          ∫ t : ℝ in Set.Ioi (N : ℝ), L t :=
    setIntegral_union hdisjoint measurableSet_Ioi hwindow htail
  dsimp [Complex.finiteAbelPlanaLogLowerVerticalFullIntegral, L]
  exact Eq.trans (congrArg (fun s : Set ℝ =>
    ∫ t : ℝ in s, Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)
      hunion.symm) hsplit

/-- Lower vertical Abel-Plana improper-integral convergence on `(0,∞)`.

This is the concrete improper-integral theorem for the logarithmic jump kernel
appearing on the lower vertical side of the Abel-Plana contour.  It is the
standard convergence statement obtained from the Binet logarithmic-jump
majorant: the finite-height integrals over `(0,T]` converge to the integral
over the positive half-line. -/
theorem Complex.finiteAbelPlana_log_lowerVerticalIntegralUpTo_tendsto_unsplitFull_owner
    {w : ℂ}
    (hw : 0 < w.re) :
    Tendsto
      (fun T : ℝ =>
        Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)
      atTop
      (𝓝 (Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w)) := by
  exact
    Complex.tendsto_integral_Ioc_real_of_integrableOn_Ioi
      (Complex.finiteAbelPlana_log_lowerVerticalIntegrand_integrableOn_Ioi hw)

/-- The unsplit lower vertical improper integral is the Binet lower split.

The split is the ordinary additivity of the lower vertical improper integral
over `(0,∞) = (0,N] ∪ (N,∞)`, with the first part named
`binetAbelPlanaFiniteBoundaryCorrection` and the tail named
`binetAbelPlanaFiniteLowerContourTail`. -/
theorem Complex.finiteAbelPlana_log_lowerVerticalFullIntegral_eq_split_owner
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    :
    Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w =
      Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w := by
  exact
    Eq.trans
      (Complex.finiteAbelPlana_log_lowerVerticalFullIntegral_eq_window_add_tail
        hw N)
      (Complex.finiteAbelPlana_log_lowerVerticalSplit_unfold N w).symm

/-- Lower vertical finite-height convergence to the named Binet split. -/
theorem Complex.finiteAbelPlana_log_lowerVerticalIntegralUpTo_tendsto_full_owner
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    Tendsto
      (fun T : ℝ =>
        Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)
      atTop
      (𝓝 (Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w)) := by
  have hlimit :
      Tendsto
        (fun T : ℝ =>
          Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)
        atTop
        (𝓝 (Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w)) :=
    Complex.finiteAbelPlana_log_lowerVerticalIntegralUpTo_tendsto_unsplitFull_owner
      hw
  have hsplit :
      Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w =
        Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w :=
    Complex.finiteAbelPlana_log_lowerVerticalFullIntegral_eq_split_owner hw N
  exact hsplit ▸ hlimit

/-- Upper vertical Abel-Plana improper-integral convergence on `(0,∞)`.

This is the concrete improper-integral theorem for the endpoint logarithmic
jump kernel on the upper vertical side.  Its proof is the same monotone
set-integral convergence argument after using the finite upper residual
majorant for integrability. -/
theorem Complex.finiteAbelPlana_log_upperVerticalIntegralUpTo_tendsto_unsplitFull_owner
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    Tendsto
      (fun T : ℝ =>
        Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T)
      atTop
      (𝓝 (Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w)) := by
  exact
    Complex.tendsto_integral_Ioc_real_of_integrableOn_Ioi
      (Complex.finiteAbelPlana_log_upperVerticalIntegrand_integrableOn_Ioi
        hw N)

/-- The unsplit upper vertical integral is the named finite upper endpoint
residual. -/
theorem Complex.finiteAbelPlana_log_upperVerticalFullIntegral_eq_named_owner
    (N : ℕ)
    (w : ℂ) :
    Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w =
      Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w := by
  rfl

/-- Upper vertical finite-height convergence to the named upper residual. -/
theorem Complex.finiteAbelPlana_log_upperVerticalIntegralUpTo_tendsto_full_owner
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    Tendsto
      (fun T : ℝ =>
        Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T)
      atTop
      (𝓝 (Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w)) := by
  have hlimit :
      Tendsto
        (fun T : ℝ =>
          Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T)
        atTop
        (𝓝 (Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w)) :=
    Complex.finiteAbelPlana_log_upperVerticalIntegralUpTo_tendsto_unsplitFull_owner
      hw N
  have hnamed :
      Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w =
        Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w :=
    Complex.finiteAbelPlana_log_upperVerticalFullIntegral_eq_named_owner N w
  exact hnamed ▸ hlimit

/-- Finite-height Abel-Plana boundary pieces converge to the full named
Abel-Plana boundary expression, assuming the two vertical-side owner limits. -/
theorem Complex.finiteAbelPlana_log_boundaryNamedPiecesUpTo_tendsto_full_owner
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    Tendsto
      (fun T : ℝ =>
        Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T)
      atTop
      (𝓝 (Complex.finiteAbelPlanaLogBoundaryNamedPieces N w)) := by
  have hlower :
      Tendsto
        (fun T : ℝ =>
          Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)
        atTop
        (𝓝 (Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w)) :=
    Complex.finiteAbelPlana_log_lowerVerticalIntegralUpTo_tendsto_full_owner
      hw N
  have hupper :
      Tendsto
        (fun T : ℝ =>
          Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T)
        atTop
        (𝓝 (Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w)) :=
    Complex.finiteAbelPlana_log_upperVerticalIntegralUpTo_tendsto_full_owner
      hw N
  let base : ℂ :=
    let M : ℕ := N + 1
    (∫ x : ℝ in (0 : ℝ)..(M : ℝ),
        Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
      Complex.finiteAbelPlanaLogSummandHalfEndpoints N w
  have hbase :
      Tendsto
        (fun _T : ℝ => base)
        atTop
        (𝓝 base) :=
    tendsto_const_nhds
  have hsubLower :
      Tendsto
        (fun T : ℝ =>
          base - Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)
        atTop
        (𝓝 (base -
          Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w)) :=
    hbase.sub hlower
  have hsubBoth :
      Tendsto
        (fun T : ℝ =>
          base - Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
            Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T)
        atTop
        (𝓝 (base -
          Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w -
            Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w)) :=
    hsubLower.sub hupper
  dsimp [Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo,
    Complex.finiteAbelPlanaLogBoundaryNamedPieces, base] at hsubBoth ⊢
  exact hsubBoth

end

end LFunctions
end Boundary

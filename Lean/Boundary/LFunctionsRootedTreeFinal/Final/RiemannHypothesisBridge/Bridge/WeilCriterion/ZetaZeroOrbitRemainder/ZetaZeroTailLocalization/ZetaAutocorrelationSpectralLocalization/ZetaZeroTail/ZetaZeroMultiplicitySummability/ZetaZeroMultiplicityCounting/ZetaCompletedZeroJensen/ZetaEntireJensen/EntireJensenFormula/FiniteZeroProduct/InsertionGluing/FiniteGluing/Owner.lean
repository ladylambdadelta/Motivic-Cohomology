import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.FiniteZeroProduct.InsertionGluing.LocalDivision.Owner

/-!
# Normalized factor insertion and removable gluing

This owner layer was split from `FiniteZeroProduct.InsertionGluing.Owner` without changing public declaration names.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

created by dividing by `(1 - w / a)^m`. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteSupportFiniteRemovableQuotient_single_insert_removable_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (S : Finset (EntireFunctionZero F))
    (a : EntireFunctionZero F)
    (ha_not_mem : a ∉ S)
    (hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0)
    (ha0 : (a : ℂ) ≠ 0)
    (hlocal_a :
      ∃ g : ℂ → ℂ,
        AnalyticAt ℂ g (a : ℂ) ∧
        g (a : ℂ) ≠ 0 ∧
        ∀ᶠ w in 𝓝 (a : ℂ),
          F w =
            (w - (a : ℂ)) ^
                entireFunctionZeroMultiplicity F hF (a : ℂ) •
              g w)
    (hS :
      ∃ Q : ℂ → ℂ,
        (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
        (∀ w : ℂ,
          ‖w‖ ≤ ρ →
          F w =
            Q w *
              entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
                F hF S w) ∧
        Q 0 = F 0) :
    ∃ Q : ℂ → ℂ,
      (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
      (∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
              F hF (insert a S) w) ∧
      Q 0 = F 0 := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_singleZeroNormalizedFactor_removableQuotient_ownerRoot
      F hF ρ hρ S a ha_not_mem hS0 ha0 hlocal_a hS

/-- One-step finite divisor extraction.

Assuming a removable quotient has already been constructed for `S`, this
theorem extracts one further nonzero zero `a ∉ S`.  The proof is the local
single-zero removable quotient theorem applied to the current quotient times
the remaining product, using the local multiplicity factor of `F` at `a`. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteSupportFiniteRemovableQuotient_glue_finset_insert_step_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (S : Finset (EntireFunctionZero F))
    (a : EntireFunctionZero F)
    (ha_not_mem : a ∉ S)
    (hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0)
    (ha0 : (a : ℂ) ≠ 0)
    (hlocal_a :
      ∃ g : ℂ → ℂ,
        AnalyticAt ℂ g (a : ℂ) ∧
        g (a : ℂ) ≠ 0 ∧
        ∀ᶠ w in 𝓝 (a : ℂ),
          F w =
            (w - (a : ℂ)) ^
                entireFunctionZeroMultiplicity F hF (a : ℂ) •
              g w)
    (hS :
      ∃ Q : ℂ → ℂ,
        (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
        (∀ w : ℂ,
          ‖w‖ ≤ ρ →
          F w =
            Q w *
              entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
                F hF S w) ∧
        Q 0 = F 0) :
    ∃ Q : ℂ → ℂ,
      (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
      (∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
              F hF (insert a S) w) ∧
      Q 0 = F 0 := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteSupportFiniteRemovableQuotient_single_insert_removable_ownerRoot
      F hF ρ hρ S a ha_not_mem hS0 ha0 hlocal_a hS

/-- Finset-induction construction of the finite removable quotient.

The induction step removes one indexed nonzero zero using the local factor
supplied by `AnalyticAt.order_eq_nat_iff`; the remaining finite product is
analytic and nonzero at that center, so the single-zero removable value is the
local Taylor unit divided by the remaining leading coefficient. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteSupportFiniteRemovableQuotient_glue_finset_induction_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (S : Finset (EntireFunctionZero F))
    (hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0)
    (hlocal :
      ∀ z : EntireFunctionZero F,
        z ∈ S →
          ∃ g : ℂ → ℂ,
            AnalyticAt ℂ g (z : ℂ) ∧
            g (z : ℂ) ≠ 0 ∧
            ∀ᶠ w in 𝓝 (z : ℂ),
              F w =
                (w - (z : ℂ)) ^
                    entireFunctionZeroMultiplicity F hF (z : ℂ) •
                  g w) :
    ∃ Q : ℂ → ℂ,
      (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
      (∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
              F hF S w) ∧
      Q 0 = F 0 := by
  have hbase :
      (∀ z : EntireFunctionZero F, z ∈ (∅ : Finset (EntireFunctionZero F)) → (z : ℂ) ≠ 0) →
      (∀ z : EntireFunctionZero F,
        z ∈ (∅ : Finset (EntireFunctionZero F)) →
          ∃ g : ℂ → ℂ,
            AnalyticAt ℂ g (z : ℂ) ∧
            g (z : ℂ) ≠ 0 ∧
            ∀ᶠ w in 𝓝 (z : ℂ),
              F w =
                (w - (z : ℂ)) ^
                    entireFunctionZeroMultiplicity F hF (z : ℂ) •
                  g w) →
      ∃ Q : ℂ → ℂ,
        (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
        (∀ w : ℂ,
          ‖w‖ ≤ ρ →
          F w =
            Q w *
              entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
                F hF ∅ w) ∧
        Q 0 = F 0 := by
    intro _hS0 _hlocal
    exact
      entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteSupportFiniteRemovableQuotient_glue_finset_empty
        F hF ρ hρ
  have hstep :
      ∀ a S,
        a ∉ S →
        ((∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0) →
          (∀ z : EntireFunctionZero F,
            z ∈ S →
              ∃ g : ℂ → ℂ,
                AnalyticAt ℂ g (z : ℂ) ∧
                g (z : ℂ) ≠ 0 ∧
                ∀ᶠ w in 𝓝 (z : ℂ),
                  F w =
                    (w - (z : ℂ)) ^
                        entireFunctionZeroMultiplicity F hF (z : ℂ) •
                      g w) →
          ∃ Q : ℂ → ℂ,
            (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
            (∀ w : ℂ,
              ‖w‖ ≤ ρ →
              F w =
                Q w *
                  entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
                    F hF S w) ∧
            Q 0 = F 0) →
        (∀ z : EntireFunctionZero F, z ∈ insert a S → (z : ℂ) ≠ 0) →
        (∀ z : EntireFunctionZero F,
          z ∈ insert a S →
            ∃ g : ℂ → ℂ,
              AnalyticAt ℂ g (z : ℂ) ∧
              g (z : ℂ) ≠ 0 ∧
              ∀ᶠ w in 𝓝 (z : ℂ),
                F w =
                  (w - (z : ℂ)) ^
                      entireFunctionZeroMultiplicity F hF (z : ℂ) •
                    g w) →
        ∃ Q : ℂ → ℂ,
          (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
          (∀ w : ℂ,
            ‖w‖ ≤ ρ →
            F w =
              Q w *
                entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
                  F hF (insert a S) w) ∧
          Q 0 = F 0 := by
    intro a S ha_not_mem ih hS0 hlocal
    have hS0_tail :
        ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0 := by
      intro z hz
      exact hS0 z (Finset.mem_insert.2 (Or.inr hz))
    have ha0 : (a : ℂ) ≠ 0 :=
      hS0 a (Finset.mem_insert.2 (Or.inl rfl))
    have hlocal_a :
        ∃ g : ℂ → ℂ,
          AnalyticAt ℂ g (a : ℂ) ∧
          g (a : ℂ) ≠ 0 ∧
          ∀ᶠ w in 𝓝 (a : ℂ),
            F w =
              (w - (a : ℂ)) ^
                  entireFunctionZeroMultiplicity F hF (a : ℂ) •
                g w :=
      hlocal a (Finset.mem_insert.2 (Or.inl rfl))
    have hlocal_tail :
        ∀ z : EntireFunctionZero F,
          z ∈ S →
            ∃ g : ℂ → ℂ,
              AnalyticAt ℂ g (z : ℂ) ∧
              g (z : ℂ) ≠ 0 ∧
              ∀ᶠ w in 𝓝 (z : ℂ),
                F w =
                  (w - (z : ℂ)) ^
                      entireFunctionZeroMultiplicity F hF (z : ℂ) •
                    g w := by
      intro z hz
      exact hlocal z (Finset.mem_insert.2 (Or.inr hz))
    have hS :
        ∃ Q : ℂ → ℂ,
          (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
          (∀ w : ℂ,
            ‖w‖ ≤ ρ →
            F w =
              Q w *
                entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
                  F hF S w) ∧
          Q 0 = F 0 :=
      ih hS0_tail hlocal_tail
    exact
      entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteSupportFiniteRemovableQuotient_glue_finset_insert_step_ownerRoot
        F hF ρ hρ S a ha_not_mem hS0_tail ha0 hlocal_a hS
  exact Finset.induction_on S hbase hstep hS0 hlocal

/-- Parameterized finite removable quotient gluing across a finite set of
nonzero zeros.

This is the single owner-level removable-singularity construction used by both
the closed-disk support product and the radial-gap product.  The supplied
finite set determines the extracted divisor; any zeros not in `S` remain zeros
of the quotient rather than singularities. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteSupportFiniteRemovableQuotient_glue_finset_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (S : Finset (EntireFunctionZero F))
    (hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0)
    (hlocal :
      ∀ z : EntireFunctionZero F,
        z ∈ S →
          ∃ g : ℂ → ℂ,
            AnalyticAt ℂ g (z : ℂ) ∧
            g (z : ℂ) ≠ 0 ∧
            ∀ᶠ w in 𝓝 (z : ℂ),
              F w =
                (w - (z : ℂ)) ^
                    entireFunctionZeroMultiplicity F hF (z : ℂ) •
                  g w) :
    ∃ Q : ℂ → ℂ,
      (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
      (∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
              F hF S w) ∧
      Q 0 = F 0 := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteSupportFiniteRemovableQuotient_glue_finset_induction_ownerRoot
      F hF ρ hρ S hS0 hlocal

/-- Finset-level removable quotient gluing across the closed-disk support.

This is the closed-disk analogue of the radial support gluing root. It is the
correct owner for a quotient that is zero-free on `‖w‖ ≤ ρ`, because it removes
boundary zeros as well as strictly interior zeros. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteRemovableQuotient_glue_finset_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (S : Finset (EntireFunctionZero F))
    (hS :
      S =
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
          F hF hF0 ρ)
    (hlocal :
      ∀ z : EntireFunctionZero F,
        z ∈ S →
          ∃ g : ℂ → ℂ,
            AnalyticAt ℂ g (z : ℂ) ∧
            g (z : ℂ) ≠ 0 ∧
            ∀ᶠ w in 𝓝 (z : ℂ),
              F w =
                (w - (z : ℂ)) ^
                    entireFunctionZeroMultiplicity F hF (z : ℂ) •
                  g w) :
    ∃ Q : ℂ → ℂ,
      (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
      (∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
              F hF hF0 ρ w) ∧
      Q 0 = F 0 := by
  have hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0 := by
    intro z hz
    have hz_closed :
        z ∈
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
            F hF hF0 ρ :=
      Eq.subst (motive := fun T : Finset (EntireFunctionZero F) => z ∈ T)
        hS hz
    exact
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor_mem_ne_zero
        F hF hF0 ρ z hz_closed
  exact
    match
      entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteSupportFiniteRemovableQuotient_glue_finset_ownerRoot
        F hF ρ hρ S hS0 hlocal with
    | Exists.intro Q hQ_data =>
        match hQ_data with
        | And.intro hQ_an hQ_tail =>
            match hQ_tail with
            | And.intro hfactor hQ0 =>
                have hfactor_closed :
                    ∀ w : ℂ,
                      ‖w‖ ≤ ρ →
                      F w =
                        Q w *
                          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
                            F hF hF0 ρ w := by
                  intro w hwρ
                  have hprod :
                      entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
                          F hF S w =
                        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
                          F hF hF0 ρ w := by
                    calc
                      entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
                          F hF S w =
                        entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
                          F hF
                          (entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
                            F hF hF0 ρ) w := by
                        exact congrArg
                          (fun T : Finset (EntireFunctionZero F) =>
                            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
                              F hF T w)
                          hS
                      _ =
                        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
                          F hF hF0 ρ w := by
                        exact
                          (entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct_def
                            F hF hF0 ρ w).symm
                  calc
                    F w =
                        Q w *
                          entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
                            F hF S w :=
                      hfactor w hwρ
                    _ =
                        Q w *
                          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
                            F hF hF0 ρ w := by
                      exact congrArg (fun x : ℂ => Q w * x) hprod
                Exists.intro Q (And.intro hQ_an (And.intro hfactor_closed hQ0))

/-- Closed-disk removable quotient after extracting all nonzero zeros in
`‖w‖ ≤ ρ`. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteRemovableQuotient_extension_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ) :
    ∃ Q : ℂ → ℂ,
      (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
      (∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
              F hF hF0 ρ w) ∧
      Q 0 = F 0 := by
  let S : Finset (EntireFunctionZero F) :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
      F hF hF0 ρ
  have hS :
      S =
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
          F hF hF0 ρ :=
    rfl
  have hlocal :
      ∀ z : EntireFunctionZero F,
        z ∈ S →
          ∃ g : ℂ → ℂ,
            AnalyticAt ℂ g (z : ℂ) ∧
            g (z : ℂ) ≠ 0 ∧
            ∀ᶠ w in 𝓝 (z : ℂ),
              F w =
                (w - (z : ℂ)) ^
                    entireFunctionZeroMultiplicity F hF (z : ℂ) •
                  g w := by
    intro z hz
    exact
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteRemovableQuotient_localMultiplicityFactor_ownerRoot
        F hF hF0 ρ z hz
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteRemovableQuotient_glue_finset_ownerRoot
      F hF hF0 ρ hρ S hS hlocal

/-- Finset-level removable quotient gluing across the extracted Jensen support.

This is the owner lemma for the finite gluing step: every support point carries
the local multiplicity factor of `F`, and the support product carries the same
power there.  The resulting local quotients patch with the raw quotient on the
complement of the support and give one analytic quotient on the closed disk.
Cf. Titchmarsh, *The Theory of Functions*, §5. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteRemovableQuotient_glue_finset_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (S : Finset (EntireFunctionZero F))
    (hS :
      S =
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ)
    (hlocal :
      ∀ z : EntireFunctionZero F,
        z ∈ S →
          ∃ g : ℂ → ℂ,
            AnalyticAt ℂ g (z : ℂ) ∧
            g (z : ℂ) ≠ 0 ∧
            ∀ᶠ w in 𝓝 (z : ℂ),
              F w =
                (w - (z : ℂ)) ^
                    entireFunctionZeroMultiplicity F hF (z : ℂ) •
                  g w) :
    ∃ Q : ℂ → ℂ,
      (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
      (∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
              F hF hF0 ρ w) ∧
      Q 0 = F 0 := by
  have hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0 := by
    intro z hz
    have hz_radial :
        z ∈
          entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ :=
      Eq.subst (motive := fun T : Finset (EntireFunctionZero F) => z ∈ T)
        hS hz
    exact
      entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor_mem_ne_zero
        F hF hF0 ρ z hz_radial
  exact
    match
      entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteSupportFiniteRemovableQuotient_glue_finset_ownerRoot
        F hF ρ hρ S hS0 hlocal with
    | Exists.intro Q hQ_data =>
        match hQ_data with
        | And.intro hQ_an hQ_tail =>
            match hQ_tail with
            | And.intro hfactor hQ0 =>
                have hfactor_support :
                    ∀ w : ℂ,
                      ‖w‖ ≤ ρ →
                      F w =
                        Q w *
                          entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
                            F hF hF0 ρ w := by
                  intro w hwρ
                  have hprod :
                      entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
                          F hF S w =
                        entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
                          F hF hF0 ρ w := by
                    calc
                      entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
                          F hF S w =
                        entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
                          F hF
                          (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
                            F hF hF0 ρ) w := by
                        exact congrArg
                          (fun T : Finset (EntireFunctionZero F) =>
                            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
                              F hF T w)
                          hS
                      _ =
                        entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
                          F hF hF0 ρ w := by
                        exact
                          (entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct_def
                            F hF hF0 ρ w).symm
                  calc
                    F w =
                        Q w *
                          entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
                            F hF S w :=
                      hfactor w hwρ
                    _ =
                        Q w *
                          entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
                            F hF hF0 ρ w := by
                      exact congrArg (fun x : ℂ => Q w * x) hprod
                Exists.intro Q (And.intro hQ_an (And.intro hfactor_support hQ0))

/-- Canonical finite removable quotient after extracting exactly the Jensen
support divisor, stated as a thin wrapper over the Finset gluing owner lemma. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteRemovableQuotient_finiteExtension_from_glue_finset_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ) :
    ∃ Q : ℂ → ℂ,
      (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
      (∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
              F hF hF0 ρ w) ∧
      Q 0 = F 0 := by
  let S : Finset (EntireFunctionZero F) :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
      F hF hF0 ρ
  have hS :
      S =
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ :=
    rfl
  have hlocal :
      ∀ z : EntireFunctionZero F,
        z ∈ S →
          ∃ g : ℂ → ℂ,
            AnalyticAt ℂ g (z : ℂ) ∧
            g (z : ℂ) ≠ 0 ∧
            ∀ᶠ w in 𝓝 (z : ℂ),
              F w =
                (w - (z : ℂ)) ^
                    entireFunctionZeroMultiplicity F hF (z : ℂ) •
                  g w := by
    intro z hz
    exact
      entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteRemovableQuotient_localMultiplicityFactor_ownerRoot
        F hF hF0 ρ z hz
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteRemovableQuotient_glue_finset_ownerRoot
      F hF hF0 ρ hρ S hS hlocal

/-- Canonical finite removable quotient after extracting the Jensen support
divisor.

The construction removes the finite set of quotient singularities by the local
Taylor factors at the support zeros and agrees with the raw quotient away from
that finite support. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteRemovableQuotient_finiteExtension_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ) :
    ∃ Q : ℂ → ℂ,
      (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
      (∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
              F hF hF0 ρ w) ∧
      Q 0 = F 0 := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteRemovableQuotient_finiteExtension_from_glue_finset_ownerRoot
      F hF hF0 ρ hρ

/-- Away from the finite support, the raw quotient is the required local
quotient and reconstructs `F` after multiplication by the finite divisor
product. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteRemovableQuotient_puncturedAgreement_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    ∀ w : ℂ,
      w ∉
        (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ).image
          (fun z : EntireFunctionZero F => (z : ℂ)) →
      F w =
        entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient
            F hF hF0 ρ w *
          entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
            F hF hF0 ρ w := by
  intro w hw
  have hproduct_ne :
      entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
          F hF hF0 ρ w ≠ 0 := by
    have hproduct_expanded :
        entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
            F hF hF0 ρ w =
          ∏ z in
            entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
              F hF hF0 ρ,
            (1 - w / (z : ℂ)) ^ entireFunctionZeroMultiplicity F hF (z : ℂ) :=
      entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct_def
        F hF hF0 ρ w
    have hfinite_product_ne :
        (∏ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (1 - w / (z : ℂ)) ^ entireFunctionZeroMultiplicity F hF (z : ℂ)) ≠ 0 := by
      exact
        Finset.prod_ne_zero_iff.mpr
          (fun z hz =>
            pow_ne_zero
              (entireFunctionZeroMultiplicity F hF (z : ℂ))
              (fun hfactor =>
                hw
                  (Finset.mem_image.mpr
                    (Exists.intro z
                      (And.intro hz
                        ((entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct_factor_eq_zero_iff
                          F hF hF0 ρ z hz w).1 hfactor).symm)))))
    exact
      Eq.subst
        (motive := fun x : ℂ => x ≠ 0)
        hproduct_expanded.symm
        hfinite_product_ne
  exact
    (entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient_mul_product_of_product_ne_zero
      F hF hF0 ρ w hproduct_ne).symm

/-- Removable extension across the finite Jensen support.

The local Taylor factors at the support zeros cancel the corresponding powers
in the finite product, while the raw quotient gives the construction away from
the support.  The output is an entire quotient on the closed disk together with
the exact product factorization there. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteRemovableQuotient_extension_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ) :
    ∃ Q : ℂ → ℂ,
      (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
      (∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
              F hF hF0 ρ w) ∧
      Q 0 = F 0 := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteRemovableQuotient_finiteExtension_ownerRoot
      F hF hF0 ρ hρ


end
end LFunctions
end Boundary

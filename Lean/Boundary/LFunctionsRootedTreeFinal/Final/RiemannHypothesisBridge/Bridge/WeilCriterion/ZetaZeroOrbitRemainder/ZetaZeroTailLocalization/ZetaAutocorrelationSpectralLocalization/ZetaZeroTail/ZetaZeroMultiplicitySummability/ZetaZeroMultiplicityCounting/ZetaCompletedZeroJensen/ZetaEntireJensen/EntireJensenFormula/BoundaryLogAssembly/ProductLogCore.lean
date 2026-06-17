import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.BoundaryLogAssembly.ZeroFreeQuotient

/-!
# Product logarithm core for boundary-log assembly

This file owns the algebraic finite-product logarithm identity consumed by the
closed-support boundary product-log layer.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Pointwise logarithm of a finite product of nonzero complex factors.

This is the algebraic product-log identity used after the finite boundary
exception set has removed every vanishing boundary factor. -/
theorem finiteComplexProduct_log_norm_eq_sum_log_norm_of_nonzero
    {ι : Type*}
    (S : Finset ι)
    (f : ι → ℂ)
    (hf : ∀ i : ι, i ∈ S → f i ≠ 0) :
    Real.log ‖∏ i in S, f i‖ =
      ∑ i in S, Real.log ‖f i‖ := by
  letI : DecidableEq ι := Classical.decEq ι
  exact
    (Finset.induction_on
      (p := fun T : Finset ι =>
        (∀ i : ι, i ∈ T → f i ≠ 0) →
          Real.log ‖∏ i in T, f i‖ =
            ∑ i in T, Real.log ‖f i‖)
      S
      (fun _h_empty => by
        calc
          Real.log ‖∏ i in (∅ : Finset ι), f i‖ = Real.log ‖(1 : ℂ)‖ := by
            rfl
          _ = Real.log 1 := by
            exact congrArg Real.log (norm_one : ‖(1 : ℂ)‖ = 1)
          _ = 0 := by
            exact Real.log_one
          _ = ∑ i in (∅ : Finset ι), Real.log ‖f i‖ := by
            rfl)
      (fun a T ha_not_mem ih h_insert => by
        have ha_ne : f a ≠ 0 :=
          h_insert a (Finset.mem_insert.2 (Or.inl rfl))
        have hT_ne : ∀ i : ι, i ∈ T → f i ≠ 0 := by
          intro i hi
          exact h_insert i (Finset.mem_insert.2 (Or.inr hi))
        have hprod_ne : (∏ i in T, f i) ≠ 0 :=
          Finset.prod_ne_zero_iff.mpr hT_ne
        have hnorm_a_ne : ‖f a‖ ≠ 0 :=
          norm_ne_zero_iff.mpr ha_ne
        have hnorm_prod_ne : ‖∏ i in T, f i‖ ≠ 0 :=
          norm_ne_zero_iff.mpr hprod_ne
        calc
          Real.log ‖∏ i in insert a T, f i‖ =
              Real.log ‖f a * ∏ i in T, f i‖ := by
            exact congrArg (fun x : ℂ => Real.log ‖x‖)
              (Finset.prod_insert ha_not_mem)
          _ = Real.log (‖f a‖ * ‖∏ i in T, f i‖) := by
            exact congrArg Real.log (norm_mul (f a) (∏ i in T, f i))
          _ = Real.log ‖f a‖ + Real.log ‖∏ i in T, f i‖ := by
            exact Real.log_mul hnorm_a_ne hnorm_prod_ne
          _ = Real.log ‖f a‖ + ∑ i in T, Real.log ‖f i‖ := by
            exact congrArg (fun x : ℝ => Real.log ‖f a‖ + x) (ih hT_ne)
          _ = ∑ i in insert a T, Real.log ‖f i‖ := by
            have hsum_insert :
                (∑ i in insert a T, (fun j : ι => Real.log ‖f j‖) i) =
                  (fun j : ι => Real.log ‖f j‖) a +
                    ∑ i in T, (fun j : ι => Real.log ‖f j‖) i :=
              Finset.sum_insert
                (s := T)
                (a := a)
                (f := fun j : ι => Real.log ‖f j‖)
                ha_not_mem
            exact hsum_insert.symm)
      hf)

/-- Pull a fixed scalar into the second factor of a finite real weighted sum. -/
theorem finiteReal_sum_scalar_mul_weighted_integrals
    {ι : Type*}
    (S : Finset ι)
    (c : ℝ)
    (m I : ι → ℝ) :
    c * (∑ i in S, m i * I i) =
      ∑ i in S, m i * (c * I i) := by
  letI : DecidableEq ι := Classical.decEq ι
  exact
    Finset.induction_on
      (p := fun T : Finset ι =>
        c * (∑ i in T, m i * I i) =
          ∑ i in T, m i * (c * I i))
      S
      (by
        calc
          c * (∑ i in (∅ : Finset ι), m i * I i) = c * 0 := by
            exact congrArg (fun x : ℝ => c * x) Finset.sum_empty
          _ = 0 := mul_zero c
          _ = ∑ i in (∅ : Finset ι), m i * (c * I i) := by
            exact Finset.sum_empty.symm)
      (fun a T ha_not_mem ih => by
        have hterm :
            c * (m a * I a) = m a * (c * I a) := by
          calc
            c * (m a * I a) = (c * m a) * I a :=
              (mul_assoc c (m a) (I a)).symm
            _ = (m a * c) * I a := by
              exact congrArg (fun x : ℝ => x * I a) (mul_comm c (m a))
            _ = m a * (c * I a) :=
              mul_assoc (m a) c (I a)
        calc
          c * (∑ i in insert a T, m i * I i) =
              c * (m a * I a + ∑ i in T, m i * I i) := by
            exact congrArg (fun x : ℝ => c * x)
              (Finset.sum_insert
                (s := T)
                (a := a)
                (f := fun i : ι => m i * I i)
                ha_not_mem)
          _ = c * (m a * I a) + c * (∑ i in T, m i * I i) :=
            mul_add c (m a * I a) (∑ i in T, m i * I i)
          _ = m a * (c * I a) + ∑ i in T, m i * (c * I i) := by
            exact congrArg₂ HAdd.hAdd hterm ih
          _ = ∑ i in insert a T, m i * (c * I i) := by
            have hsum_insert :
                (∑ i in insert a T, (fun j : ι => m j * (c * I j)) i) =
                  (fun j : ι => m j * (c * I j)) a +
                    ∑ i in T, (fun j : ι => m j * (c * I j)) i :=
              Finset.sum_insert
                (s := T)
                (a := a)
                (f := fun j : ι => m j * (c * I j))
                ha_not_mem
            exact hsum_insert.symm)

end
end LFunctions
end Boundary

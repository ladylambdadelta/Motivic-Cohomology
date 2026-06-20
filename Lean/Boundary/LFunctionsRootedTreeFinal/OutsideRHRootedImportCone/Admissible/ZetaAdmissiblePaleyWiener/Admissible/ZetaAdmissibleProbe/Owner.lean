import Boundary.LFunctionsRootedTreeFinal.OutsideRHRootedImportCone.Admissible.ZetaAdmissibleAutocorrelation.Owner
import Boundary.LFunctionsRootedTreeFinal.OutsideRHRootedImportCone.Admissible.ZetaAdmissiblePaleyWiener.Admissible.ZetaAdmissibleProbe.Core.ZetaTransformCalculusBase.Owner

/-!
# Boundary admissible probe

This file names the concrete admissible probe built from the autocorrelation
of an admissible test function.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The raw Laplace pairing of an admissible probe with a finite exponential distribution. -/
def finiteExponentialLaplacePairing
    (S : Finset ℂ) (c : S → ℂ) (f : ZetaAdmissibleFunction) : ℂ :=
  ∑ z : S,
    Boundary.zetaLaplaceTransform f.toZetaTestFunction' (z : ℂ) * c z

/-- A finite exponential distribution is tomographically zero when it annihilates every
admissible probe under the raw Laplace pairing. -/
def finiteExponentialDistributionAnnihilatesAdmissibleProbes
    (S : Finset ℂ) (c : S → ℂ) : Prop :=
  ∀ f : ZetaAdmissibleFunction,
    finiteExponentialLaplacePairing S c f = 0

/-- The finite Laplace-sample vector of an admissible probe, kept local to the
admissible-probe owner file to avoid importing downstream Paley/cardinal APIs. -/
def admissibleProbeLaplaceFiniteSample
    (S : Finset ℂ) (f : ZetaAdmissibleFunction) : S → ℂ :=
  fun z : S =>
    Boundary.zetaLaplaceTransform f.toZetaTestFunction' (z : ℂ)

/-- The finite admissible Laplace-sample vector of a scalar multiple is the scalar multiple
of the finite admissible Laplace-sample vector. -/
theorem admissibleProbeLaplaceFiniteSample_smul
    (S : Finset ℂ) (c : ℂ) (f : ZetaAdmissibleFunction) :
    admissibleProbeLaplaceFiniteSample S (c • f) =
      c • admissibleProbeLaplaceFiniteSample S f := by
  ext z
  have hpoint :
      (c • f).toZetaTestFunction' =
        c • f.toZetaTestFunction' := by
    ext t
    calc
      (c • f).toZetaTestFunction' t =
          (c • f) t := by
        exact ZetaAdmissibleFunction.toZetaTestFunction'_apply (c • f) t
      _ = c * f t := by
        exact ZetaAdmissibleFunction.smul_apply c f t
      _ = c * f.toZetaTestFunction' t := by
        exact congrArg (fun u : ℂ => c * u)
          (ZetaAdmissibleFunction.toZetaTestFunction'_apply f t).symm
      _ = (c • f.toZetaTestFunction') t := by
        rfl
  calc
    Boundary.zetaLaplaceTransform (c • f).toZetaTestFunction' (z : ℂ) =
        Boundary.zetaLaplaceTransform (c • f.toZetaTestFunction') (z : ℂ) := by
      exact congrFun (Boundary.zetaLaplaceTransform_congr
        (fun t : ℝ =>
          congrArg (fun F : ZetaTestFunction => F t) hpoint)) (z : ℂ)
    _ = c * Boundary.zetaLaplaceTransform f.toZetaTestFunction' (z : ℂ) := by
      exact Boundary.zetaLaplaceTransform_smul c f.toZetaTestFunction' (z : ℂ)
    _ = (c • admissibleProbeLaplaceFiniteSample S f) z := by
      rfl

/-- The finite admissible Laplace-sample vector of a sum is the sum of the finite
admissible Laplace-sample vectors. -/
theorem admissibleProbeLaplaceFiniteSample_add
    (S : Finset ℂ) (f g : ZetaAdmissibleFunction) :
    admissibleProbeLaplaceFiniteSample S (f + g) =
      admissibleProbeLaplaceFiniteSample S f +
        admissibleProbeLaplaceFiniteSample S g := by
  ext z
  have hpoint :
      (f + g).toZetaTestFunction' =
        f.toZetaTestFunction' + g.toZetaTestFunction' := by
    ext t
    calc
      (f + g).toZetaTestFunction' t =
          (f + g) t := by
        exact ZetaAdmissibleFunction.toZetaTestFunction'_apply (f + g) t
      _ = f t + g t := by
        exact ZetaAdmissibleFunction.add_apply f g t
      _ = f.toZetaTestFunction' t + g.toZetaTestFunction' t := by
        exact congrArg₂ (fun u v : ℂ => u + v)
          (ZetaAdmissibleFunction.toZetaTestFunction'_apply f t).symm
          (ZetaAdmissibleFunction.toZetaTestFunction'_apply g t).symm
      _ = (f.toZetaTestFunction' + g.toZetaTestFunction') t := by
        rfl
  calc
    Boundary.zetaLaplaceTransform (f + g).toZetaTestFunction' (z : ℂ) =
        Boundary.zetaLaplaceTransform
          (f.toZetaTestFunction' + g.toZetaTestFunction') (z : ℂ) := by
      exact congrFun (Boundary.zetaLaplaceTransform_congr
        (fun t : ℝ =>
          congrArg (fun F : ZetaTestFunction => F t) hpoint)) (z : ℂ)
    _ =
        Boundary.zetaLaplaceTransform f.toZetaTestFunction' (z : ℂ) +
          Boundary.zetaLaplaceTransform g.toZetaTestFunction' (z : ℂ) := by
      exact Boundary.zetaLaplaceTransform_add
        f.toZetaTestFunction'
        g.toZetaTestFunction'
        (z : ℂ)
        (integrable_laplaceKernel_at f (z : ℂ))
        (integrable_laplaceKernel_at g (z : ℂ))
    _ =
        (admissibleProbeLaplaceFiniteSample S f +
          admissibleProbeLaplaceFiniteSample S g) z := by
      rfl

/-- The finite admissible Laplace-sample map as a bundled linear map. -/
def admissibleProbeLaplaceFiniteSampleLinearMap
    (S : Finset ℂ) :
    ZetaAdmissibleFunction →ₗ[ℂ] (S → ℂ) where
  toFun := admissibleProbeLaplaceFiniteSample S
  map_add' := fun f g =>
    admissibleProbeLaplaceFiniteSample_add S f g
  map_smul' := fun c f =>
    admissibleProbeLaplaceFiniteSample_smul S c f

/-- The finite dual functional attached to a finite exponential coefficient family. -/
def finiteExponentialCoefficientFunctional
    (S : Finset ℂ) (c : S → ℂ) : (S → ℂ) →ₗ[ℂ] ℂ where
  toFun := fun a : S → ℂ => ∑ z : S, a z * c z
  map_add' := by
    intro a b
    calc
      (∑ z : S, (a + b) z * c z) =
          ∑ z : S, (a z + b z) * c z := by
        rfl
      _ =
          ∑ z : S, (a z * c z + b z * c z) := by
        exact Finset.sum_congr rfl
          (fun z _hz =>
            add_mul (a z) (b z) (c z))
      _ =
          (∑ z : S, a z * c z) + ∑ z : S, b z * c z := by
        exact Finset.sum_add_distrib
  map_smul' := by
    intro r a
    calc
      (∑ z : S, (r • a) z * c z) =
          ∑ z : S, (r * a z) * c z := by
        rfl
      _ =
          ∑ z : S, r * (a z * c z) := by
        exact Finset.sum_congr rfl
          (fun z _hz =>
            mul_assoc r (a z) (c z))
      _ =
          r * ∑ z : S, a z * c z := by
        exact (Finset.mul_sum Finset.univ (fun z : S => a z * c z) r).symm

/-- The coordinate vector at a finite spectral sample. -/
def admissibleProbeLaplaceFiniteSampleCoordinate
    (S : Finset ℂ) (z₀ : S) : S → ℂ :=
  fun z : S => if z = z₀ then 1 else 0

/-- The coordinate vector is one at its own coordinate. -/
theorem admissibleProbeLaplaceFiniteSampleCoordinate_self
    (S : Finset ℂ) (z₀ : S) :
    admissibleProbeLaplaceFiniteSampleCoordinate S z₀ z₀ = 1 := by
  exact if_pos rfl

/-- The coordinate vector is zero away from its own coordinate. -/
theorem admissibleProbeLaplaceFiniteSampleCoordinate_of_ne
    (S : Finset ℂ) {z z₀ : S} (hz : z ≠ z₀) :
    admissibleProbeLaplaceFiniteSampleCoordinate S z₀ z = 0 := by
  exact if_neg hz

/-- Every finite sample vector is the coordinate expansion against the finite delta basis. -/
theorem admissibleProbeLaplaceFiniteSampleCoordinate_expansion
    (S : Finset ℂ) (a : S → ℂ) :
    (∑ z : S, a z • admissibleProbeLaplaceFiniteSampleCoordinate S z) = a := by
  funext w
  have hsingle :
      (∑ z : S, (a z • admissibleProbeLaplaceFiniteSampleCoordinate S z) w) =
        (a w • admissibleProbeLaplaceFiniteSampleCoordinate S w) w := by
    exact Finset.sum_eq_single w
      (fun z _hz hzw =>
        have hcoord :
            admissibleProbeLaplaceFiniteSampleCoordinate S z w = 0 :=
          admissibleProbeLaplaceFiniteSampleCoordinate_of_ne S hzw.symm
        calc
          (a z • admissibleProbeLaplaceFiniteSampleCoordinate S z) w =
              a z * admissibleProbeLaplaceFiniteSampleCoordinate S z w := by
            rfl
          _ = a z * 0 := by
            exact congrArg (fun u : ℂ => a z * u) hcoord
          _ = 0 := by
            exact mul_zero (a z))
      (fun hw => False.elim (hw (Finset.mem_univ w)))
  calc
    (∑ z : S, a z • admissibleProbeLaplaceFiniteSampleCoordinate S z) w =
        ∑ z : S, (a z • admissibleProbeLaplaceFiniteSampleCoordinate S z) w := by
      exact Finset.univ.sum_apply w
        (fun z : S => a z • admissibleProbeLaplaceFiniteSampleCoordinate S z)
    _ = (a w • admissibleProbeLaplaceFiniteSampleCoordinate S w) w := by
      exact hsingle
    _ = a w * admissibleProbeLaplaceFiniteSampleCoordinate S w w := by
      rfl
    _ = a w * 1 := by
      exact congrArg
        (fun u : ℂ => a w * u)
        (admissibleProbeLaplaceFiniteSampleCoordinate_self S w)
    _ = a w := by
      exact mul_one (a w)

/-- A linear functional on a finite sample space is represented by its coordinate
coefficients. -/
theorem admissibleProbeLaplaceFiniteSampleLinearFunctional_eq_coefficients
    (S : Finset ℂ) (Λ : (S → ℂ) →ₗ[ℂ] ℂ) :
    Λ =
      finiteExponentialCoefficientFunctional S
        (fun z : S => Λ (admissibleProbeLaplaceFiniteSampleCoordinate S z)) := by
  exact LinearMap.ext
    (fun a =>
      calc
        Λ a =
            Λ (∑ z : S, a z • admissibleProbeLaplaceFiniteSampleCoordinate S z) := by
          exact congrArg Λ
            (admissibleProbeLaplaceFiniteSampleCoordinate_expansion S a).symm
        _ =
            ∑ z : S, Λ (a z • admissibleProbeLaplaceFiniteSampleCoordinate S z) := by
          exact map_sum Λ
            (fun z : S => a z • admissibleProbeLaplaceFiniteSampleCoordinate S z)
            Finset.univ
        _ =
            ∑ z : S,
              a z * Λ (admissibleProbeLaplaceFiniteSampleCoordinate S z) := by
          exact Finset.sum_congr rfl
            (fun z _hz =>
              LinearMap.map_smul Λ (a z)
                (admissibleProbeLaplaceFiniteSampleCoordinate S z))
        _ =
            finiteExponentialCoefficientFunctional S
              (fun z : S => Λ (admissibleProbeLaplaceFiniteSampleCoordinate S z)) a := by
          rfl)

/-- Finite admissible Laplace-sample interpolation on a finite spectral sample set.

This is the owner surjectivity form of the finite Paley-Wiener interpolation input: every
finite spectral sample vector is realized as the Laplace-sample vector of an admissible
probe. -/
theorem admissibleProbeLaplaceFiniteSample_surjective_ownerAdmissibleProbe
    (S : Finset ℂ) :
    Function.Surjective (admissibleProbeLaplaceFiniteSample S) := by
  intro a
  match
      exists_zetaLaplaceTransformFiniteSample_eq_ownerPaleyWiener
        S a with
  | ⟨f, hf⟩ =>
      exact ⟨f, by
        ext z
        exact hf ⟨z, z.property⟩⟩

/-- The bundled finite admissible Laplace-sample linear map has full range. -/
theorem admissibleProbeLaplaceFiniteSample_range_top_ownerAdmissibleProbe
    (S : Finset ℂ) :
    LinearMap.range (admissibleProbeLaplaceFiniteSampleLinearMap S) = ⊤ := by
  exact LinearMap.range_eq_top.mpr
    (admissibleProbeLaplaceFiniteSample_surjective_ownerAdmissibleProbe S)

/-- Every finite sample vector belongs to the finite admissible Laplace-sample range. -/
theorem admissibleProbeLaplaceFiniteSample_mem_range_ownerAdmissibleProbe
    (S : Finset ℂ) (a : S → ℂ) :
    a ∈ Set.range (admissibleProbeLaplaceFiniteSample S) := by
  exact admissibleProbeLaplaceFiniteSample_surjective_ownerAdmissibleProbe S a

/-- Finite-dimensional restricted-Laplace separation by admissible probes.

This is the exact finite tomography engine: if a linear functional on the finite spectral
sample space vanishes on every admissible Laplace sample vector, then it is the zero
functional. This is the finite-dimensional linear-algebra consequence of finite
Laplace-sample surjectivity; coefficient tomography and Paley-Wiener cardinal APIs are
downstream consequences. -/
theorem admissibleProbeLaplaceFiniteSample_dual_separating_ownerAdmissibleProbe
    (S : Finset ℂ)
    (Λ : (S → ℂ) →ₗ[ℂ] ℂ)
    (hΛ :
      ∀ f : ZetaAdmissibleFunction,
        Λ (admissibleProbeLaplaceFiniteSample S f) = 0) :
    Λ = 0 := by
  exact LinearMap.ext
    (fun a =>
      match admissibleProbeLaplaceFiniteSample_surjective_ownerAdmissibleProbe S a with
      | ⟨f, hf⟩ =>
          Eq.subst
            (motive := fun v : S → ℂ => Λ v = 0)
            hf
            (hΛ f))

/-- Finite exponential-distribution tomography by admissible probes.

This is the coefficient form of finite Laplace-sample dual separation: if every admissible
probe has zero raw Laplace pairing with a finite exponential distribution, then all
coefficients of that distribution vanish. -/
theorem finiteExponentialDistribution_coefficients_eq_zero_of_tomography_ownerAdmissibleProbe
    (S : Finset ℂ) (c : S → ℂ)
    (hc : finiteExponentialDistributionAnnihilatesAdmissibleProbes S c) :
    ∀ z : S, c z = 0 := by
  intro z₀
  let Λ : (S → ℂ) →ₗ[ℂ] ℂ :=
    finiteExponentialCoefficientFunctional S c
  have hΛvanish :
      ∀ f : ZetaAdmissibleFunction,
        Λ (admissibleProbeLaplaceFiniteSample S f) = 0 := by
    intro f
    show finiteExponentialLaplacePairing S c f = 0
    exact hc f
  have hΛzero : Λ = 0 :=
    admissibleProbeLaplaceFiniteSample_dual_separating_ownerAdmissibleProbe
      S Λ hΛvanish
  let e : S → ℂ := admissibleProbeLaplaceFiniteSampleCoordinate S z₀
  have hΛe_zero : Λ e = 0 := by
    exact congrArg (fun M : (S → ℂ) →ₗ[ℂ] ℂ => M e) hΛzero
  have hsingle :
      Λ e = e z₀ * c z₀ := by
    show
      (∑ z : S, e z * c z) = e z₀ * c z₀
    exact Finset.sum_eq_single z₀
      (fun z _hz hz =>
        have heq : e z = 0 := by
          exact admissibleProbeLaplaceFiniteSampleCoordinate_of_ne S hz
        calc
          e z * c z = 0 * c z := by
            exact congrArg (fun w : ℂ => w * c z) heq
          _ = 0 := by
            exact zero_mul (c z))
      (fun hz₀ => False.elim (hz₀ (Finset.mem_univ z₀)))
  have hcoord :
      e z₀ * c z₀ = c z₀ := by
    calc
      e z₀ * c z₀ = 1 * c z₀ := by
        exact congrArg (fun w : ℂ => w * c z₀)
          (admissibleProbeLaplaceFiniteSampleCoordinate_self S z₀)
      _ = c z₀ := by
        exact one_mul (c z₀)
  exact hcoord.symm.trans (hsingle.symm.trans hΛe_zero)

/-- Admissible probes are separating generators for finite exponential distributions.

This is the existence form of finite exponential-distribution tomography: a nonzero finite
coefficient family has some admissible probe whose raw Laplace pairing with that finite
exponential distribution is nonzero. -/
theorem admissibleProbes_separate_finiteExponentialDistributions
    (S : Finset ℂ) (c : S → ℂ)
    (hc : ∃ z : S, c z ≠ 0) :
    ∃ f : ZetaAdmissibleFunction,
      finiteExponentialLaplacePairing S c f ≠ 0 := by
  match hc with
  | ⟨z₀, hz₀⟩ =>
      let e : S → ℂ := admissibleProbeLaplaceFiniteSampleCoordinate S z₀
      match admissibleProbeLaplaceFiniteSample_surjective_ownerAdmissibleProbe S e with
      | ⟨f, hf⟩ =>
          have hpair :
              finiteExponentialLaplacePairing S c f = e z₀ * c z₀ := by
            show
              (∑ z : S,
                Boundary.zetaLaplaceTransform f.toZetaTestFunction' (z : ℂ) * c z) =
                e z₀ * c z₀
            exact Finset.sum_eq_single z₀
              (fun z _hz hzz₀ =>
                have hsample :
                    Boundary.zetaLaplaceTransform f.toZetaTestFunction' (z : ℂ) =
                      e z := by
                  exact congrArg (fun a : S → ℂ => a z) hf
                have heq : e z = 0 :=
                  admissibleProbeLaplaceFiniteSampleCoordinate_of_ne S hzz₀
                calc
                  Boundary.zetaLaplaceTransform f.toZetaTestFunction' (z : ℂ) * c z =
                      e z * c z := by
                    exact congrArg (fun u : ℂ => u * c z) hsample
                  _ = 0 * c z := by
                    exact congrArg (fun u : ℂ => u * c z) heq
                  _ = 0 := by
                    exact zero_mul (c z))
              (fun hz₀mem => False.elim (hz₀mem (Finset.mem_univ z₀)))
          have hcoord :
              e z₀ * c z₀ = c z₀ := by
            calc
              e z₀ * c z₀ = 1 * c z₀ := by
                exact congrArg (fun u : ℂ => u * c z₀)
                  (admissibleProbeLaplaceFiniteSampleCoordinate_self S z₀)
              _ = c z₀ := by
                exact one_mul (c z₀)
          exact ⟨f, fun hzero =>
            hz₀ (hcoord.symm.trans (hpair.symm.trans hzero))⟩

/-- Admissible probes detect nonzero finite exponential distributions.

This is the separation owner theorem in existence form: a nonzero finite coefficient
family has some admissible probe whose Laplace pairing with the associated finite
exponential distribution is nonzero. It is upstream of cardinal probes and finite
Laplace-sample surjectivity. -/
theorem exists_admissibleProbe_detects_nonzero_finiteExponentialDistribution
    (S : Finset ℂ) (c : S → ℂ)
    (hc : ∃ z : S, c z ≠ 0) :
    ∃ f : ZetaAdmissibleFunction,
      (∑ z : S,
        Boundary.zetaLaplaceTransform f.toZetaTestFunction' (z : ℂ) * c z) ≠ 0 := by
  exact admissibleProbes_separate_finiteExponentialDistributions S c hc

/-- If a finite exponential distribution annihilates every admissible probe, then every
coefficient is zero. -/
theorem finiteExponentialDistribution_coefficients_eq_zero_of_annihilates_admissibleProbes
    (S : Finset ℂ) (c : S → ℂ)
    (hc : finiteExponentialDistributionAnnihilatesAdmissibleProbes S c) :
    ∀ z : S, c z = 0 := by
  exact
    finiteExponentialDistribution_coefficients_eq_zero_of_tomography_ownerAdmissibleProbe
      S c hc

/-- Coefficientwise zero finite exponential distributions annihilate every admissible
probe. -/
theorem finiteExponentialDistribution_annihilates_admissibleProbes_of_coefficients_eq_zero
    (S : Finset ℂ) (c : S → ℂ)
    (hc : ∀ z : S, c z = 0) :
    finiteExponentialDistributionAnnihilatesAdmissibleProbes S c := by
  intro f
  show finiteExponentialLaplacePairing S c f = 0
  exact Finset.sum_eq_zero
    (fun z _hz =>
      calc
        Boundary.zetaLaplaceTransform f.toZetaTestFunction' (z : ℂ) * c z =
            Boundary.zetaLaplaceTransform f.toZetaTestFunction' (z : ℂ) * 0 := by
          exact congrArg
            (fun w : ℂ =>
              Boundary.zetaLaplaceTransform f.toZetaTestFunction' (z : ℂ) * w)
            (hc z)
        _ = 0 := by
          exact mul_zero
            (Boundary.zetaLaplaceTransform f.toZetaTestFunction' (z : ℂ)))

/-- Admissible probe tomography for finite exponential distributions: annihilating every
admissible probe is equivalent to coefficientwise zero. -/
theorem finiteExponentialDistribution_annihilates_admissibleProbes_iff_coefficients_eq_zero
    (S : Finset ℂ) (c : S → ℂ) :
    finiteExponentialDistributionAnnihilatesAdmissibleProbes S c ↔
      ∀ z : S, c z = 0 :=
  ⟨finiteExponentialDistribution_coefficients_eq_zero_of_annihilates_admissibleProbes S c,
    finiteExponentialDistribution_annihilates_admissibleProbes_of_coefficients_eq_zero S c⟩

/-- Finite exponential-sample separation by admissible probes.

If a finite exponential distribution pairs to zero with the Laplace transforms of every
admissible probe, then all of its coefficients vanish. This is the admissible-probe owner
form of the Paley-Wiener uniqueness input; finite cardinal probes and finite-dimensional
surjectivity are downstream consequences. -/
theorem zetaLaplaceTransformFiniteExponentialSamples_separated_by_admissibleProbes_ownerAdmissibleProbe
    (S : Finset ℂ) (c : S → ℂ)
    (hc :
      ∀ f : ZetaAdmissibleFunction,
        (∑ z : S,
          Boundary.zetaLaplaceTransform f.toZetaTestFunction' (z : ℂ) * c z) = 0) :
    ∀ z : S, c z = 0 := by
  exact
    finiteExponentialDistribution_coefficients_eq_zero_of_annihilates_admissibleProbes
      S c hc

/-- The admissible separating probe attached to an admissible function. -/
def separatingProbe (f : ZetaAdmissibleFunction) : ZetaTestFunction :=
  (autocorrelation f).toZetaTestFunction'

/-- The separating probe is pointwise the autocorrelation. -/
theorem separatingProbe_apply (f : ZetaAdmissibleFunction) (x : ℝ) :
    separatingProbe f x = f x * star (f x) := by
  rfl

/-- The separating probe is the admissible autocorrelation. -/
theorem separatingProbe_eq (f : ZetaAdmissibleFunction) :
    separatingProbe f = (autocorrelation f).toZetaTestFunction' := by
  rfl

/-- The admissible probe is the pointwise conjugate square. -/
theorem separatingProbe_conjSq (f : ZetaAdmissibleFunction) (x : ℝ) :
    separatingProbe f x = f x * star (f x) := by
  rfl

/-- The admissible probe is the pointwise conjugate square. -/
theorem separatingProbe_pointwise (f : ZetaAdmissibleFunction) (x : ℝ) :
    separatingProbe f x = f x * star (f x) := by
  rfl

/-- The admissible probe is pointwise the conjugate square. -/
theorem separatingProbe_square (f : ZetaAdmissibleFunction) (x : ℝ) :
    separatingProbe f x = f x * star (f x) := by
  rfl

/-- The admissible probe is the autocorrelation square. -/
theorem admissible_probe_square (f : ZetaAdmissibleFunction) (x : ℝ) :
    separatingProbe f x = f x * star (f x) := by
  rfl

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

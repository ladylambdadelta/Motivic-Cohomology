import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaBoundaryPL.DampedFamily.BoundedPL

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Filter Topology
local notation "π" => Real.pi

/-- The cosine damping kernel is entire as a function of the strip variable. -/
theorem verticalStripCosineDampingKernel_differentiable
    (a b : ℝ)
    (hab : a < b) :
    Differentiable ℂ (verticalStripCosineDampingKernel a b) := by
  have hwidth_ne : ((verticalStripWidth a b : ℝ) : ℂ) ≠ 0 := by
    exact
      Complex.ofReal_ne_zero.mpr
        (verticalStripWidth_ne_zero hab)
  have haffine :
      Differentiable ℂ
        (fun z : ℂ =>
          ((π : ℝ) : ℂ) *
            (z - ((verticalStripCenter a b : ℝ) : ℂ)) /
              ((verticalStripWidth a b : ℝ) : ℂ)) := by
    exact
      ((differentiable_id.sub_const
          (((verticalStripCenter a b : ℝ) : ℂ))).const_mul
        (((π : ℝ) : ℂ))).div_const
        (((verticalStripWidth a b : ℝ) : ℂ))
  exact
    Complex.differentiable_cos.comp haffine

/-- The subcritical cosine barrier kernel is entire as a function of the strip
variable. -/
theorem verticalStripSubcriticalCosineBarrierKernel_differentiable
    (a b d : ℝ) :
    Differentiable ℂ
      (verticalStripSubcriticalCosineBarrierKernel a b d) := by
  have haffine :
      Differentiable ℂ
        (fun z : ℂ =>
          ((d : ℝ) : ℂ) *
            (z - ((verticalStripCenter a b : ℝ) : ℂ))) := by
    exact
      (differentiable_id.sub_const
        ((verticalStripCenter a b : ℝ) : ℂ)).const_mul
        ((d : ℝ) : ℂ)
  exact
    Complex.differentiable_cos.comp haffine

/-- The exponential cosine damping factor is entire on the strip variable. -/
theorem verticalStripCosineDampingFactor_differentiable
    (a b ε : ℝ)
    (hab : a < b) :
    Differentiable ℂ
      (fun z : ℂ =>
        Complex.exp
          (-((ε : ℝ) : ℂ) *
            verticalStripCosineDampingKernel a b z)) := by
  have hkernel :
      Differentiable ℂ (verticalStripCosineDampingKernel a b) :=
    verticalStripCosineDampingKernel_differentiable a b hab
  have hexponent :
      Differentiable ℂ
        (fun z : ℂ =>
          -((ε : ℝ) : ℂ) *
            verticalStripCosineDampingKernel a b z) :=
    hkernel.const_mul (-((ε : ℝ) : ℂ))
  exact
    Complex.differentiable_exp.comp hexponent

/-- The subcritical exponential cosine damping factor is entire on the strip
variable. -/
theorem verticalStripSubcriticalCosineDampingFactor_differentiable
    (a b d ε : ℝ) :
    Differentiable ℂ
      (fun z : ℂ =>
        Complex.exp
          (-((ε : ℝ) : ℂ) *
            verticalStripSubcriticalCosineBarrierKernel a b d z)) := by
  have hkernel :
      Differentiable ℂ (verticalStripSubcriticalCosineBarrierKernel a b d) :=
    verticalStripSubcriticalCosineBarrierKernel_differentiable a b d
  have hexponent :
      Differentiable ℂ
        (fun z : ℂ =>
          -((ε : ℝ) : ℂ) *
            verticalStripSubcriticalCosineBarrierKernel a b d z) :=
    hkernel.const_mul (-((ε : ℝ) : ℂ))
  exact
    Complex.differentiable_exp.comp hexponent

/-- The exponential cosine damping factor is holomorphic on the closed strip
in the `DiffContOnCl` sense used by the Phragmen-Lindelöf API. -/
theorem verticalStripCosineDampingFactor_diffContOnCl
    (a b ε : ℝ)
    (hab : a < b) :
    DiffContOnCl ℂ
      (fun z : ℂ =>
        Complex.exp
          (-((ε : ℝ) : ℂ) *
            verticalStripCosineDampingKernel a b z))
      (Complex.re ⁻¹' Set.Ioo a b) :=
  (verticalStripCosineDampingFactor_differentiable a b ε hab).diffContOnCl

/-- The subcritical exponential cosine damping factor is holomorphic on the
closed strip in the `DiffContOnCl` sense used by the Phragmen-Lindelöf API. -/
theorem verticalStripSubcriticalCosineDampingFactor_diffContOnCl
    (a b d ε : ℝ) :
    DiffContOnCl ℂ
      (fun z : ℂ =>
        Complex.exp
          (-((ε : ℝ) : ℂ) *
            verticalStripSubcriticalCosineBarrierKernel a b d z))
      (Complex.re ⁻¹' Set.Ioo a b) :=
  (verticalStripSubcriticalCosineDampingFactor_differentiable
    a b d ε).diffContOnCl

/-- Multiplying by the cosine damping factor preserves strip holomorphy. -/
theorem verticalStripCosineDampedFamily_diffContOnCl
    (f : ℂ → ℂ)
    (a b ε : ℝ)
    (hab : a < b)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b)) :
    DiffContOnCl ℂ (verticalStripCosineDampedFamily f a b ε)
      (Complex.re ⁻¹' Set.Ioo a b) := by
  let g : ℂ → ℂ :=
    fun z : ℂ =>
      Complex.exp
        (-((ε : ℝ) : ℂ) *
          verticalStripCosineDampingKernel a b z)
  have hg : DiffContOnCl ℂ g (Complex.re ⁻¹' Set.Ioo a b) :=
    verticalStripCosineDampingFactor_diffContOnCl a b ε hab
  have hproduct : DiffContOnCl ℂ (fun z : ℂ => g z • f z)
      (Complex.re ⁻¹' Set.Ioo a b) :=
    hg.smul hhol
  have hfunctions :
      (fun z : ℂ => g z • f z) =
        verticalStripCosineDampedFamily f a b ε :=
    funext
      fun z : ℂ =>
        calc
          g z • f z = g z * f z := by
            exact smul_eq_mul (g z) (f z)
          _ = f z * g z := mul_comm (g z) (f z)
          _ = verticalStripCosineDampedFamily f a b ε z := rfl
  exact
    Eq.subst
      (motive := fun F : ℂ → ℂ =>
        DiffContOnCl ℂ F (Complex.re ⁻¹' Set.Ioo a b))
      hfunctions
      hproduct

/-- Multiplying by the subcritical cosine damping factor preserves strip
holomorphy. -/
theorem verticalStripSubcriticalCosineDampedFamily_diffContOnCl
    (f : ℂ → ℂ)
    (a b d ε : ℝ)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b)) :
    DiffContOnCl ℂ (verticalStripSubcriticalCosineDampedFamily f a b d ε)
      (Complex.re ⁻¹' Set.Ioo a b) := by
  let g : ℂ → ℂ :=
    fun z : ℂ =>
      Complex.exp
        (-((ε : ℝ) : ℂ) *
          verticalStripSubcriticalCosineBarrierKernel a b d z)
  have hg : DiffContOnCl ℂ g (Complex.re ⁻¹' Set.Ioo a b) :=
    verticalStripSubcriticalCosineDampingFactor_diffContOnCl a b d ε
  have hproduct : DiffContOnCl ℂ (fun z : ℂ => g z • f z)
      (Complex.re ⁻¹' Set.Ioo a b) :=
    hg.smul hhol
  have hfunctions :
      (fun z : ℂ => g z • f z) =
        verticalStripSubcriticalCosineDampedFamily f a b d ε :=
    funext
      fun z : ℂ =>
        calc
          g z • f z = g z * f z := by
            exact smul_eq_mul (g z) (f z)
          _ = f z * g z := mul_comm (g z) (f z)
          _ = verticalStripSubcriticalCosineDampedFamily f a b d ε z := rfl
  exact
    Eq.subst
      (motive := fun F : ℂ → ℂ =>
        DiffContOnCl ℂ F (Complex.re ⁻¹' Set.Ioo a b))
      hfunctions
      hproduct

/-- The tilted upper-tail damping base is entire in the strip variable. -/
theorem verticalStripUpperTailDampingBase_differentiable
    (a b : ℝ) :
    Differentiable ℂ (verticalStripUpperTailDampingBase a b) := by
  let K : ℂ := (((|a| + |b| + 2 : ℝ) : ℂ))
  let c : ℂ := ((verticalStripCenter a b : ℝ) : ℂ)
  have haffine :
      Differentiable ℂ
        (fun z : ℂ => K - Complex.I * (z - c)) := by
    exact
      differentiable_const.sub
        ((differentiable_id.sub_const c).const_mul Complex.I)
  have hfunctions :
      (fun z : ℂ => K - Complex.I * (z - c)) =
        verticalStripUpperTailDampingBase a b :=
    funext
      fun z : ℂ =>
        calc
          K - Complex.I * (z - c) =
              (((|a| + |b| + 2 : ℝ) : ℂ)) -
                Complex.I * (z - ((verticalStripCenter a b : ℝ) : ℂ)) := rfl
          _ = verticalStripUpperTailDampingBase a b z := rfl
  exact
    Eq.subst
      (motive := fun F : ℂ → ℂ => Differentiable ℂ F)
      hfunctions
      haffine

/-- The tilted upper-tail damping kernel is entire. -/
theorem verticalStripUpperTailDampingKernel_differentiable
    (a b : ℝ) :
    Differentiable ℂ (verticalStripUpperTailDampingKernel a b) := by
  have hbase :
      Differentiable ℂ (verticalStripUpperTailDampingBase a b) :=
    verticalStripUpperTailDampingBase_differentiable a b
  have hexponent :
      Differentiable ℂ
        (fun z : ℂ =>
          ((verticalStripUpperTailDampingScale a b : ℝ) : ℂ) *
            verticalStripUpperTailDampingBase a b z) :=
    hbase.const_mul
      (((verticalStripUpperTailDampingScale a b : ℝ) : ℂ))
  exact
    Complex.differentiable_exp.comp hexponent

/-- The upper-tail polynomial normalizing kernel is entire. -/
theorem verticalStripUpperTailPolynomialNormalizerKernel_differentiable
    (a b : ℝ)
    (N : ℕ) :
    Differentiable ℂ
      (verticalStripUpperTailPolynomialNormalizerKernel a b N) := by
  have hbase :
      Differentiable ℂ (verticalStripUpperTailDampingBase a b) :=
    verticalStripUpperTailDampingBase_differentiable a b
  have hpow :
      Differentiable ℂ
        (fun z : ℂ => (verticalStripUpperTailDampingBase a b z) ^ N) :=
    hbase.pow N
  have hfunctions :
      (fun z : ℂ => (verticalStripUpperTailDampingBase a b z) ^ N) =
        verticalStripUpperTailPolynomialNormalizerKernel a b N :=
    funext
      fun z : ℂ =>
        calc
          (verticalStripUpperTailDampingBase a b z) ^ N =
              verticalStripUpperTailPolynomialNormalizerKernel a b N z := rfl
  exact
    Eq.subst
      (motive := fun F : ℂ → ℂ => Differentiable ℂ F)
      hfunctions
      hpow

/-- The upper-tail polynomial normalizing factor is entire. -/
theorem verticalStripUpperTailPolynomialNormalizingFactor_differentiable
    (a b C : ℝ)
    (N : ℕ) :
    Differentiable ℂ
      (fun z : ℂ =>
        Complex.exp
          (-((C : ℝ) : ℂ) *
            verticalStripUpperTailPolynomialNormalizerKernel a b N z)) := by
  have hkernel :
      Differentiable ℂ
        (verticalStripUpperTailPolynomialNormalizerKernel a b N) :=
    verticalStripUpperTailPolynomialNormalizerKernel_differentiable a b N
  have hexponent :
      Differentiable ℂ
        (fun z : ℂ =>
          -((C : ℝ) : ℂ) *
            verticalStripUpperTailPolynomialNormalizerKernel a b N z) :=
    hkernel.const_mul (-((C : ℝ) : ℂ))
  exact
    Complex.differentiable_exp.comp hexponent

/-- The upper-tail polynomial normalizing factor is holomorphic on the closed
strip in the `DiffContOnCl` sense used by the Phragmen-Lindelöf API. -/
theorem verticalStripUpperTailPolynomialNormalizingFactor_diffContOnCl
    (a b C : ℝ)
    (N : ℕ) :
    DiffContOnCl ℂ
      (fun z : ℂ =>
        Complex.exp
          (-((C : ℝ) : ℂ) *
            verticalStripUpperTailPolynomialNormalizerKernel a b N z))
      (Complex.re ⁻¹' Set.Ioo a b) :=
  (verticalStripUpperTailPolynomialNormalizingFactor_differentiable
    a b C N).diffContOnCl

/-- Multiplying by the polynomial normalizing factor preserves strip
holomorphy. -/
theorem verticalStripUpperTailPolynomialNormalizedFamily_diffContOnCl
    (f : ℂ → ℂ)
    (a b C : ℝ)
    (N : ℕ)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b)) :
    DiffContOnCl ℂ
      (verticalStripUpperTailPolynomialNormalizedFamily f a b C N)
      (Complex.re ⁻¹' Set.Ioo a b) := by
  let g : ℂ → ℂ :=
    fun z : ℂ =>
      Complex.exp
        (-((C : ℝ) : ℂ) *
          verticalStripUpperTailPolynomialNormalizerKernel a b N z)
  have hg : DiffContOnCl ℂ g (Complex.re ⁻¹' Set.Ioo a b) :=
    verticalStripUpperTailPolynomialNormalizingFactor_diffContOnCl a b C N
  have hproduct : DiffContOnCl ℂ (fun z : ℂ => g z • f z)
      (Complex.re ⁻¹' Set.Ioo a b) :=
    hg.smul hhol
  have hfunctions :
      (fun z : ℂ => g z • f z) =
        verticalStripUpperTailPolynomialNormalizedFamily f a b C N :=
    funext
      fun z : ℂ =>
        calc
          g z • f z = g z * f z := by
            exact smul_eq_mul (g z) (f z)
          _ = f z * g z := mul_comm (g z) (f z)
          _ =
            verticalStripUpperTailPolynomialNormalizedFamily f a b C N z := rfl
  exact
    Eq.subst
      (motive := fun F : ℂ → ℂ =>
        DiffContOnCl ℂ F (Complex.re ⁻¹' Set.Ioo a b))
      hfunctions
      hproduct

/-- Multiplying the polynomial normalized family by the boundary constant
preserves strip holomorphy. -/
theorem verticalStripUpperTailPolynomialBoundedFactor_diffContOnCl
    (f : ℂ → ℂ)
    (a b A C : ℝ)
    (N : ℕ)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b)) :
    DiffContOnCl ℂ
      (verticalStripUpperTailPolynomialBoundedFactor f a b A C N)
      (Complex.re ⁻¹' Set.Ioo a b) := by
  have hnormalized :
      DiffContOnCl ℂ
        (verticalStripUpperTailPolynomialNormalizedFamily f a b C N)
        (Complex.re ⁻¹' Set.Ioo a b) :=
    verticalStripUpperTailPolynomialNormalizedFamily_diffContOnCl
      f a b C N hhol
  let κ : ℂ := ((A⁻¹ : ℝ) : ℂ)
  have hscaled :
      DiffContOnCl ℂ
        (fun z : ℂ =>
          κ • verticalStripUpperTailPolynomialNormalizedFamily f a b C N z)
        (Complex.re ⁻¹' Set.Ioo a b) :=
    hnormalized.const_smul κ
  have hfunctions :
      (fun z : ℂ =>
          κ • verticalStripUpperTailPolynomialNormalizedFamily f a b C N z) =
        verticalStripUpperTailPolynomialBoundedFactor f a b A C N :=
    funext
      fun z : ℂ =>
        calc
          κ • verticalStripUpperTailPolynomialNormalizedFamily f a b C N z =
              κ * verticalStripUpperTailPolynomialNormalizedFamily f a b C N z := by
            exact
              smul_eq_mul
                κ
                (verticalStripUpperTailPolynomialNormalizedFamily f a b C N z)
          _ =
              ((A⁻¹ : ℝ) : ℂ) *
                verticalStripUpperTailPolynomialNormalizedFamily f a b C N z := rfl
          _ =
              verticalStripUpperTailPolynomialBoundedFactor f a b A C N z := rfl
  exact
    Eq.subst
      (motive := fun F : ℂ → ℂ =>
        DiffContOnCl ℂ F (Complex.re ⁻¹' Set.Ioo a b))
      hfunctions
      hscaled

/-- The degree-dependent upper-tail polynomial base is entire. -/
theorem verticalStripUpperTailDegreePolynomialBase_differentiable
    (a b : ℝ)
    (N : ℕ) :
    Differentiable ℂ (verticalStripUpperTailDegreePolynomialBase a b N) := by
  let K : ℂ :=
    ((4 * ((N + 1 : ℕ) : ℝ) * (|a| + |b| + 2) + 1 : ℝ) : ℂ)
  let c : ℂ := ((verticalStripCenter a b : ℝ) : ℂ)
  have haffine :
      Differentiable ℂ
        (fun z : ℂ => K - Complex.I * (z - c)) := by
    exact
      differentiable_const.sub
        ((differentiable_id.sub_const c).const_mul Complex.I)
  have hfunctions :
      (fun z : ℂ => K - Complex.I * (z - c)) =
        verticalStripUpperTailDegreePolynomialBase a b N :=
    funext
      fun z : ℂ =>
        calc
          K - Complex.I * (z - c) =
              ((4 * ((N + 1 : ℕ) : ℝ) * (|a| + |b| + 2) + 1 : ℝ) : ℂ) -
                Complex.I * (z - ((verticalStripCenter a b : ℝ) : ℂ)) := rfl
          _ = verticalStripUpperTailDegreePolynomialBase a b N z := rfl
  exact
    Eq.subst
      (motive := fun F : ℂ → ℂ => Differentiable ℂ F)
      hfunctions
      haffine

/-- The degree-dependent upper-tail polynomial kernel is entire. -/
theorem verticalStripUpperTailDegreePolynomialKernel_differentiable
    (a b : ℝ)
    (N : ℕ) :
    Differentiable ℂ (verticalStripUpperTailDegreePolynomialKernel a b N) := by
  have hbase :
      Differentiable ℂ (verticalStripUpperTailDegreePolynomialBase a b N) :=
    verticalStripUpperTailDegreePolynomialBase_differentiable a b N
  have hpow :
      Differentiable ℂ
        (fun z : ℂ => (verticalStripUpperTailDegreePolynomialBase a b N z) ^ N) :=
    hbase.pow N
  have hfunctions :
      (fun z : ℂ => (verticalStripUpperTailDegreePolynomialBase a b N z) ^ N) =
        verticalStripUpperTailDegreePolynomialKernel a b N :=
    funext
      fun z : ℂ =>
        calc
          (verticalStripUpperTailDegreePolynomialBase a b N z) ^ N =
              verticalStripUpperTailDegreePolynomialKernel a b N z := rfl
  exact
    Eq.subst
      (motive := fun F : ℂ → ℂ => Differentiable ℂ F)
      hfunctions
      hpow

/-- The degree-dependent bounded polynomial normalized factor is holomorphic on
the strip. -/
theorem verticalStripUpperTailDegreePolynomialBoundedFactor_diffContOnCl
    (f : ℂ → ℂ)
    (a b A C : ℝ)
    (N : ℕ)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b)) :
    DiffContOnCl ℂ
      (verticalStripUpperTailDegreePolynomialBoundedFactor f a b A C N)
      (Complex.re ⁻¹' Set.Ioo a b) := by
  have hkernel :
      Differentiable ℂ (verticalStripUpperTailDegreePolynomialKernel a b N) :=
    verticalStripUpperTailDegreePolynomialKernel_differentiable a b N
  have hfactor_diff :
      Differentiable ℂ
        (fun z : ℂ =>
          Complex.exp
            (-((C : ℝ) : ℂ) *
              verticalStripUpperTailDegreePolynomialKernel a b N z)) := by
    have hexponent :
        Differentiable ℂ
          (fun z : ℂ =>
            -((C : ℝ) : ℂ) *
              verticalStripUpperTailDegreePolynomialKernel a b N z) :=
      hkernel.const_mul (-((C : ℝ) : ℂ))
    exact Complex.differentiable_exp.comp hexponent
  have hfactor :
      DiffContOnCl ℂ
        (fun z : ℂ =>
          Complex.exp
            (-((C : ℝ) : ℂ) *
              verticalStripUpperTailDegreePolynomialKernel a b N z))
        (Complex.re ⁻¹' Set.Ioo a b) :=
    hfactor_diff.diffContOnCl
  let g : ℂ → ℂ :=
    fun z : ℂ =>
      Complex.exp
        (-((C : ℝ) : ℂ) *
          verticalStripUpperTailDegreePolynomialKernel a b N z)
  have hproduct :
      DiffContOnCl ℂ
        (fun z : ℂ => ((A⁻¹ : ℝ) : ℂ) • (g z • f z))
        (Complex.re ⁻¹' Set.Ioo a b) :=
    (hfactor.smul hhol).const_smul (((A⁻¹ : ℝ) : ℂ))
  have hfunctions :
      (fun z : ℂ => ((A⁻¹ : ℝ) : ℂ) • (g z • f z)) =
        verticalStripUpperTailDegreePolynomialBoundedFactor f a b A C N :=
    funext
      fun z : ℂ =>
        calc
          ((A⁻¹ : ℝ) : ℂ) • (g z • f z) =
              ((A⁻¹ : ℝ) : ℂ) *
                (g z * f z) := by
            exact congrArg
              (fun y : ℂ => ((A⁻¹ : ℝ) : ℂ) * y)
              (smul_eq_mul (g z) (f z))
          _ =
              ((A⁻¹ : ℝ) : ℂ) *
                (f z * g z) := by
            exact congrArg
              (fun y : ℂ => ((A⁻¹ : ℝ) : ℂ) * y)
              (mul_comm (g z) (f z))
          _ =
              verticalStripUpperTailDegreePolynomialBoundedFactor
                f a b A C N z := rfl
  exact
    Eq.subst
      (motive := fun F : ℂ → ℂ =>
        DiffContOnCl ℂ F (Complex.re ⁻¹' Set.Ioo a b))
      hfunctions
      hproduct

/-- The mixed subcritical-cosine/degree-polynomial bounded normalized factor is
holomorphic on the strip whenever the original function is. -/
theorem verticalStripSubcriticalCosineDegreePolynomialBoundedFactor_diffContOnCl
    (f : ℂ → ℂ)
    (a b d A C ε : ℝ)
    (N : ℕ)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b)) :
    DiffContOnCl ℂ
      (verticalStripSubcriticalCosineDegreePolynomialBoundedFactor
        f a b d A C ε N)
      (Complex.re ⁻¹' Set.Ioo a b) := by
  have hdamped :
      DiffContOnCl ℂ
        (verticalStripSubcriticalCosineDampedFamily f a b d ε)
        (Complex.re ⁻¹' Set.Ioo a b) :=
    verticalStripSubcriticalCosineDampedFamily_diffContOnCl
      f a b d ε hhol
  exact
    verticalStripUpperTailDegreePolynomialBoundedFactor_diffContOnCl
      (verticalStripSubcriticalCosineDampedFamily f a b d ε)
      a b A C N hdamped

/-- The upper-tail damping factor is entire in the strip variable. -/
theorem verticalStripUpperTailDampingFactor_differentiable
    (a b ε : ℝ) :
    Differentiable ℂ
      (fun z : ℂ =>
        Complex.exp
          (-((ε : ℝ) : ℂ) *
            verticalStripUpperTailDampingKernel a b z)) := by
  have hkernel :
      Differentiable ℂ (verticalStripUpperTailDampingKernel a b) :=
    verticalStripUpperTailDampingKernel_differentiable a b
  have hexponent :
      Differentiable ℂ
        (fun z : ℂ =>
          -((ε : ℝ) : ℂ) *
            verticalStripUpperTailDampingKernel a b z) :=
    hkernel.const_mul (-((ε : ℝ) : ℂ))
  exact
    Complex.differentiable_exp.comp hexponent

/-- The upper-tail damping factor is holomorphic on the closed strip in the
`DiffContOnCl` sense used by the Phragmen-Lindelöf API. -/
theorem verticalStripUpperTailDampingFactor_diffContOnCl
    (a b ε : ℝ) :
    DiffContOnCl ℂ
      (fun z : ℂ =>
        Complex.exp
          (-((ε : ℝ) : ℂ) *
            verticalStripUpperTailDampingKernel a b z))
      (Complex.re ⁻¹' Set.Ioo a b) :=
  (verticalStripUpperTailDampingFactor_differentiable a b ε).diffContOnCl

/-- Multiplying by the upper-tail damping factor preserves strip holomorphy. -/
theorem verticalStripUpperTailDampedFamily_diffContOnCl
    (f : ℂ → ℂ)
    (a b ε : ℝ)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b)) :
    DiffContOnCl ℂ (verticalStripUpperTailDampedFamily f a b ε)
      (Complex.re ⁻¹' Set.Ioo a b) := by
  let g : ℂ → ℂ :=
    fun z : ℂ =>
      Complex.exp
        (-((ε : ℝ) : ℂ) *
          verticalStripUpperTailDampingKernel a b z)
  have hg : DiffContOnCl ℂ g (Complex.re ⁻¹' Set.Ioo a b) :=
    verticalStripUpperTailDampingFactor_diffContOnCl a b ε
  have hproduct : DiffContOnCl ℂ (fun z : ℂ => g z • f z)
      (Complex.re ⁻¹' Set.Ioo a b) :=
    hg.smul hhol
  have hfunctions :
      (fun z : ℂ => g z • f z) =
        verticalStripUpperTailDampedFamily f a b ε :=
    funext
      fun z : ℂ =>
        calc
          g z • f z = g z * f z := by
            exact smul_eq_mul (g z) (f z)
          _ = f z * g z := mul_comm (g z) (f z)
          _ = verticalStripUpperTailDampedFamily f a b ε z := rfl
  exact
    Eq.subst
      (motive := fun F : ℂ → ℂ =>
        DiffContOnCl ℂ F (Complex.re ⁻¹' Set.Ioo a b))
      hfunctions
      hproduct

/-- The real part of the affine strip coordinate lies in the standard cosine
window. -/
theorem verticalStripCosineDampingAffine_re_mem_standardWindow_ownerGap
    (a b : ℝ)
    (hab : a < b)
    (z : ℂ)
    (hz : z ∈ Complex.re ⁻¹' Set.Ioo a b) :
    (π * ((z - ((verticalStripCenter a b : ℝ) : ℂ)) /
        ((verticalStripWidth a b : ℝ) : ℂ)).re) ∈
      Set.Icc (-(π / 2)) (π / 2) := by
  let u : ℝ :=
    ((z - ((verticalStripCenter a b : ℝ) : ℂ)) /
      ((verticalStripWidth a b : ℝ) : ℂ)).re
  have hwidth_pos : 0 < verticalStripWidth a b :=
    verticalStripWidth_pos hab
  have hpi_nonneg : 0 ≤ π :=
    le_of_lt Real.pi_pos
  have hz_left : a < z.re :=
    hz.1
  have hz_right : z.re < b :=
    hz.2
  have hcenter_left :
      a - verticalStripCenter a b ≤ z.re - verticalStripCenter a b :=
    sub_le_sub_right (le_of_lt hz_left) (verticalStripCenter a b)
  have hcenter_right :
      z.re - verticalStripCenter a b ≤ b - verticalStripCenter a b :=
    sub_le_sub_right (le_of_lt hz_right) (verticalStripCenter a b)
  have hleft_endpoint :
      a - verticalStripCenter a b =
        -(verticalStripWidth a b / 2) := by
    calc
      a - verticalStripCenter a b = (a - b) / 2 :=
        leftEndpoint_sub_verticalStripCenter a b
      _ = (-(b - a)) / 2 := by
        exact congrArg (fun x : ℝ => x / 2) (neg_sub b a).symm
      _ = -((b - a) / 2) := by
        exact neg_div (b - a) 2
      _ = -(verticalStripWidth a b / 2) := rfl
  have hright_endpoint :
      b - verticalStripCenter a b =
        verticalStripWidth a b / 2 :=
    rightEndpoint_sub_verticalStripCenter a b
  have hcoord :
      u =
        (z.re - verticalStripCenter a b) / verticalStripWidth a b := by
    calc
      u =
          ((z - ((verticalStripCenter a b : ℝ) : ℂ)) /
            ((verticalStripWidth a b : ℝ) : ℂ)).re := rfl
      _ =
          (z - ((verticalStripCenter a b : ℝ) : ℂ)).re /
            verticalStripWidth a b := by
        exact
          Complex.div_ofReal_re
            (z - ((verticalStripCenter a b : ℝ) : ℂ))
            (verticalStripWidth a b)
      _ = (z.re - verticalStripCenter a b) / verticalStripWidth a b := by
        exact
          congrArg (fun x : ℝ => x / verticalStripWidth a b)
            (Complex.sub_re z ((verticalStripCenter a b : ℝ) : ℂ) ▸
              congrArg (fun x : ℝ => z.re - x)
                (Complex.ofReal_re (verticalStripCenter a b)))
  have hu_lower : -(1 / 2 : ℝ) ≤ u := by
    have hmul_lower :
        -(1 / 2 : ℝ) * verticalStripWidth a b ≤
          z.re - verticalStripCenter a b := by
      have hleft_transport :
          -(verticalStripWidth a b / 2) ≤
            z.re - verticalStripCenter a b :=
        Eq.subst
          (motive := fun x : ℝ =>
            x ≤ z.re - verticalStripCenter a b)
          hleft_endpoint
          hcenter_left
      have hmul_eq :
          -(1 / 2 : ℝ) * verticalStripWidth a b =
            -(verticalStripWidth a b / 2) := by
        calc
          -(1 / 2 : ℝ) * verticalStripWidth a b =
              -((1 / 2 : ℝ) * verticalStripWidth a b) := by
            exact neg_mul (1 / 2 : ℝ) (verticalStripWidth a b)
          _ = -(verticalStripWidth a b * (1 / 2 : ℝ)) := by
            exact congrArg Neg.neg (mul_comm (1 / 2 : ℝ) (verticalStripWidth a b))
          _ = -(verticalStripWidth a b / 2) := by
            exact congrArg Neg.neg (mul_one_div (verticalStripWidth a b) 2)
      exact
        Eq.subst
          (motive := fun x : ℝ =>
            x ≤ z.re - verticalStripCenter a b)
          hmul_eq.symm
          hleft_transport
    have hdiv_lower :
        -(1 / 2 : ℝ) ≤
          (z.re - verticalStripCenter a b) / verticalStripWidth a b :=
      (le_div_iff₀ hwidth_pos).mpr hmul_lower
    exact
      Eq.subst
        (motive := fun x : ℝ => -(1 / 2 : ℝ) ≤ x)
        hcoord.symm
        hdiv_lower
  have hu_upper : u ≤ (1 / 2 : ℝ) := by
    have hmul_upper :
        z.re - verticalStripCenter a b ≤
          (1 / 2 : ℝ) * verticalStripWidth a b := by
      have hright_transport :
          z.re - verticalStripCenter a b ≤
            verticalStripWidth a b / 2 :=
        Eq.subst
          (motive := fun x : ℝ =>
            z.re - verticalStripCenter a b ≤ x)
          hright_endpoint
          hcenter_right
      have hmul_eq :
          (1 / 2 : ℝ) * verticalStripWidth a b =
            verticalStripWidth a b / 2 := by
        calc
          (1 / 2 : ℝ) * verticalStripWidth a b =
              verticalStripWidth a b * (1 / 2 : ℝ) := by
            exact mul_comm (1 / 2 : ℝ) (verticalStripWidth a b)
          _ = verticalStripWidth a b / 2 := by
            exact mul_one_div (verticalStripWidth a b) 2
      exact
        Eq.subst
          (motive := fun x : ℝ =>
            z.re - verticalStripCenter a b ≤ x)
          hmul_eq.symm
          hright_transport
    have hdiv_upper :
        (z.re - verticalStripCenter a b) / verticalStripWidth a b ≤
          (1 / 2 : ℝ) :=
      (div_le_iff₀ hwidth_pos).mpr hmul_upper
    exact
      Eq.subst
        (motive := fun x : ℝ => x ≤ (1 / 2 : ℝ))
        hcoord.symm
        hdiv_upper
  constructor
  · calc
      -(π / 2) = π * (-(1 / 2 : ℝ)) := by
        calc
          -(π / 2) = -(π * (1 / 2 : ℝ)) := by
            exact congrArg Neg.neg (div_eq_mul_one_div π 2)
          _ = π * (-(1 / 2 : ℝ)) := by
            exact (mul_neg π (1 / 2 : ℝ)).symm
      _ ≤ π * u :=
        mul_le_mul_of_nonneg_left hu_lower hpi_nonneg
  · calc
      π * u ≤ π * (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hu_upper hpi_nonneg
      _ = π / 2 := by
        exact (div_eq_mul_one_div π 2).symm

/-- Complex cosine has real part `cos x * cosh y` in coordinates. -/
theorem complexCos_re_eq_realCos_mul_realCosh
    (w : ℂ) :
    (Complex.cos w).re = Real.cos w.re * Real.cosh w.im := by
  let A : ℂ := Complex.cos w.re * Complex.cosh w.im
  let B : ℂ := Complex.sin w.re * Complex.sinh w.im * Complex.I
  have hA_re : A.re = Real.cos w.re * Real.cosh w.im := by
    have hmul :
        (Complex.cos w.re * Complex.cosh w.im).re =
          (Complex.cos w.re).re * (Complex.cosh w.im).re -
            (Complex.cos w.re).im * (Complex.cosh w.im).im :=
      Complex.mul_re (Complex.cos w.re) (Complex.cosh w.im)
    have hreal :
        (Complex.cos w.re).re * (Complex.cosh w.im).re -
            (Complex.cos w.re).im * (Complex.cosh w.im).im =
          Real.cos w.re * Real.cosh w.im - 0 * 0 :=
      Eq.trans
        (congrArg₂
          (fun x y : ℝ =>
            x * y - (Complex.cos w.re).im * (Complex.cosh w.im).im)
          (Complex.cos_ofReal_re w.re)
          (Complex.cosh_ofReal_re w.im))
        (congrArg₂
          (fun x y : ℝ => Real.cos w.re * Real.cosh w.im - x * y)
          (Complex.cos_ofReal_im w.re)
          (Complex.cosh_ofReal_im w.im))
    have him :
        Real.cos w.re * Real.cosh w.im - 0 * 0 =
          Real.cos w.re * Real.cosh w.im := by
      calc
        Real.cos w.re * Real.cosh w.im - 0 * 0 =
            Real.cos w.re * Real.cosh w.im - 0 := by
          exact congrArg (fun x : ℝ => Real.cos w.re * Real.cosh w.im - x) (zero_mul 0)
        _ = Real.cos w.re * Real.cosh w.im := by
          exact sub_zero (Real.cos w.re * Real.cosh w.im)
    exact Eq.trans hmul (Eq.trans hreal him)
  have hB_re : B.re = 0 := by
    let C : ℂ := Complex.sin w.re * Complex.sinh w.im
    have hC_im : C.im = 0 := by
      have hmul :
          (Complex.sin w.re * Complex.sinh w.im).im =
            (Complex.sin w.re).re * (Complex.sinh w.im).im +
              (Complex.sin w.re).im * (Complex.sinh w.im).re :=
        Complex.mul_im (Complex.sin w.re) (Complex.sinh w.im)
      have him :
          (Complex.sin w.re).re * (Complex.sinh w.im).im +
              (Complex.sin w.re).im * (Complex.sinh w.im).re =
            (Complex.sin w.re).re * 0 + 0 * (Complex.sinh w.im).re :=
        congrArg₂
          (fun x y : ℝ => (Complex.sin w.re).re * x + y * (Complex.sinh w.im).re)
          (Complex.sinh_ofReal_im w.im)
          (Complex.sin_ofReal_im w.re)
      have hzero :
          (Complex.sin w.re).re * 0 + 0 * (Complex.sinh w.im).re = 0 := by
        calc
          (Complex.sin w.re).re * 0 + 0 * (Complex.sinh w.im).re =
              0 + 0 * (Complex.sinh w.im).re := by
            exact congrArg (fun x : ℝ => x + 0 * (Complex.sinh w.im).re)
              (mul_zero (Complex.sin w.re).re)
          _ = 0 + 0 := by
            exact congrArg (fun x : ℝ => 0 + x) (zero_mul (Complex.sinh w.im).re)
          _ = 0 := by
            exact zero_add 0
      exact Eq.trans hmul (Eq.trans him hzero)
    calc
      B.re = (C * Complex.I).re := rfl
      _ = -C.im := Complex.mul_I_re C
      _ = -0 := congrArg Neg.neg hC_im
      _ = 0 := neg_zero
  calc
    (Complex.cos w).re =
        (Complex.cos w.re * Complex.cosh w.im -
          Complex.sin w.re * Complex.sinh w.im * Complex.I).re := by
      exact congrArg Complex.re (Complex.cos_eq w)
    _ = Real.cos w.re * Real.cosh w.im := by
      calc
        (Complex.cos w.re * Complex.cosh w.im -
            Complex.sin w.re * Complex.sinh w.im * Complex.I).re =
            A.re - B.re := by
          exact Complex.sub_re A B
        _ = Real.cos w.re * Real.cosh w.im - 0 := by
          exact congrArg₂ Sub.sub hA_re hB_re
        _ = Real.cos w.re * Real.cosh w.im := by
          exact sub_zero (Real.cos w.re * Real.cosh w.im)

/-- The subcritical cosine barrier has strictly positive real part on the
closed vertical strip. -/
theorem verticalStrip_subcritical_cosineBarrier_re_pos_on_closedStrip
    {a b d : ℝ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    {z : ℂ}
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b) :
    0 <
      (Complex.cos
        (((d : ℝ) : ℂ) *
          (z - ((verticalStripCenter a b : ℝ) : ℂ)))).re := by
  let W : ℂ :=
    ((d : ℝ) : ℂ) *
      (z - ((verticalStripCenter a b : ℝ) : ℂ))
  have hW_re :
      W.re = d * (z.re - verticalStripCenter a b) := by
    let Q : ℂ := z - ((verticalStripCenter a b : ℝ) : ℂ)
    have hmul :
        (((d : ℝ) : ℂ) * Q).re =
          (((d : ℝ) : ℂ)).re * Q.re -
            (((d : ℝ) : ℂ)).im * Q.im :=
      Complex.mul_re ((d : ℝ) : ℂ) Q
    have hQ_re : Q.re = z.re - verticalStripCenter a b := by
      calc
        Q.re =
            z.re - (((verticalStripCenter a b : ℝ) : ℂ)).re := by
          exact Complex.sub_re z ((verticalStripCenter a b : ℝ) : ℂ)
        _ = z.re - verticalStripCenter a b := by
          exact congrArg
            (fun x : ℝ => z.re - x)
            (Complex.ofReal_re (verticalStripCenter a b))
    have hcoords₁ :
        (((d : ℝ) : ℂ)).re * Q.re -
            (((d : ℝ) : ℂ)).im * Q.im =
          d * Q.re - 0 * Q.im :=
      congrArg₂
        (fun x y : ℝ => x * Q.re - y * Q.im)
        (Complex.ofReal_re d)
        (Complex.ofReal_im d)
    have hcoords₂ :
        d * Q.re - 0 * Q.im =
          d * (z.re - verticalStripCenter a b) - 0 * Q.im :=
      congrArg
        (fun x : ℝ => d * x - 0 * Q.im)
        hQ_re
    have hzero :
        d * (z.re - verticalStripCenter a b) - 0 * Q.im =
          d * (z.re - verticalStripCenter a b) := by
      calc
        d * (z.re - verticalStripCenter a b) - 0 * Q.im =
            d * (z.re - verticalStripCenter a b) - 0 := by
          exact congrArg
            (fun x : ℝ => d * (z.re - verticalStripCenter a b) - x)
            (zero_mul Q.im)
        _ = d * (z.re - verticalStripCenter a b) := by
          exact sub_zero (d * (z.re - verticalStripCenter a b))
    exact Eq.trans hmul (Eq.trans hcoords₁ (Eq.trans hcoords₂ hzero))
  have hangle_abs :
      |d * (z.re - verticalStripCenter a b)| < π / 2 :=
    verticalStrip_subcritical_cosineBarrier_angle_abs_lt_pi_div_two
      hab hd_pos hd_threshold hza hzb
  have hangle_bounds :
      -(π / 2) < d * (z.re - verticalStripCenter a b) ∧
        d * (z.re - verticalStripCenter a b) < π / 2 :=
    abs_lt.mp hangle_abs
  have hW_window : W.re ∈ Set.Ioo (-(π / 2)) (π / 2) :=
    Eq.subst
      (motive := fun x : ℝ => x ∈ Set.Ioo (-(π / 2)) (π / 2))
      hW_re.symm
      hangle_bounds
  have hcos_pos : 0 < Real.cos W.re :=
    Real.cos_pos_of_mem_Ioo hW_window
  have hcosh_pos : 0 < Real.cosh W.im :=
    Real.cosh_pos W.im
  have hproduct_pos : 0 < Real.cos W.re * Real.cosh W.im :=
    mul_pos hcos_pos hcosh_pos
  exact
    Eq.subst
      (motive := fun x : ℝ => 0 < x)
      (complexCos_re_eq_realCos_mul_realCosh W).symm
      hproduct_pos

/-- The complex cosine has nonnegative real part in the standard vertical
cosine window. -/
theorem complexCos_re_nonneg_of_re_mem_standardWindow
    (w : ℂ)
    (hw : w.re ∈ Set.Icc (-(π / 2)) (π / 2)) :
    0 ≤ (Complex.cos w).re := by
  have hcos : 0 ≤ Real.cos w.re :=
    Real.cos_nonneg_of_mem_Icc hw
  have hcosh : 0 ≤ Real.cosh w.im :=
    le_of_lt (Real.cosh_pos w.im)
  have hproduct : 0 ≤ Real.cos w.re * Real.cosh w.im :=
    mul_nonneg hcos hcosh
  exact
    Eq.subst
      (motive := fun x : ℝ => 0 ≤ x)
      (complexCos_re_eq_realCos_mul_realCosh w).symm
      hproduct

/-- On the open vertical strip, the real part of the cosine damping kernel is
nonnegative.

Writing
`w = π * (z - center) / width`, the open strip gives
`w.re ∈ (-π/2, π/2)`, hence `0 ≤ Real.cos w.re`; also
`0 ≤ Real.cosh w.im`.  Since
`(Complex.cos w).re = Real.cos w.re * Real.cosh w.im`, the claim follows.
This is the only trigonometric input needed for the open-strip damping bound. -/
theorem verticalStripCosineDampingKernel_re_nonneg_on_openStrip_ownerGap
    (a b : ℝ)
    (hab : a < b)
    (z : ℂ)
    (hz : z ∈ Complex.re ⁻¹' Set.Ioo a b) :
    0 ≤ (verticalStripCosineDampingKernel a b z).re := by
  let w : ℂ :=
    ((π : ℝ) : ℂ) *
      (z - ((verticalStripCenter a b : ℝ) : ℂ)) /
        ((verticalStripWidth a b : ℝ) : ℂ)
  have hw_re :
      w.re =
        π * ((z - ((verticalStripCenter a b : ℝ) : ℂ)) /
          ((verticalStripWidth a b : ℝ) : ℂ)).re := by
    let q : ℂ := z - ((verticalStripCenter a b : ℝ) : ℂ)
    have hπ_im : (((π : ℝ) : ℂ)).im = 0 :=
      Complex.ofReal_im π
    have hπ_re : (((π : ℝ) : ℂ)).re = π :=
      Complex.ofReal_re π
    change
      ((((π : ℝ) : ℂ) * q) /
          ((verticalStripWidth a b : ℝ) : ℂ)).re =
        π * (q / ((verticalStripWidth a b : ℝ) : ℂ)).re
    calc
      ((((π : ℝ) : ℂ) * q) /
          ((verticalStripWidth a b : ℝ) : ℂ)).re =
          ((((π : ℝ) : ℂ) * q).re) /
            verticalStripWidth a b := by
        exact
          Complex.div_ofReal_re
            (((π : ℝ) : ℂ) * q)
            (verticalStripWidth a b)
      _ =
          (π * q.re - 0 * q.im) /
            verticalStripWidth a b := by
        exact
          congrArg (fun x : ℝ => x / verticalStripWidth a b)
            (Eq.trans
              (Complex.mul_re ((π : ℝ) : ℂ) q)
              (congrArg₂ (fun x y : ℝ => x * q.re - y * q.im)
                hπ_re hπ_im))
      _ =
          (π * q.re) / verticalStripWidth a b := by
        exact
          congrArg (fun x : ℝ => x / verticalStripWidth a b)
            (sub_eq_self.mpr (zero_mul q.im))
      _ =
          π * (q.re / verticalStripWidth a b) := by
        exact mul_div_assoc π q.re (verticalStripWidth a b)
      _ =
          π * (q / ((verticalStripWidth a b : ℝ) : ℂ)).re := by
        exact
          congrArg (fun x : ℝ => π * x)
            (Complex.div_ofReal_re q (verticalStripWidth a b)).symm
  have hwindow_raw :
      (π * ((z - ((verticalStripCenter a b : ℝ) : ℂ)) /
          ((verticalStripWidth a b : ℝ) : ℂ)).re) ∈
        Set.Icc (-(π / 2)) (π / 2) :=
    verticalStripCosineDampingAffine_re_mem_standardWindow_ownerGap a b hab z hz
  have hwindow : w.re ∈ Set.Icc (-(π / 2)) (π / 2) :=
    Eq.subst
      (motive := fun x : ℝ => x ∈ Set.Icc (-(π / 2)) (π / 2))
      hw_re.symm
      hwindow_raw
  have hcos : 0 ≤ (Complex.cos w).re :=
    complexCos_re_nonneg_of_re_mem_standardWindow w hwindow
  have hkernel :
      verticalStripCosineDampingKernel a b z = Complex.cos w := by
    rfl
  exact
    Eq.subst
      (motive := fun x : ℂ => 0 ≤ x.re)
      hkernel.symm
      hcos

/-- Real part of the cosine-damping exponent. -/
theorem verticalStripCosineDampingExponent_re_eq_neg_mul
    (a b ε : ℝ)
    (z : ℂ) :
    (-((ε : ℝ) : ℂ) *
        verticalStripCosineDampingKernel a b z).re =
      -ε * (verticalStripCosineDampingKernel a b z).re := by
  calc
    (-((ε : ℝ) : ℂ) *
        verticalStripCosineDampingKernel a b z).re =
        (-ε) * (verticalStripCosineDampingKernel a b z).re -
          (0 : ℝ) * (verticalStripCosineDampingKernel a b z).im := by
      exact
        Eq.trans
          (Complex.mul_re (-((ε : ℝ) : ℂ)) (verticalStripCosineDampingKernel a b z))
          (congrArg₂
            (fun x y : ℝ =>
              x * (verticalStripCosineDampingKernel a b z).re -
                y * (verticalStripCosineDampingKernel a b z).im)
            (by
              calc
                (-((ε : ℝ) : ℂ)).re = -(((ε : ℝ) : ℂ).re) :=
                  Complex.neg_re ((ε : ℝ) : ℂ)
                _ = -ε :=
                  congrArg Neg.neg (Complex.ofReal_re ε))
            (by
              calc
                (-((ε : ℝ) : ℂ)).im = -(((ε : ℝ) : ℂ).im) :=
                  Complex.neg_im ((ε : ℝ) : ℂ)
                _ = -0 :=
                  congrArg Neg.neg (Complex.ofReal_im ε)
                _ = 0 :=
                  neg_zero))
    _ =
        (-ε) * (verticalStripCosineDampingKernel a b z).re - 0 := by
      exact congrArg
        (fun y : ℝ =>
          (-ε) * (verticalStripCosineDampingKernel a b z).re - y)
        (zero_mul (verticalStripCosineDampingKernel a b z).im)
    _ =
        (-ε) * (verticalStripCosineDampingKernel a b z).re := by
      exact sub_zero ((-ε) * (verticalStripCosineDampingKernel a b z).re)
    _ =
        -(ε * (verticalStripCosineDampingKernel a b z).re) := by
      exact neg_mul ε (verticalStripCosineDampingKernel a b z).re
    _ =
        -ε * (verticalStripCosineDampingKernel a b z).re := by
      exact (neg_mul ε (verticalStripCosineDampingKernel a b z).re).symm

/-- The cosine-damping exponent has nonpositive real part on the open strip. -/
theorem verticalStripCosineDampingExponent_re_nonpos_on_openStrip
    (a b ε : ℝ)
    (hab : a < b)
    (hε : 0 ≤ ε)
    (z : ℂ)
    (hz : z ∈ Complex.re ⁻¹' Set.Ioo a b) :
    (-((ε : ℝ) : ℂ) *
        verticalStripCosineDampingKernel a b z).re ≤ 0 := by
  have hkernel_nonneg :
      0 ≤ (verticalStripCosineDampingKernel a b z).re :=
    verticalStripCosineDampingKernel_re_nonneg_on_openStrip_ownerGap
      a b hab z hz
  have hmul_nonneg :
      0 ≤ ε * (verticalStripCosineDampingKernel a b z).re :=
    mul_nonneg hε hkernel_nonneg
  have hneg_nonpos :
      -(ε * (verticalStripCosineDampingKernel a b z).re) ≤ 0 :=
    neg_nonpos.mpr hmul_nonneg
  have hre :
      (-((ε : ℝ) : ℂ) *
          verticalStripCosineDampingKernel a b z).re =
        -ε * (verticalStripCosineDampingKernel a b z).re :=
    verticalStripCosineDampingExponent_re_eq_neg_mul a b ε z
  have hmul :
      -ε * (verticalStripCosineDampingKernel a b z).re =
        -(ε * (verticalStripCosineDampingKernel a b z).re) :=
    neg_mul ε (verticalStripCosineDampingKernel a b z).re
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ 0)
      (Eq.trans hre hmul).symm
      hneg_nonpos

/-- The norm of a complex exponential is the exponential of its real part. -/
theorem complexNorm_exp_eq_realExp_re
    (w : ℂ) :
    ‖Complex.exp w‖ = Real.exp w.re := by
  exact Eq.trans (Complex.norm_eq_abs (Complex.exp w)) (Complex.abs_exp w)

/-- Norm identity for the upper-tail polynomial normalized family. -/
theorem verticalStripUpperTailPolynomialNormalizedFamily_norm_eq
    (f : ℂ → ℂ)
    (a b C : ℝ)
    (N : ℕ)
    (z : ℂ) :
    ‖verticalStripUpperTailPolynomialNormalizedFamily f a b C N z‖ =
      ‖f z‖ *
        Real.exp
          (-(C *
            (verticalStripUpperTailPolynomialNormalizerKernel a b N z).re)) := by
  let K : ℂ := verticalStripUpperTailPolynomialNormalizerKernel a b N z
  have hfactor :
      ‖Complex.exp (-((C : ℝ) : ℂ) * K)‖ =
        Real.exp (-(C * K.re)) := by
    have hre :
        (-((C : ℝ) : ℂ) * K).re = -(C * K.re) := by
      calc
        (-((C : ℝ) : ℂ) * K).re =
            (-((C : ℝ) : ℂ)).re * K.re -
              (-((C : ℝ) : ℂ)).im * K.im :=
          Complex.mul_re (-((C : ℝ) : ℂ)) K
        _ = (-C) * K.re - 0 * K.im := by
          have hneg_re : (-((C : ℝ) : ℂ)).re = -C := by
            calc
              (-((C : ℝ) : ℂ)).re = -(((C : ℝ) : ℂ).re) :=
                Complex.neg_re ((C : ℝ) : ℂ)
              _ = -C := congrArg Neg.neg (Complex.ofReal_re C)
          have hneg_im : (-((C : ℝ) : ℂ)).im = 0 := by
            calc
              (-((C : ℝ) : ℂ)).im = -(((C : ℝ) : ℂ).im) :=
                Complex.neg_im ((C : ℝ) : ℂ)
              _ = -0 := congrArg Neg.neg (Complex.ofReal_im C)
              _ = 0 := neg_zero
          exact congrArg₂
            (fun x y : ℝ => x * K.re - y * K.im)
            hneg_re
            hneg_im
        _ = (-C) * K.re - 0 := by
          exact congrArg (fun x : ℝ => (-C) * K.re - x) (zero_mul K.im)
        _ = (-C) * K.re := sub_zero ((-C) * K.re)
        _ = -(C * K.re) := neg_mul C K.re
    exact
      Eq.subst
        (motive := fun x : ℝ =>
          ‖Complex.exp (-((C : ℝ) : ℂ) * K)‖ = Real.exp x)
        hre
        (complexNorm_exp_eq_realExp_re (-((C : ℝ) : ℂ) * K))
  calc
    ‖verticalStripUpperTailPolynomialNormalizedFamily f a b C N z‖ =
        ‖f z * Complex.exp (-((C : ℝ) : ℂ) * K)‖ := rfl
    _ = ‖f z‖ * ‖Complex.exp (-((C : ℝ) : ℂ) * K)‖ :=
      norm_mul (f z) (Complex.exp (-((C : ℝ) : ℂ) * K))
    _ = ‖f z‖ * Real.exp (-(C * K.re)) :=
      congrArg (fun x : ℝ => ‖f z‖ * x) hfactor

/-- Norm identity for the bounded upper-tail polynomial normalized factor. -/
theorem verticalStripUpperTailPolynomialBoundedFactor_norm_eq
    (f : ℂ → ℂ)
    (a b A C : ℝ)
    (N : ℕ)
    (z : ℂ) :
    ‖verticalStripUpperTailPolynomialBoundedFactor f a b A C N z‖ =
      ‖A⁻¹‖ *
        (‖f z‖ *
          Real.exp
            (-(C *
              (verticalStripUpperTailPolynomialNormalizerKernel a b N z).re))) := by
  have hnorm :
      ‖verticalStripUpperTailPolynomialNormalizedFamily f a b C N z‖ =
        ‖f z‖ *
          Real.exp
            (-(C *
              (verticalStripUpperTailPolynomialNormalizerKernel a b N z).re)) :=
    verticalStripUpperTailPolynomialNormalizedFamily_norm_eq f a b C N z
  calc
    ‖verticalStripUpperTailPolynomialBoundedFactor f a b A C N z‖ =
        ‖((A⁻¹ : ℝ) : ℂ) *
          verticalStripUpperTailPolynomialNormalizedFamily f a b C N z‖ := rfl
    _ =
        ‖((A⁻¹ : ℝ) : ℂ)‖ *
          ‖verticalStripUpperTailPolynomialNormalizedFamily f a b C N z‖ :=
      norm_mul
        (((A⁻¹ : ℝ) : ℂ))
        (verticalStripUpperTailPolynomialNormalizedFamily f a b C N z)
    _ =
        ‖A⁻¹‖ *
          ‖verticalStripUpperTailPolynomialNormalizedFamily f a b C N z‖ := by
      have hcoe_norm : ‖((A⁻¹ : ℝ) : ℂ)‖ = ‖A⁻¹‖ :=
        RCLike.norm_ofReal (K := ℂ) (A⁻¹)
      exact congrArg
        (fun x : ℝ =>
          x * ‖verticalStripUpperTailPolynomialNormalizedFamily f a b C N z‖)
        hcoe_norm
    _ =
        ‖A⁻¹‖ *
          (‖f z‖ *
            Real.exp
              (-(C *
                (verticalStripUpperTailPolynomialNormalizerKernel a b N z).re))) :=
      congrArg (fun x : ℝ => ‖A⁻¹‖ * x) hnorm

/-- Norm identity for the degree-dependent bounded upper-tail polynomial
normalized factor. -/
theorem verticalStripUpperTailDegreePolynomialBoundedFactor_norm_eq
    (f : ℂ → ℂ)
    (a b A C : ℝ)
    (N : ℕ)
    (z : ℂ) :
    ‖verticalStripUpperTailDegreePolynomialBoundedFactor f a b A C N z‖ =
      ‖A⁻¹‖ *
        (‖f z‖ *
          Real.exp
            (-(C *
              (verticalStripUpperTailDegreePolynomialKernel a b N z).re))) := by
  let K : ℂ := verticalStripUpperTailDegreePolynomialKernel a b N z
  have hfactor :
      ‖Complex.exp (-((C : ℝ) : ℂ) * K)‖ =
        Real.exp (-(C * K.re)) := by
    have hre :
        (-((C : ℝ) : ℂ) * K).re = -(C * K.re) := by
      calc
        (-((C : ℝ) : ℂ) * K).re =
            (-((C : ℝ) : ℂ)).re * K.re -
              (-((C : ℝ) : ℂ)).im * K.im :=
          Complex.mul_re (-((C : ℝ) : ℂ)) K
        _ = (-C) * K.re - 0 * K.im := by
          have hneg_re : (-((C : ℝ) : ℂ)).re = -C := by
            calc
              (-((C : ℝ) : ℂ)).re = -(((C : ℝ) : ℂ).re) :=
                Complex.neg_re ((C : ℝ) : ℂ)
              _ = -C := congrArg Neg.neg (Complex.ofReal_re C)
          have hneg_im : (-((C : ℝ) : ℂ)).im = 0 := by
            calc
              (-((C : ℝ) : ℂ)).im = -(((C : ℝ) : ℂ).im) :=
                Complex.neg_im ((C : ℝ) : ℂ)
              _ = -0 := congrArg Neg.neg (Complex.ofReal_im C)
              _ = 0 := neg_zero
          exact congrArg₂
            (fun x y : ℝ => x * K.re - y * K.im)
            hneg_re
            hneg_im
        _ = (-C) * K.re - 0 := by
          exact congrArg (fun x : ℝ => (-C) * K.re - x) (zero_mul K.im)
        _ = (-C) * K.re := sub_zero ((-C) * K.re)
        _ = -(C * K.re) := neg_mul C K.re
    exact
      Eq.subst
        (motive := fun x : ℝ =>
          ‖Complex.exp (-((C : ℝ) : ℂ) * K)‖ = Real.exp x)
        hre
        (complexNorm_exp_eq_realExp_re (-((C : ℝ) : ℂ) * K))
  have hcoe_norm : ‖((A⁻¹ : ℝ) : ℂ)‖ = ‖A⁻¹‖ :=
    RCLike.norm_ofReal (K := ℂ) (A⁻¹)
  calc
    ‖verticalStripUpperTailDegreePolynomialBoundedFactor f a b A C N z‖ =
        ‖((A⁻¹ : ℝ) : ℂ) *
          (f z * Complex.exp (-((C : ℝ) : ℂ) * K))‖ := rfl
    _ =
        ‖((A⁻¹ : ℝ) : ℂ)‖ *
          ‖f z * Complex.exp (-((C : ℝ) : ℂ) * K)‖ :=
      norm_mul
        (((A⁻¹ : ℝ) : ℂ))
        (f z * Complex.exp (-((C : ℝ) : ℂ) * K))
    _ =
        ‖((A⁻¹ : ℝ) : ℂ)‖ *
          (‖f z‖ * ‖Complex.exp (-((C : ℝ) : ℂ) * K)‖) := by
      exact congrArg
        (fun x : ℝ => ‖((A⁻¹ : ℝ) : ℂ)‖ * x)
        (norm_mul (f z) (Complex.exp (-((C : ℝ) : ℂ) * K)))
    _ =
        ‖A⁻¹‖ *
          (‖f z‖ *
            Real.exp
              (-(C *
                (verticalStripUpperTailDegreePolynomialKernel a b N z).re))) := by
      exact congrArg₂ HMul.hMul
        hcoe_norm
        (congrArg (fun x : ℝ => ‖f z‖ * x) hfactor)

/-- The named subcritical cosine barrier has strictly positive real part on the
closed vertical strip. -/
theorem verticalStripSubcriticalCosineBarrierKernel_re_pos_on_closedStrip
    {a b d : ℝ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    {z : ℂ}
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b) :
    0 < (verticalStripSubcriticalCosineBarrierKernel a b d z).re := by
  have hraw :
      0 <
        (Complex.cos
          (((d : ℝ) : ℂ) *
            (z - ((verticalStripCenter a b : ℝ) : ℂ)))).re :=
    verticalStrip_subcritical_cosineBarrier_re_pos_on_closedStrip
      hab hd_pos hd_threshold hza hzb
  exact
    Eq.subst
      (motive := fun w : ℂ => 0 < w.re)
      (verticalStripSubcriticalCosineBarrierKernel_eq a b d z).symm
      hraw

/-- Coordinate formula for the real part of the subcritical cosine barrier. -/
theorem verticalStripSubcriticalCosineBarrierKernel_re_eq_cos_mul_cosh
    (a b d : ℝ)
    (z : ℂ) :
    (verticalStripSubcriticalCosineBarrierKernel a b d z).re =
      Real.cos (d * (z.re - verticalStripCenter a b)) *
        Real.cosh (d * z.im) := by
  let W : ℂ :=
    ((d : ℝ) : ℂ) *
      (z - ((verticalStripCenter a b : ℝ) : ℂ))
  let Q : ℂ := z - ((verticalStripCenter a b : ℝ) : ℂ)
  have hQ_re : Q.re = z.re - verticalStripCenter a b := by
    calc
      Q.re =
          z.re - (((verticalStripCenter a b : ℝ) : ℂ)).re := by
        exact Complex.sub_re z ((verticalStripCenter a b : ℝ) : ℂ)
      _ = z.re - verticalStripCenter a b := by
        exact congrArg
          (fun x : ℝ => z.re - x)
          (Complex.ofReal_re (verticalStripCenter a b))
  have hQ_im : Q.im = z.im := by
    calc
      Q.im =
          z.im - (((verticalStripCenter a b : ℝ) : ℂ)).im := by
        exact Complex.sub_im z ((verticalStripCenter a b : ℝ) : ℂ)
      _ = z.im - 0 := by
        exact congrArg
          (fun x : ℝ => z.im - x)
          (Complex.ofReal_im (verticalStripCenter a b))
      _ = z.im := by
        exact sub_zero z.im
  have hW_re : W.re = d * (z.re - verticalStripCenter a b) := by
    have hmul :
        (((d : ℝ) : ℂ) * Q).re =
          (((d : ℝ) : ℂ)).re * Q.re -
            (((d : ℝ) : ℂ)).im * Q.im :=
      Complex.mul_re ((d : ℝ) : ℂ) Q
    have hcoords₁ :
        (((d : ℝ) : ℂ)).re * Q.re -
            (((d : ℝ) : ℂ)).im * Q.im =
          d * Q.re - 0 * Q.im :=
      congrArg₂
        (fun x y : ℝ => x * Q.re - y * Q.im)
        (Complex.ofReal_re d)
        (Complex.ofReal_im d)
    have hcoords₂ :
        d * Q.re - 0 * Q.im =
          d * (z.re - verticalStripCenter a b) - 0 * Q.im :=
      congrArg
        (fun x : ℝ => d * x - 0 * Q.im)
        hQ_re
    have hzero :
        d * (z.re - verticalStripCenter a b) - 0 * Q.im =
          d * (z.re - verticalStripCenter a b) := by
      calc
        d * (z.re - verticalStripCenter a b) - 0 * Q.im =
            d * (z.re - verticalStripCenter a b) - 0 := by
          exact congrArg
            (fun x : ℝ => d * (z.re - verticalStripCenter a b) - x)
            (zero_mul Q.im)
        _ = d * (z.re - verticalStripCenter a b) := by
          exact sub_zero (d * (z.re - verticalStripCenter a b))
    exact Eq.trans hmul (Eq.trans hcoords₁ (Eq.trans hcoords₂ hzero))
  have hW_im : W.im = d * z.im := by
    have hmul :
        (((d : ℝ) : ℂ) * Q).im =
          (((d : ℝ) : ℂ)).re * Q.im +
            (((d : ℝ) : ℂ)).im * Q.re :=
      Complex.mul_im ((d : ℝ) : ℂ) Q
    have hcoords₁ :
        (((d : ℝ) : ℂ)).re * Q.im +
            (((d : ℝ) : ℂ)).im * Q.re =
          d * Q.im + 0 * Q.re :=
      congrArg₂
        (fun x y : ℝ => x * Q.im + y * Q.re)
        (Complex.ofReal_re d)
        (Complex.ofReal_im d)
    have hcoords₂ :
        d * Q.im + 0 * Q.re =
          d * z.im + 0 * Q.re :=
      congrArg
        (fun x : ℝ => d * x + 0 * Q.re)
        hQ_im
    have hzero :
        d * z.im + 0 * Q.re = d * z.im := by
      calc
        d * z.im + 0 * Q.re = d * z.im + 0 := by
          exact congrArg (fun x : ℝ => d * z.im + x) (zero_mul Q.re)
        _ = d * z.im := by
          exact add_zero (d * z.im)
    exact Eq.trans hmul (Eq.trans hcoords₁ (Eq.trans hcoords₂ hzero))
  have hkernel :
      verticalStripSubcriticalCosineBarrierKernel a b d z =
        Complex.cos W := by
    rfl
  have hre :
      (Complex.cos W).re =
        Real.cos (d * (z.re - verticalStripCenter a b)) *
          Real.cosh (d * z.im) := by
    calc
      (Complex.cos W).re =
          Real.cos W.re * Real.cosh W.im :=
        complexCos_re_eq_realCos_mul_realCosh W
      _ =
          Real.cos (d * (z.re - verticalStripCenter a b)) *
            Real.cosh W.im := by
        exact congrArg
          (fun x : ℝ => Real.cos x * Real.cosh W.im)
          hW_re
      _ =
          Real.cos (d * (z.re - verticalStripCenter a b)) *
            Real.cosh (d * z.im) := by
        exact congrArg
          (fun x : ℝ =>
            Real.cos (d * (z.re - verticalStripCenter a b)) *
              Real.cosh x)
          hW_im
  exact
    Eq.subst
      (motive := fun w : ℂ =>
        w.re =
          Real.cos (d * (z.re - verticalStripCenter a b)) *
            Real.cosh (d * z.im))
      hkernel.symm
      hre

/-- Real part of the subcritical cosine barrier on the left boundary line. -/
theorem verticalStripSubcriticalCosineBarrierKernel_leftBoundary_re_eq
    (a b d : ℝ)
    {z : ℂ}
    (hz : z.re = a) :
    (verticalStripSubcriticalCosineBarrierKernel a b d z).re =
      Real.cos (d * (-((b - a) / 2))) * Real.cosh (d * z.im) := by
  have hcoords :
      z.re - verticalStripCenter a b = -((b - a) / 2) := by
    exact Eq.trans
      (congrArg (fun x : ℝ => x - verticalStripCenter a b) hz)
      (Eq.trans
        (leftEndpoint_sub_verticalStripCenter a b)
        (Eq.trans
          (congrArg (fun x : ℝ => x / 2) (sub_eq_neg_sub a b))
          (neg_div (b - a) 2).symm))
  exact Eq.trans
    (verticalStripSubcriticalCosineBarrierKernel_re_eq_cos_mul_cosh a b d z)
    (congrArg
      (fun x : ℝ => Real.cos (d * x) * Real.cosh (d * z.im))
      hcoords)

/-- Real part of the subcritical cosine barrier on the right boundary line. -/
theorem verticalStripSubcriticalCosineBarrierKernel_rightBoundary_re_eq
    (a b d : ℝ)
    {z : ℂ}
    (hz : z.re = b) :
    (verticalStripSubcriticalCosineBarrierKernel a b d z).re =
      Real.cos (d * ((b - a) / 2)) * Real.cosh (d * z.im) := by
  have hcoords :
      z.re - verticalStripCenter a b = (b - a) / 2 := by
    exact Eq.trans
      (congrArg (fun x : ℝ => x - verticalStripCenter a b) hz)
      (rightEndpoint_sub_verticalStripCenter a b)
  exact Eq.trans
    (verticalStripSubcriticalCosineBarrierKernel_re_eq_cos_mul_cosh a b d z)
    (congrArg
      (fun x : ℝ => Real.cos (d * x) * Real.cosh (d * z.im))
      hcoords)

/-- The fixed right-boundary cosine coefficient is positive for a subcritical
barrier frequency. -/
theorem verticalStripSubcriticalCosineBarrierKernel_rightBoundary_cos_pos
    {a b d : ℝ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a)) :
    0 < Real.cos (d * ((b - a) / 2)) := by
  have hangle :
      |d * (b - verticalStripCenter a b)| < π / 2 :=
    verticalStrip_subcritical_cosineBarrier_angle_abs_lt_pi_div_two
      hab hd_pos hd_threshold (le_of_lt hab) (le_refl b)
  have hendpoint :
      b - verticalStripCenter a b = (b - a) / 2 :=
    rightEndpoint_sub_verticalStripCenter a b
  have hangle_endpoint :
      |d * ((b - a) / 2)| < π / 2 := by
    exact Eq.subst
      (motive := fun x : ℝ => |d * x| < π / 2)
      hendpoint
      hangle
  have hwindow :
      d * ((b - a) / 2) ∈ Set.Ioo (-(π / 2)) (π / 2) :=
    abs_lt.mp hangle_endpoint
  exact Real.cos_pos_of_mem_Ioo hwindow

/-- The fixed left-boundary cosine coefficient is positive for a subcritical
barrier frequency. -/
theorem verticalStripSubcriticalCosineBarrierKernel_leftBoundary_cos_pos
    {a b d : ℝ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a)) :
    0 < Real.cos (d * (-((b - a) / 2))) := by
  have hangle :
      |d * (a - verticalStripCenter a b)| < π / 2 :=
    verticalStrip_subcritical_cosineBarrier_angle_abs_lt_pi_div_two
      hab hd_pos hd_threshold (le_refl a) (le_of_lt hab)
  have hleft :
      a - verticalStripCenter a b = -((b - a) / 2) := by
    exact Eq.trans
      (leftEndpoint_sub_verticalStripCenter a b)
      (Eq.trans
        (congrArg (fun x : ℝ => x / 2) (sub_eq_neg_sub a b))
        (neg_div (b - a) 2).symm)
  have hangle_endpoint :
      |d * (-((b - a) / 2))| < π / 2 := by
    exact Eq.subst
      (motive := fun x : ℝ => |d * x| < π / 2)
      hleft
      hangle
  have hwindow :
      d * (-((b - a) / 2)) ∈ Set.Ioo (-(π / 2)) (π / 2) :=
    abs_lt.mp hangle_endpoint
  exact Real.cos_pos_of_mem_Ioo hwindow

/-- The right-boundary half-cosine absorber coefficient is positive. -/
theorem verticalStripSubcriticalCosineBarrierKernel_rightBoundary_halfCos_pos
    {a b d : ℝ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a)) :
    0 < Real.cos (d * ((b - a) / 2)) / 2 := by
  exact div_pos
    (verticalStripSubcriticalCosineBarrierKernel_rightBoundary_cos_pos
      hab hd_pos hd_threshold)
    zero_lt_two

/-- The left-boundary half-cosine absorber coefficient is positive. -/
theorem verticalStripSubcriticalCosineBarrierKernel_leftBoundary_halfCos_pos
    {a b d : ℝ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a)) :
    0 < Real.cos (d * (-((b - a) / 2))) / 2 := by
  exact div_pos
    (verticalStripSubcriticalCosineBarrierKernel_leftBoundary_cos_pos
      hab hd_pos hd_threshold)
    zero_lt_two

/-- The right-boundary superexponential absorber coefficient is positive for
positive damping. -/
theorem verticalStripSubcriticalCosineDamping_rightBoundary_absorberCoeff_pos
    {a b d ε : ℝ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε : 0 < ε) :
    0 < ε * (Real.cos (d * ((b - a) / 2)) / 2) := by
  exact mul_pos hε
    (verticalStripSubcriticalCosineBarrierKernel_rightBoundary_halfCos_pos
      hab hd_pos hd_threshold)

/-- The left-boundary superexponential absorber coefficient is positive for
positive damping. -/
theorem verticalStripSubcriticalCosineDamping_leftBoundary_absorberCoeff_pos
    {a b d ε : ℝ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε : 0 < ε) :
    0 < ε * (Real.cos (d * (-((b - a) / 2))) / 2) := by
  exact mul_pos hε
    (verticalStripSubcriticalCosineBarrierKernel_leftBoundary_halfCos_pos
      hab hd_pos hd_threshold)

/-- On the right boundary ray, the subcritical barrier real part dominates
the fixed positive endpoint cosine coefficient. -/
theorem verticalStripSubcriticalCosineBarrierKernel_rightBoundary_re_ge_cos
    {a b d : ℝ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    {z : ℂ}
    (hz : z.re = b) :
    Real.cos (d * ((b - a) / 2)) ≤
      (verticalStripSubcriticalCosineBarrierKernel a b d z).re := by
  let c : ℝ := Real.cos (d * ((b - a) / 2))
  have hc_pos : 0 < c :=
    verticalStripSubcriticalCosineBarrierKernel_rightBoundary_cos_pos
      hab hd_pos hd_threshold
  have hc_nonneg : 0 ≤ c :=
    le_of_lt hc_pos
  have hcosh_one : 1 ≤ Real.cosh (d * z.im) :=
    Real.one_le_cosh (d * z.im)
  have hmul :
      c ≤ c * Real.cosh (d * z.im) := by
    calc
      c = c * 1 := by
        exact (mul_one c).symm
      _ ≤ c * Real.cosh (d * z.im) :=
        mul_le_mul_of_nonneg_left hcosh_one hc_nonneg
  exact Eq.subst
    (motive := fun x : ℝ => c ≤ x)
    (verticalStripSubcriticalCosineBarrierKernel_rightBoundary_re_eq
      a b d hz).symm
    hmul

/-- On the left boundary ray, the subcritical barrier real part dominates
the fixed positive endpoint cosine coefficient. -/
theorem verticalStripSubcriticalCosineBarrierKernel_leftBoundary_re_ge_cos
    {a b d : ℝ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    {z : ℂ}
    (hz : z.re = a) :
    Real.cos (d * (-((b - a) / 2))) ≤
      (verticalStripSubcriticalCosineBarrierKernel a b d z).re := by
  let c : ℝ := Real.cos (d * (-((b - a) / 2)))
  have hc_pos : 0 < c :=
    verticalStripSubcriticalCosineBarrierKernel_leftBoundary_cos_pos
      hab hd_pos hd_threshold
  have hc_nonneg : 0 ≤ c :=
    le_of_lt hc_pos
  have hcosh_one : 1 ≤ Real.cosh (d * z.im) :=
    Real.one_le_cosh (d * z.im)
  have hmul :
      c ≤ c * Real.cosh (d * z.im) := by
    calc
      c = c * 1 := by
        exact (mul_one c).symm
      _ ≤ c * Real.cosh (d * z.im) :=
        mul_le_mul_of_nonneg_left hcosh_one hc_nonneg
  exact Eq.subst
    (motive := fun x : ℝ => c ≤ x)
    (verticalStripSubcriticalCosineBarrierKernel_leftBoundary_re_eq
      a b d hz).symm
    hmul

/-- The hyperbolic cosine dominates half of the positive exponential. -/
theorem real_exp_half_le_cosh
    (x : ℝ) :
    Real.exp x / 2 ≤ Real.cosh x := by
  have hpos : 0 ≤ Real.exp (-x) :=
    le_of_lt (Real.exp_pos (-x))
  have hsum : Real.exp x ≤ Real.exp x + Real.exp (-x) :=
    le_add_of_nonneg_right hpos
  have hdiv : Real.exp x / 2 ≤ (Real.exp x + Real.exp (-x)) / 2 :=
    div_le_div_of_nonneg_right hsum (le_of_lt zero_lt_two)
  exact
    Eq.subst
      (motive := fun y : ℝ => Real.exp x / 2 ≤ y)
      (Real.cosh_eq x).symm
      hdiv

/-- The hyperbolic cosine dominates half of the negative exponential. -/
theorem real_exp_neg_half_le_cosh
    (x : ℝ) :
    Real.exp (-x) / 2 ≤ Real.cosh x := by
  have hpos : 0 ≤ Real.exp x :=
    le_of_lt (Real.exp_pos x)
  have hsum : Real.exp (-x) ≤ Real.exp x + Real.exp (-x) :=
    le_add_of_nonneg_left hpos
  have hdiv : Real.exp (-x) / 2 ≤ (Real.exp x + Real.exp (-x)) / 2 :=
    div_le_div_of_nonneg_right hsum (le_of_lt zero_lt_two)
  exact
    Eq.subst
      (motive := fun y : ℝ => Real.exp (-x) / 2 ≤ y)
      (Real.cosh_eq x).symm
      hdiv

/-- On the right boundary ray, the subcritical barrier real part has
exponential lower growth in the upper-tail height. -/
theorem verticalStripSubcriticalCosineBarrierKernel_rightBoundary_re_ge_exp
    {a b d : ℝ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    {z : ℂ}
    (hz : z.re = b) :
    (Real.cos (d * ((b - a) / 2)) / 2) * Real.exp (d * z.im) ≤
      (verticalStripSubcriticalCosineBarrierKernel a b d z).re := by
  let c : ℝ := Real.cos (d * ((b - a) / 2))
  have hc_pos : 0 < c :=
    verticalStripSubcriticalCosineBarrierKernel_rightBoundary_cos_pos
      hab hd_pos hd_threshold
  have hc_nonneg : 0 ≤ c :=
    le_of_lt hc_pos
  have hcosh_lower :
      Real.exp (d * z.im) / 2 ≤ Real.cosh (d * z.im) :=
    real_exp_half_le_cosh (d * z.im)
  have hmul_lower :
      c * (Real.exp (d * z.im) / 2) ≤ c * Real.cosh (d * z.im) :=
    mul_le_mul_of_nonneg_left hcosh_lower hc_nonneg
  have hleft_eq :
      (c / 2) * Real.exp (d * z.im) =
        c * (Real.exp (d * z.im) / 2) := by
    calc
      (c / 2) * Real.exp (d * z.im) =
          (c * (1 / 2)) * Real.exp (d * z.im) := by
        exact congrArg
          (fun y : ℝ => y * Real.exp (d * z.im))
          (div_eq_mul_one_div c 2)
      _ = c * ((1 / 2) * Real.exp (d * z.im)) := by
        exact mul_assoc c (1 / 2) (Real.exp (d * z.im))
      _ = c * (Real.exp (d * z.im) * (1 / 2)) := by
        exact congrArg
          (fun y : ℝ => c * y)
          (mul_comm (1 / 2) (Real.exp (d * z.im)))
      _ = c * (Real.exp (d * z.im) / 2) := by
        exact congrArg
          (fun y : ℝ => c * y)
          (div_eq_mul_one_div (Real.exp (d * z.im)) 2).symm
  exact
    Eq.subst
      (motive := fun y : ℝ =>
        (c / 2) * Real.exp (d * z.im) ≤ y)
      (verticalStripSubcriticalCosineBarrierKernel_rightBoundary_re_eq
        a b d hz).symm
      (Eq.subst
        (motive := fun y : ℝ => y ≤ c * Real.cosh (d * z.im))
        hleft_eq
        hmul_lower)

/-- On the left boundary ray, the subcritical barrier real part has
exponential lower growth in the upper-tail height. -/
theorem verticalStripSubcriticalCosineBarrierKernel_leftBoundary_re_ge_exp
    {a b d : ℝ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    {z : ℂ}
    (hz : z.re = a) :
    (Real.cos (d * (-((b - a) / 2))) / 2) * Real.exp (d * z.im) ≤
      (verticalStripSubcriticalCosineBarrierKernel a b d z).re := by
  let c : ℝ := Real.cos (d * (-((b - a) / 2)))
  have hc_pos : 0 < c :=
    verticalStripSubcriticalCosineBarrierKernel_leftBoundary_cos_pos
      hab hd_pos hd_threshold
  have hc_nonneg : 0 ≤ c :=
    le_of_lt hc_pos
  have hcosh_lower :
      Real.exp (d * z.im) / 2 ≤ Real.cosh (d * z.im) :=
    real_exp_half_le_cosh (d * z.im)
  have hmul_lower :
      c * (Real.exp (d * z.im) / 2) ≤ c * Real.cosh (d * z.im) :=
    mul_le_mul_of_nonneg_left hcosh_lower hc_nonneg
  have hleft_eq :
      (c / 2) * Real.exp (d * z.im) =
        c * (Real.exp (d * z.im) / 2) := by
    calc
      (c / 2) * Real.exp (d * z.im) =
          (c * (1 / 2)) * Real.exp (d * z.im) := by
        exact congrArg
          (fun y : ℝ => y * Real.exp (d * z.im))
          (div_eq_mul_one_div c 2)
      _ = c * ((1 / 2) * Real.exp (d * z.im)) := by
        exact mul_assoc c (1 / 2) (Real.exp (d * z.im))
      _ = c * (Real.exp (d * z.im) * (1 / 2)) := by
        exact congrArg
          (fun y : ℝ => c * y)
          (mul_comm (1 / 2) (Real.exp (d * z.im)))
      _ = c * (Real.exp (d * z.im) / 2) := by
        exact congrArg
          (fun y : ℝ => c * y)
          (div_eq_mul_one_div (Real.exp (d * z.im)) 2).symm
  exact
    Eq.subst
      (motive := fun y : ℝ =>
        (c / 2) * Real.exp (d * z.im) ≤ y)
      (verticalStripSubcriticalCosineBarrierKernel_leftBoundary_re_eq
        a b d hz).symm
      (Eq.subst
        (motive := fun y : ℝ => y ≤ c * Real.cosh (d * z.im))
        hleft_eq
        hmul_lower)

/-- On the whole closed strip, the subcritical barrier real part has a uniform
positive upper-tail exponential lower bound. -/
theorem verticalStripSubcriticalCosineBarrierKernel_closedStrip_re_ge_exp
    {a b d : ℝ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    {z : ℂ}
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b) :
    (Real.cos (d * ((b - a) / 2)) / 2) * Real.exp (d * z.im) ≤
      (verticalStripSubcriticalCosineBarrierKernel a b d z).re := by
  let w : ℝ := b - a
  let x : ℝ := z.re - verticalStripCenter a b
  let θ : ℝ := d * x
  have hw_pos : 0 < w :=
    sub_pos.mpr hab
  have hx_left : -(w / 2) ≤ x := by
    have hleft :
        a - verticalStripCenter a b = -(w / 2) := by
      calc
        a - verticalStripCenter a b = (a - b) / 2 :=
          leftEndpoint_sub_verticalStripCenter a b
        _ = -(w / 2) := by
          have hnum : a - b = -w :=
            sub_eq_neg_sub a b
          exact
            Eq.trans
              (congrArg (fun t : ℝ => t / 2) hnum)
              (neg_div w 2).symm
    have hmono :
        a - verticalStripCenter a b ≤
          z.re - verticalStripCenter a b :=
      sub_le_sub_right hza (verticalStripCenter a b)
    exact
      Eq.subst
        (motive := fun y : ℝ => y ≤ x)
        hleft
        hmono
  have hx_right : x ≤ w / 2 := by
    have hright :
        b - verticalStripCenter a b = w / 2 :=
      rightEndpoint_sub_verticalStripCenter a b
    have hmono :
        z.re - verticalStripCenter a b ≤
          b - verticalStripCenter a b :=
      sub_le_sub_right hzb (verticalStripCenter a b)
    exact
      Eq.subst
        (motive := fun y : ℝ => x ≤ y)
        hright
        hmono
  have hx_abs : |x| ≤ w / 2 :=
    abs_le.mpr ⟨hx_left, hx_right⟩
  have htheta_abs : |θ| ≤ d * (w / 2) := by
    calc
      |θ| = |d| * |x| := abs_mul d x
      _ = d * |x| := by
        exact congrArg (fun y : ℝ => y * |x|) (abs_of_pos hd_pos)
      _ ≤ d * (w / 2) :=
        mul_le_mul_of_nonneg_left hx_abs (le_of_lt hd_pos)
  have hdw_lt_pi : d * w < π :=
    (lt_div_iff₀ hw_pos).mp hd_threshold
  have hendpoint_lt_pi_div_two : d * (w / 2) < π / 2 := by
    have hdiv : d * w / 2 < π / 2 :=
      div_lt_div_of_pos_right hdw_lt_pi zero_lt_two
    exact
      Eq.subst
        (motive := fun y : ℝ => y < π / 2)
        (mul_div_assoc d w 2).symm
        hdiv
  have hendpoint_nonneg : 0 ≤ d * (w / 2) :=
    mul_nonneg (le_of_lt hd_pos)
      (div_nonneg (le_of_lt hw_pos) (le_of_lt zero_lt_two))
  have hpi_div_two_le_pi : π / 2 ≤ π :=
    div_le_self (le_of_lt Real.pi_pos) one_le_two
  have hendpoint_le_pi : d * (w / 2) ≤ π :=
    le_trans (le_of_lt hendpoint_lt_pi_div_two) hpi_div_two_le_pi
  have hcos_endpoint_le_abs :
      Real.cos (d * (w / 2)) ≤ Real.cos |θ| :=
    Real.cos_le_cos_of_nonneg_of_le_pi
      (abs_nonneg θ) hendpoint_le_pi htheta_abs


  have hcos_abs :
      Real.cos |θ| = Real.cos θ :=
    Real.cos_abs θ
  have hcos_lower :
      Real.cos (d * (w / 2)) ≤ Real.cos θ :=
    Eq.subst
      (motive := fun y : ℝ => Real.cos (d * (w / 2)) ≤ y)
      hcos_abs
      hcos_endpoint_le_abs
  have hcosh_lower :
      Real.exp (d * z.im) / 2 ≤ Real.cosh (d * z.im) :=
    real_exp_half_le_cosh (d * z.im)
  have hcos_endpoint_pos :
      0 < Real.cos (d * (w / 2)) := by
    have hangle_abs : |d * (w / 2)| < π / 2 :=
      Eq.subst
        (motive := fun y : ℝ => |y| < π / 2)
        (abs_of_nonneg hendpoint_nonneg).symm
        hendpoint_lt_pi_div_two
    exact Real.cos_pos_of_mem_Ioo (abs_lt.mp hangle_abs)
  have hcos_endpoint_nonneg :
      0 ≤ Real.cos (d * (w / 2)) :=
    le_of_lt hcos_endpoint_pos
  have hcosh_nonneg :
      0 ≤ Real.cosh (d * z.im) :=
    le_of_lt (Real.cosh_pos (d * z.im))
  have hmul_lower :
      (Real.cos (d * (w / 2)) / 2) * Real.exp (d * z.im) ≤
        Real.cos θ * Real.cosh (d * z.im) := by
    have hleft_assoc :
        (Real.cos (d * (w / 2)) / 2) * Real.exp (d * z.im) =
          Real.cos (d * (w / 2)) * (Real.exp (d * z.im) / 2) := by
      calc
        (Real.cos (d * (w / 2)) / 2) * Real.exp (d * z.im) =
            (Real.cos (d * (w / 2)) * (1 / 2)) *
              Real.exp (d * z.im) := by
          exact congrArg
            (fun y : ℝ => y * Real.exp (d * z.im))
            (div_eq_mul_one_div (Real.cos (d * (w / 2))) 2)
        _ =
            Real.cos (d * (w / 2)) *
              ((1 / 2) * Real.exp (d * z.im)) :=
          mul_assoc (Real.cos (d * (w / 2))) (1 / 2)
            (Real.exp (d * z.im))
        _ =
            Real.cos (d * (w / 2)) *
              (Real.exp (d * z.im) / 2) := by
          exact congrArg
            (fun y : ℝ => Real.cos (d * (w / 2)) * y)
            (Eq.trans
              (mul_comm (1 / 2) (Real.exp (d * z.im)))
              (div_eq_mul_one_div (Real.exp (d * z.im)) 2).symm)
    have hfirst :
        Real.cos (d * (w / 2)) * (Real.exp (d * z.im) / 2) ≤
          Real.cos (d * (w / 2)) * Real.cosh (d * z.im) :=
      mul_le_mul_of_nonneg_left hcosh_lower hcos_endpoint_nonneg
    have hsecond :
        Real.cos (d * (w / 2)) * Real.cosh (d * z.im) ≤
          Real.cos θ * Real.cosh (d * z.im) :=
      mul_le_mul_of_nonneg_right hcos_lower hcosh_nonneg
    exact
      Eq.subst
        (motive := fun y : ℝ =>
          y ≤ Real.cos θ * Real.cosh (d * z.im))
        hleft_assoc.symm
        (le_trans hfirst hsecond)
  have hkernel_eq :
      (verticalStripSubcriticalCosineBarrierKernel a b d z).re =
        Real.cos θ * Real.cosh (d * z.im) :=
    verticalStripSubcriticalCosineBarrierKernel_re_eq_cos_mul_cosh
      a b d z
  exact
    Eq.subst
      (motive := fun y : ℝ =>
        (Real.cos (d * ((b - a) / 2)) / 2) *
            Real.exp (d * z.im) ≤ y)
      hkernel_eq.symm
      hmul_lower


end
end LFunctions
end Boundary

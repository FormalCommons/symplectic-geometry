/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.Distribution.LinearEquiv
public import SymplecticGeometry.Analysis.Distribution.OfFun
public import TauCeti.Analysis.Distribution.Restriction
public import TauCeti.Analysis.Distribution.SingularSupport
import TauCeti.MeasureTheory.Function.LocalRepresentative

/-!
# Coordinate distributions of a vector-valued locally integrable function

Let `w : E → F` be locally integrable on an open set `U` of a finite-dimensional real normed
space `E`, for a measure `μ`, with values in a finite-dimensional real space `F` with a basis `b`.
Let `e : E ≃L[ℝ] E'` be a continuous linear equivalence and `Ω ⊆ E'` an open set with
`e⁻¹ '' Ω ⊆ U`. The `i`-th coordinate distribution of `w` is the complex distribution

`Distribution.coordOfFun e hΩ b w μ i : φ ↦ ∫ x, φ (e x) • b.repr (w x) i ∂μ`

on `Ω`, the transport along `e⁻¹` (`Distribution.transportCLM`) of the distribution of the `i`-th
coordinate of `w`. For `E' = CoordinateSpace n` these are the families `ι → 𝓓'(Ω, ℂ)` to which
the interior regularity of elliptic systems applies.

## Main results

* `MeasureTheory.LocallyIntegrableOn.ofReal_basis_repr`: the coordinates of a locally integrable
  function, as complex functions, are locally integrable.
* `Distribution.coordOfFun_apply`: the pairing with a test function is an integral over `E`.
* `Distribution.coordOfFun_zero`, `Distribution.coordOfFun_neg`, `Distribution.coordOfFun_add`,
  `Distribution.coordOfFun_sub`, `Distribution.coordOfFun_smul`,
  `Distribution.coordOfFun_congr_ae`: linearity, and independence of the representative of `w`.
* `Distribution.restrictCLM_coordOfFun`: restricting to a smaller open set gives the coordinate
  distributions there.
* `Distribution.lineDerivOp_coordOfFun`, `Distribution.iteratedLineDerivOp_coordOfFun`: for an
  additive Haar measure and `w` of class `C¹` (resp. `C^k`) on `U`, the derivative along `v` of
  the coordinate distributions is that of `x ↦ fderiv ℝ w x (e⁻¹ v)`, and the iterated derivative
  along `m` is that of `x ↦ iteratedFDeriv ℝ k w x (e⁻¹ ∘ m)`.
* `Distribution.smulLeftCLM_coordOfFun`: multiplying by a smooth function `g` on `E'` multiplies
  `w` by `g ∘ e`.
* `Distribution.coordOfFun_eq_sum_smulLeftCLM`: if a coordinate of `w` is, almost everywhere on
  `U`, a combination of the coordinates of another function `w'` with smooth coefficients read
  through `e`, the coordinate distribution of `w` is the same combination of those of `w'`.
* `Distribution.singularSupport_coordOfFun_eq_empty`: the coordinate distributions of a function
  smooth on `U` have empty singular support.
* `Distribution.exists_contDiffOn_ae_eq_of_singularSupport_coordOfFun_eq_empty`: if `e` maps `U`
  into `Ω` and every coordinate distribution has empty singular support, then `w` agrees almost
  everywhere on `U` with a function smooth on `U`.

For the last result, near each point the singular support hypothesis gives a function, smooth near
the image of the point, that represents the coordinate distribution for the volume of `E'`.
Changing variables along `e` (`Distribution.transportCLM_ofFun` and
`Distribution.transportCLM_ofFun_of_isAddHaarMeasure`) turns it into a smooth local representative
of the coordinate of `w` for `μ`, up to the constant factor relating the image of the volume to
`μ`; Mathlib's `Distribution.ofFun_injective` identifies the two, and Tau Ceti's
`TauCeti.exists_contDiffOn_ae_eq_of_locally` glues the local representatives. The same change of
variables, with Tau Ceti's `Distribution.singularSupport_ofFun_eq_empty`, shows that the
coordinate distributions of a smooth function have empty singular support
(`Distribution.singularSupport_coordOfFun_eq_empty`).

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §2.2 (singular
  support) and §6.1 (distributions under linear changes of variables).
-/

public section

open Set TopologicalSpace MeasureTheory Filter
open scoped Distributions LineDeriv ContDiff Topology

/-- The `i`-th coordinate of a locally integrable function with values in a finite-dimensional real
space, in a basis `b` and as a complex function, is locally integrable. -/
theorem MeasureTheory.LocallyIntegrableOn.ofReal_basis_repr {X F ι : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {μ : Measure X} {s : Set X} {w : X → F} (hw : LocallyIntegrableOn w s μ)
    (b : Module.Basis ι ℝ F) (i : ι) : LocallyIntegrableOn (fun x ↦ (b.repr (w x) i : ℂ)) s μ := by
  simpa [Function.comp_def] using
    (Complex.ofRealCLM.comp (b.coord i).toContinuousLinearMap).locallyIntegrableOn_comp hw

namespace Distribution

variable {E E' F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Opens E}
  {μ : Measure E} {w w' : E → F}

section NormedSpace

variable [NormedAddCommGroup E'] [NormedSpace ℝ E'] {Ω : Opens E'}

/-- The `i`-th **coordinate distribution** of `w : E → F` in the basis `b` of `F`, transported
along `e : E ≃L[ℝ] E'` to an open set `Ω ⊆ E'` whose image under `e⁻¹` lies in `U`: the complex
distribution `φ ↦ ∫ x, φ (e x) • b.repr (w x) i ∂μ` on `Ω`
(`Distribution.coordOfFun_apply`). -/
noncomputable def coordOfFun (e : E ≃L[ℝ] E') (hΩ : MapsTo e.symm Ω U) (b : Module.Basis ι ℝ F)
    (w : E → F) (μ : Measure E) (i : ι) : 𝓓'(Ω, ℂ) :=
  transportCLM e.symm hΩ (ofFun U (fun x ↦ (b.repr (w x) i : ℂ)) μ ⊤)

variable (e : E ≃L[ℝ] E') (hΩ : MapsTo e.symm Ω U) (b : Module.Basis ι ℝ F)

theorem coordOfFun_def (i : ι) :
    coordOfFun e hΩ b w μ i =
      transportCLM e.symm hΩ (ofFun U (fun x ↦ (b.repr (w x) i : ℂ)) μ ⊤) :=
  (rfl)

/-- The coordinate distributions depend only on the class of `w` almost everywhere on `U`. -/
theorem coordOfFun_congr_ae (h : w =ᵐ[μ.restrict U] w') (i : ι) :
    coordOfFun e hΩ b w μ i = coordOfFun e hΩ b w' μ i := by
  rw [coordOfFun_def, coordOfFun_def,
    ofFun_congr_ae (f' := fun x ↦ (b.repr (w' x) i : ℂ))
    (h.mono fun x hx ↦ by simp [hx])]

/-- The coordinate distributions of the zero function vanish. -/
@[simp]
theorem coordOfFun_zero (i : ι) : coordOfFun e hΩ b (0 : E → F) μ i = 0 := by
  rw [coordOfFun_def, ← map_zero (transportCLM e.symm hΩ), ← ofFun_zero]
  congr 2
  ext x
  simp

/-- The coordinate distributions of `-w` are the negatives of those of `w`. -/
@[simp]
theorem coordOfFun_neg (i : ι) : coordOfFun e hΩ b (-w) μ i = -coordOfFun e hΩ b w μ i := by
  rw [coordOfFun_def, coordOfFun_def, ← map_neg, ← ofFun_neg]
  congr 2
  ext x
  simp

/-- The coordinate distributions of `c • w` are `c` times those of `w`. -/
@[simp]
theorem coordOfFun_smul (c : ℝ) (i : ι) :
    coordOfFun e hΩ b (c • w) μ i = c • coordOfFun e hΩ b w μ i := by
  rw [coordOfFun_def, coordOfFun_def, ← map_smul, ← ofFun_smul]
  congr 2
  ext x
  simp

variable [FiniteDimensional ℝ F]

/-- The pairing of the `i`-th coordinate distribution of `w` with a test function `φ` on `Ω` is
`∫ x, φ (e x) • b.repr (w x) i ∂μ`. -/
theorem coordOfFun_apply (hw : LocallyIntegrableOn w U μ) (i : ι) (φ : 𝓓(Ω, ℝ)) :
    coordOfFun e hΩ b w μ i φ = ∫ x, φ (e x) • (b.repr (w x) i : ℂ) ∂μ := by
  rw [coordOfFun_def, transportCLM_apply, ofFun_apply (hw.ofReal_basis_repr b i)]
  simp

/-- The coordinate distributions of a sum of locally integrable functions are the sums of their
coordinate distributions. -/
@[simp]
theorem coordOfFun_add (hw : LocallyIntegrableOn w U μ) (hw' : LocallyIntegrableOn w' U μ)
    (i : ι) :
    coordOfFun e hΩ b (w + w') μ i = coordOfFun e hΩ b w μ i + coordOfFun e hΩ b w' μ i := by
  rw [coordOfFun_def, coordOfFun_def, coordOfFun_def, ← map_add,
    ← ofFun_add (hw.ofReal_basis_repr b i) (hw'.ofReal_basis_repr b i)]
  congr 2
  ext x
  simp

/-- The coordinate distributions of a difference of locally integrable functions are the
differences of their coordinate distributions. -/
theorem coordOfFun_sub (hw : LocallyIntegrableOn w U μ) (hw' : LocallyIntegrableOn w' U μ)
    (i : ι) :
    coordOfFun e hΩ b (w - w') μ i = coordOfFun e hΩ b w μ i - coordOfFun e hΩ b w' μ i := by
  rw [sub_eq_add_neg, coordOfFun_add e hΩ b hw hw'.neg, coordOfFun_neg, sub_eq_add_neg]

/-- On an open `Ω' ≤ Ω`, the restriction of the coordinate distributions of `w` on `Ω` is the
coordinate distributions of `w` on `Ω'`, read through any open `U'` that contains the image of
`Ω'` under `e⁻¹` and on which `w` is locally integrable. -/
theorem restrictCLM_coordOfFun {U' : Opens E} {Ω' : Opens E'} (hΩ' : MapsTo e.symm Ω' U')
    (h : Ω' ≤ Ω) (hw : LocallyIntegrableOn w U μ) (hw' : LocallyIntegrableOn w U' μ) (i : ι) :
    (restrictCLM (coordOfFun e hΩ b w μ i) : 𝓓'(Ω', ℂ)) = coordOfFun e hΩ' b w μ i := by
  ext φ
  rw [restrictCLM_apply, coordOfFun_apply e hΩ b hw, coordOfFun_apply e hΩ' b hw']
  simp [TestFunction.monoCLM_apply, h]

/-- The derivatives along `v` of the coordinate distributions of a function `w` of class `C¹` on
`U` are the coordinate distributions of its derivative `x ↦ fderiv ℝ w x (e⁻¹ v)`, for an
additive Haar measure. -/
theorem lineDerivOp_coordOfFun [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure]
    (hw : ContDiffOn ℝ 1 w U) (i : ι) (v : E') :
    ∂_{v} (coordOfFun e hΩ b w μ i) =
      coordOfFun e hΩ b (fun x ↦ fderiv ℝ w x (e.symm v)) μ i := by
  set L : F →L[ℝ] ℂ := Complex.ofRealCLM.comp (b.coord i).toContinuousLinearMap
  have hL : ∀ y, L y = (b.repr y i : ℂ) := fun y ↦ by simp [L]
  have hLw : (fun x ↦ (b.repr (w x) i : ℂ)) = L ∘ w := funext fun x ↦ (hL _).symm
  rw [coordOfFun_def, coordOfFun_def, lineDerivOp_transportCLM, hLw,
    lineDerivOp_ofFun (L.contDiff.comp_contDiffOn hw)]
  refine congrArg _ (ofFun_congr_ae ((ae_restrict_iff' U.isOpen.measurableSet).2
    (ae_of_all _ fun x hx ↦ ?_)))
  have hwx : DifferentiableAt ℝ w x :=
    (hw.differentiableOn one_ne_zero x hx).differentiableAt (U.isOpen.mem_nhds hx)
  dsimp only
  rw [(L.hasFDerivAt.comp x hwx.hasFDerivAt).fderiv]
  simp [hL]

/-- The iterated derivatives along `m : Fin k → E'` of the coordinate distributions of a function
`w` of class `C^k` on `U` are the coordinate distributions of
`x ↦ iteratedFDeriv ℝ k w x (e⁻¹ ∘ m)`, for an additive Haar measure. -/
theorem iteratedLineDerivOp_coordOfFun [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure]
    {k : ℕ} (hw : ContDiffOn ℝ k w U) (i : ι) (m : Fin k → E') :
    ∂^{m} (coordOfFun e hΩ b w μ i) =
      coordOfFun e hΩ b (fun x ↦ iteratedFDeriv ℝ k w x (e.symm ∘ m)) μ i := by
  induction k with
  | zero =>
    rw [LineDeriv.iteratedLineDerivOp_fin_zero]
    refine coordOfFun_congr_ae e hΩ b (ae_of_all _ fun x ↦ ?_) i
    simp
  | succ k ih =>
    have hwx : ∀ x ∈ U, ContDiffAt ℝ (k + 1 : ℕ) w x :=
      fun x hx ↦ hw.contDiffAt (U.isOpen.mem_nhds hx)
    -- The iterated derivative of order `k`, evaluated at a fixed family of vectors, is `C¹`.
    have hg : ∀ c : Fin k → E, ContDiffOn ℝ 1 (fun x ↦ iteratedFDeriv ℝ k w x c) U :=
      fun c x hx ↦ ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ E) F c).contDiff.contDiffAt
        |>.comp x ((hwx x hx).iteratedFDeriv_right (by norm_cast; omega))).contDiffWithinAt
    rw [LineDeriv.iteratedLineDerivOp_succ_left, ih (hw.of_le (by norm_cast; omega)),
      lineDerivOp_coordOfFun e hΩ b (hg _)]
    refine coordOfFun_congr_ae e hΩ b ((ae_restrict_iff' U.isOpen.measurableSet).2
      (ae_of_all _ fun x hx ↦ ?_)) i
    rw [iteratedFDeriv_succ_apply_left, ← fderiv_continuousMultilinear_apply_const_apply
      ((hwx x hx).differentiableAt_iteratedFDeriv (by norm_cast; omega))]
    simp [Fin.tail_def, Function.comp_def]

/-- Multiplying the coordinate distributions of `w` by a smooth function `g` on `E'` gives the
coordinate distributions of `x ↦ g (e x) • w x`. -/
theorem smulLeftCLM_coordOfFun [FiniteDimensional ℝ E] {g : E' → ℝ} (hg : ContDiff ℝ ∞ g)
    (hw : LocallyIntegrableOn w U μ) (i : ι) :
    smulLeftCLM hg (coordOfFun e hΩ b w μ i) = coordOfFun e hΩ b (fun x ↦ g (e x) • w x) μ i := by
  rw [coordOfFun_def, coordOfFun_def, smulLeftCLM_transportCLM,
    smulLeftCLM_ofFun _ (hw.ofReal_basis_repr b i)]
  congr 2
  ext x
  simp [Complex.real_smul]

omit [FiniteDimensional ℝ F] in
/-- **Changing coordinates.** If, almost everywhere on `U`, the `i`-th coordinate of `w` in `b` is
`∑ j, c j (e x) * b'.repr (w' x) j` for smooth functions `c j` on `E'` and a function `w'`
locally integrable on `U`, then the `i`-th coordinate distribution of `w` is the sum over `j`
of the coordinate distributions `coordOfFun e hΩ b' w' μ j` multiplied by `c j`. -/
theorem coordOfFun_eq_sum_smulLeftCLM [FiniteDimensional ℝ E] {F' ι' : Type*}
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F'] [Fintype ι']
    (b' : Module.Basis ι' ℝ F')
    {w' : E → F'} (hw' : LocallyIntegrableOn w' U μ) {c : ι' → E' → ℝ}
    (hc : ∀ j, ContDiff ℝ ∞ (c j)) (i : ι)
    (h : ∀ᵐ x ∂μ.restrict U, b.repr (w x) i = ∑ j, c j (e x) * b'.repr (w' x) j) :
    coordOfFun e hΩ b w μ i = ∑ j, smulLeftCLM (hc j) (coordOfFun e hΩ b' w' μ j) := by
  set f : ι' → E → ℂ := fun j x ↦ (b'.repr (c j (e x) • w' x) j : ℂ)
  have hf (j : ι') : LocallyIntegrableOn (f j) U μ :=
    (hw'.continuousOn_smul U.isOpen.isLocallyClosed
      ((hc j).continuous.comp e.continuous).continuousOn).ofReal_basis_repr b' j
  simp only [smulLeftCLM_coordOfFun e hΩ b' (hc _) hw']
  simp only [coordOfFun_def, ← map_sum]
  rw [← ofFun_sum _ fun j _ ↦ hf j]
  congr 1
  refine ofFun_congr_ae (h.mono fun x hx ↦ ?_)
  simp [f, hx]

end NormedSpace

section InnerProductSpace

variable [FiniteDimensional ℝ E] [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
  [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E'] [FiniteDimensional ℝ F]
  {Ω : Opens E'} [μ.IsAddHaarMeasure]
  (e : E ≃L[ℝ] E') (hΩ : MapsTo e.symm Ω U) (b : Module.Basis ι ℝ F)

/-- Near a point `x` that `e` sends into `Ω` but outside the singular support of the `i`-th
coordinate distribution, the `i`-th coordinate of `w` agrees almost everywhere with a smooth
function. -/
private theorem exists_contDiffOn_ae_eq_repr (hw : LocallyIntegrableOn w U μ) (i : ι) {x : E}
    (hx : e x ∈ Ω) (hsing : e x ∉ (coordOfFun e hΩ b w μ i).singularSupport) :
    ∃ N ∈ 𝓝 x, ∃ g : E → ℂ, ContDiffOn ℝ ∞ g N ∧
      (fun x ↦ (b.repr (w x) i : ℂ)) =ᵐ[μ.restrict N] g := by
  obtain ⟨V, hV, hxV, f, hf, hT⟩ := (notMem_singularSupport_iff hx).1 hsing
  have hwi := hw.ofReal_basis_repr b i
  set W : Opens E' := ⟨V ∩ Ω, hV.inter Ω.isOpen⟩
  set O : Opens E := ⟨e ⁻¹' W, W.isOpen.preimage e.continuous⟩
  have hOU : MapsTo (e.trans e.symm) O U := fun z hz ↦ by simpa using hΩ hz.2
  have hOW : MapsTo e O W := fun _ hz ↦ hz
  have hO : ∀ {z}, z ∈ O → e z ∈ V ∧ e z ∈ Ω := fun hz ↦ by simpa [O, W] using hz
  have hOΩ : MapsTo e O Ω := fun _ hz ↦ (hO hz).2
  have hfW : LocallyIntegrableOn f W :=
    (hf.mono inter_subset_left).continuousOn.locallyIntegrableOn W.isOpen.measurableSet
  -- The factor relating the image of the volume of `E'` under `e⁻¹` to `μ`.
  set κ : ℝ := (((volume : Measure E').map e.symm).addHaarScalarFactor μ : ℝ)
  have hfe : ContDiffOn ℝ ∞ (fun z ↦ κ • f (e z)) O :=
    (hf.comp e.contDiff.contDiffOn fun _ hz ↦ (hO hz).1).const_smul _
  refine ⟨O, O.isOpen.mem_nhds ⟨hxV, hx⟩, _, hfe, ofFun_injective (n := ⊤)
    (hwi.mono_set fun z hz ↦ by simpa using hOU hz)
    (hfe.continuousOn.locallyIntegrableOn O.isOpen.measurableSet) ?_⟩
  -- Both sides are transports along `e`: the left one of the coordinate distribution, the right
  -- one of the distribution of `f` on `W`.
  have h₁ : ofFun O (fun x ↦ (b.repr (w x) i : ℂ)) μ ⊤ =
      transportCLM e hOΩ (coordOfFun e hΩ b w μ i) := by
    rw [coordOfFun_def, ← transportCLM_trans e e.symm hOΩ hΩ hOU, transportCLM_ofFun _ _ hwi]
    simp
  have h₂ : ofFun O (fun z ↦ κ • f (e z)) μ ⊤ = transportCLM e hOW (ofFun W f volume ⊤) := by
    rw [transportCLM_ofFun_of_isAddHaarMeasure e hOW volume μ hfW, ← ofFun_smul, Pi.smul_def]
  rw [h₁, h₂]
  ext ψ
  -- Both test functions on `E'` are `ψ ∘ e⁻¹`.
  have hφ : ∀ (W' : Opens E') (h : MapsTo e O W'),
      ⇑(e.transportTestFunction h ψ) = ψ ∘ e.symm :=
    fun _ _ ↦ funext fun y ↦ by simp
  have hψ : tsupport (e.transportTestFunction hOΩ ψ) ⊆ V := by
    rw [hφ]
    refine (tsupport_comp_subset_preimage _ e.symm.continuous).trans fun y hy ↦ ?_
    simpa using (hO (ψ.tsupport_subset hy)).1
  rw [transportCLM_apply, transportCLM_apply, hT _ hψ, ofFun_apply hfW, hφ, hφ]

/-- **Smooth representatives from coordinate distributions.** If `e` maps `U` into `Ω` and every
coordinate distribution of `w`, locally integrable on `U` for an additive Haar measure, has empty
singular support, then `w` agrees almost everywhere on `U` with a function smooth on `U`. -/
theorem exists_contDiffOn_ae_eq_of_singularSupport_coordOfFun_eq_empty
    (hU : MapsTo e U Ω) (hw : LocallyIntegrableOn w U μ)
    (h : ∀ i, (coordOfFun e hΩ b w μ i).singularSupport = ∅) :
    ∃ g : E → F, ContDiffOn ℝ ∞ g U ∧ w =ᵐ[μ.restrict U] g := by
  have := Module.Finite.finite_basis b
  have := Fintype.ofFinite ι
  -- Glue the local smooth representatives of each coordinate.
  choose g hg hwg using fun i ↦ TauCeti.exists_contDiffOn_ae_eq_of_locally (μ := μ)
    (Ω := (U : Set E)) fun x hx ↦
      exists_contDiffOn_ae_eq_repr e hΩ b hw i (hU hx) (by simp [h i])
  refine ⟨fun x ↦ ∑ i, (g i x).re • b i,
    ContDiffOn.sum fun i _ ↦ (Complex.reCLM.contDiff.comp_contDiffOn (hg i)).smul contDiffOn_const,
    ?_⟩
  filter_upwards [ae_all_iff.2 hwg] with x hx
  conv_lhs => rw [← b.sum_repr (w x)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← hx i, Complex.ofReal_re]

/-- The coordinate distributions of a function smooth on `U` have empty singular support. -/
theorem singularSupport_coordOfFun_eq_empty (hw : ContDiffOn ℝ ∞ w U) (i : ι) :
    (coordOfFun e hΩ b w μ i).singularSupport = ∅ := by
  have hc : ContDiffOn ℝ ∞ (fun z ↦ (b.repr (w (e.symm z)) i : ℂ)) Ω :=
    (Complex.ofRealCLM.comp (b.coord i).toContinuousLinearMap).contDiff.comp_contDiffOn
      (hw.comp e.symm.contDiff.contDiffOn fun z hz ↦ hΩ hz)
  -- After the change of variables `x = e⁻¹ z`, it is a multiple of the distribution of a function
  -- smooth on `Ω`.
  rw [coordOfFun_def, transportCLM_ofFun_of_isAddHaarMeasure e.symm hΩ μ volume
    ((hw.continuousOn.locallyIntegrableOn U.isOpen.measurableSet).ofReal_basis_repr b i)]
  exact subset_empty_iff.1 ((singularSupport_smul_subset _ _).trans
    (singularSupport_ofFun_eq_empty hc).subset)

end InnerProductSpace

end Distribution

end

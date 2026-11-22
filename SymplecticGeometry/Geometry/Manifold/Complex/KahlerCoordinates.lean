/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Integrable
public import SymplecticGeometry.Geometry.Manifold.DeRham.Hodge.Chart
public import TauCeti.Analysis.Calculus.InverseFunctionTheorem
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
public import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Osculating holomorphic charts of a Kähler manifold

Let `J` be an integrable almost complex structure on a manifold `M` modelled on `E`, let `ω` be a
closed two-form, and let the Riemannian metric be `g(v, w) = ω(v, J w)`. Every point `x₀` lies in
the source of a chart `ψ` in which `J` is a constant linear complex structure `J₀` of `E` and in
which the metric, read in the chart as `SymplecticGeometry.gramInChart ψ`, has derivative zero at
`ψ x₀`.

The chart is an integrable chart `φ` followed by the quadratic map
`Φ(z) = z + Q(z - z₀, z - z₀) / 2`, where `z₀ = φ x₀` and `Q` is symmetric and complex bilinear for
`J₀`. The derivative of `Φ` at `z` is `id + Q(z - z₀, ·)`, which commutes with `J₀`, so `J` is still
`J₀` in the new chart. Let `g₀` be the metric in `φ` at `z₀` and `A` its derivative there. Since
`Φ` fixes `z₀` with derivative the identity, the derivative of the metric in the new chart at `z₀`
is `A(h)(u, v) - g₀(Q(h, u), v) - g₀(u, Q(h, v))`. A `Q` for which this vanishes is given by
`g₀(Q(h, u), v) = (A(h)(u, v) + A(J₀ h)(u, J₀ v)) / 2`: the form `A` is symmetric and
`J₀`-invariant in its last two arguments, because `g` is, and closedness of `ω` gives the cyclic
identity that makes `Q` symmetric. This linear algebra is
`TauCeti.AlmostComplexStructure.exists_symm_complexBilinear_apply_add_apply_eq`.

## Main results

* `TauCeti.AlmostComplexStructure.exists_symm_complexBilinear_apply_add_apply_eq`: the symmetric
  complex bilinear map `Q` above, for a nondegenerate symmetric `J`-invariant form `G₀` and a
  trilinear form `A` with the symmetries of the derivative of a Kähler metric.
* `SymplecticGeometry.gramInChart_apply_eq_mpullback_symm_apply`: in a chart in which `J` is `J₀`,
  the metric `g(v, w) = ω(v, J w)` is `(u, v) ↦ ω(u, J₀ v)`, with `ω` read in the chart.
* `IsIntegrable.exists_partialDiffeomorph_fderiv_gramInChart_eq_zero`, in the namespace
  `TauCeti.SmoothAlmostComplexStructure`: osculating holomorphic charts.

## Implementation notes

The fibres of the tangent bundle get their inner product spaces from the scoped instances of
`Bundle`, which are costly: with them open, elaborating statements about derivatives of
`gramInChart ψ : E → E →L[ℝ] E →L[ℝ] ℝ` can time out. They are opened only for the declarations
whose statements involve the inner product, and the computation in coordinates is a private lemma
that takes the smoothness of the metric in charts as a hypothesis.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 0, §7.
-/

public section

noncomputable section

open Set Filter
open scoped Manifold Topology ContDiff RealInnerProductSpace

namespace TauCeti.AlmostComplexStructure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Let `J` be a linear complex structure on `E`, let `G₀` be a nondegenerate symmetric bilinear
form with `G₀ (J u) (J v) = G₀ u v`, and let `A` be a trilinear form, symmetric and `J`-invariant in
its last two arguments, with `A h u (J v) - A u h (J v) + A v h (J u) = 0`. Then there is a
symmetric bilinear map `Q` with `Q h (J u) = J (Q h u)` such that
`G₀ (Q h u) v + G₀ u (Q h v) = A h u v`.

For the derivative `A` at a point of a Kähler metric `G` written in holomorphic coordinates, the
cyclic identity is the closedness of the Kähler form, and `Q` is the quadratic part of a
holomorphic change of coordinates that kills the first derivative of the metric. -/
theorem exists_symm_complexBilinear_apply_add_apply_eq (J : AlmostComplexStructure E)
    (G₀ : E →L[ℝ] E →L[ℝ] ℝ) (hG₀ : ∀ v, (∀ w, G₀ v w = 0) → v = 0)
    (hGs : ∀ u v, G₀ u v = G₀ v u) (hGJ : ∀ u v, G₀ (J u) (J v) = G₀ u v)
    (A : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (hA : ∀ h u v, A h u v = A h v u)
    (hAJ : ∀ h u v, A h (J u) (J v) = A h u v)
    (hd : ∀ h u v, A h u (J v) - A u h (J v) + A v h (J u) = 0) :
    ∃ Q : E →L[ℝ] E →L[ℝ] E, (∀ h u, Q h u = Q u h) ∧ (∀ h u, Q h (J u) = J (Q h u)) ∧
      ∀ h u v, G₀ (Q h u) v + G₀ u (Q h v) = A h u v := by
  set B : LinearMap.BilinForm ℝ E := G₀.toLinearMap₁₂
  have hBl : B.SeparatingLeft := hG₀
  have hB : B.Nondegenerate := ⟨hBl, fun y hy ↦ hBl y fun x ↦ by
    rw [← hy x]; exact hGs y x⟩
  -- The trilinear form that `G₀ (Q h u) ·` must be.
  let T : E →ₗ[ℝ] E →ₗ[ℝ] Module.Dual ℝ E := LinearMap.mk₂ ℝ
    (fun h u ↦ (1 / 2 : ℝ) • ((A h u).toLinearMap + (A (J h) u).toLinearMap ∘ₗ J.toLinearMap))
    (fun h h' u ↦ by ext v; simp [J.apply_add]; ring)
    (fun c h u ↦ by ext v; simp [J.apply_smul]; ring)
    (fun h u u' ↦ by ext v; simp; ring)
    (fun c h u ↦ by ext v; simp; ring)
  let Ql : E →ₗ[ℝ] E →ₗ[ℝ] E := T.compr₂ (B.toDual hB).symm.toLinearMap
  let Q : E →L[ℝ] E →L[ℝ] E := LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] E) ≃ₗ[ℝ] (E →L[ℝ] E)).toLinearMap ∘ₗ Ql)
  have hQ (h u v : E) : G₀ (Q h u) v = 2⁻¹ * A h u v + 2⁻¹ * A (J h) u (J v) := by
    have := LinearMap.BilinForm.apply_toDual_symm_apply (hB := hB) (T h u) v
    simp only [Q, Ql, T, B] at this ⊢
    simpa [mul_add] using this
  have hinj {x y : E} (h : ∀ v, G₀ x v = G₀ y v) : x = y := by
    rw [← sub_eq_zero]
    exact hBl _ fun v ↦ by simp [B, h v]
  have hGJ' (x v : E) : G₀ (J x) v = - G₀ x (J v) := by
    simpa [J.apply_apply] using (hGJ (J x) v).symm
  -- Symmetry of `Q`, from the cyclic identity.
  have hsymm (h u : E) : Q h u = Q u h := by
    refine hinj fun v ↦ ?_
    rw [hQ, hQ]
    have h1 := hd h u (J v)
    have h2 := hd (J u) h v
    have h3 := hd (J h) u v
    have h4 := hd (J v) h u
    have e1 := hA v (J u) (J h)
    have e2 := hA h (J v) (J u)
    have e3 := hA u (J v) (J h)
    simp only [J.apply_apply, map_neg] at h1
    linarith
  have hJl (h u : E) : Q (J h) u = J (Q h u) := by
    refine hinj fun v ↦ ?_
    rw [hQ, hGJ', hQ]
    simp [J.apply_apply]
  refine ⟨Q, hsymm, fun h u ↦ by rw [hsymm, hJl, hsymm], fun h u v ↦ ?_⟩
  rw [hGs u, hQ, hQ]
  have e1 := hAJ (J h) v (J u)
  have e2 := hA (J h) (J v) u
  have e3 := hA h v u
  simp only [J.apply_apply, map_neg] at e1
  linarith

end TauCeti.AlmostComplexStructure

namespace SymplecticGeometry

open TauCeti

section Metric

open Bundle

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- Let the metric be `g(v, w) = ω(v, J w)`, and let `φ` be a chart in which `J` is a constant
linear structure `J₀`. Then on the target of `φ` the metric in the chart is `(u, v) ↦ ω(u, J₀ v)`,
with `ω` read in the chart. -/
theorem gramInChart_apply_eq_mpullback_symm_apply {J : SmoothAlmostComplexStructure I M}
    {form : SmoothTwoForm I M}
    (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = form.val x ![v, J x w])
    (φ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) {J₀ : AlmostComplexStructure E}
    (hφ : ∀ p ∈ φ.target, ∀ w : E, J.chartPushforward φ.toOpenPartialHomeomorph p w = J₀ w)
    {z : E} (hz : z ∈ φ.target) (u v : E) :
    gramInChart φ z u v = mpullback 𝓘(ℝ, E) I φ.symm form.val z ![u, J₀ v] := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hs : φ.symm z ∈ φ.source := φ.map_target hz
  -- `J` read through the inverse of the chart is `J₀`.
  have hJ : J (φ.symm z) (mfderiv 𝓘(ℝ, E) I φ.symm z v) =
      mfderiv 𝓘(ℝ, E) I φ.symm z (J₀ v) := by
    have h1 := (J.forall_chartPushforward_apply_eq_iff φ J₀).1 hφ _ hs
      (mfderiv 𝓘(ℝ, E) I φ.symm z v)
    rw [φ.mfderiv_apply_mfderiv_symm_apply hn hz v] at h1
    have h2 := φ.mfderiv_symm_apply_mfderiv_apply hn hs
      (J (φ.symm z) (mfderiv 𝓘(ℝ, E) I φ.symm z v))
    have hr : φ (φ.symm z) = z := φ.right_inv hz
    rw [← h1]
    convert h2.symm using 2
    rw [hr]
  rw [gramInChart_apply, hg, hJ]
  refine Eq.trans ?_ (TauCeti.mpullback_apply _ _ _ _).symm
  congr 1
  ext i
  fin_cases i <;> rfl

end Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]

omit [FiniteDimensional ℝ E] in
/-- The symmetries of the derivative `A` at `z₀` of the metric `G` in a chart `φ` in which `G` is
`(u, v) ↦ ω(u, J₀ v)` for a closed form `ω`: `A` is symmetric and `J₀`-invariant in its last two
arguments, and it satisfies the cyclic identity that comes from `dω = 0`. -/
private theorem fderiv_gramInChart_symmetries {form : SmoothTwoForm I M} (hform : form.IsClosed)
    (φ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) {J₀ : AlmostComplexStructure E}
    (hc : ContDiffOn ℝ ∞ (gramInChart φ) φ.target)
    (hGΩ : ∀ z ∈ φ.target, ∀ u v : E,
      gramInChart φ z u v = mpullback 𝓘(ℝ, E) I φ.symm form.val z ![u, J₀ v])
    {z₀ : E} (hz₀ : z₀ ∈ φ.target) :
    (∀ u v, gramInChart φ z₀ (J₀ u) (J₀ v) = gramInChart φ z₀ u v) ∧
      (∀ h u v, fderiv ℝ (gramInChart φ) z₀ h u v = fderiv ℝ (gramInChart φ) z₀ h v u) ∧
      (∀ h u v, fderiv ℝ (gramInChart φ) z₀ h (J₀ u) (J₀ v) =
        fderiv ℝ (gramInChart φ) z₀ h u v) ∧
      ∀ h u v, fderiv ℝ (gramInChart φ) z₀ h u (J₀ v) - fderiv ℝ (gramInChart φ) z₀ u h (J₀ v) +
        fderiv ℝ (gramInChart φ) z₀ v h (J₀ u) = 0 := by
  set Ω : E → E [⋀^Fin 2]→L[ℝ] ℝ := mpullback 𝓘(ℝ, E) I φ.symm form.val
  set G := gramInChart φ with hG
  have hGJ (z : E) (hz : z ∈ φ.target) (u v : E) : G z (J₀ u) (J₀ v) = G z u v :=
    calc G z (J₀ u) (J₀ v) = Ω z ![J₀ u, J₀ (J₀ v)] := hGΩ z hz _ _
      _ = - Ω z ![J₀ (J₀ v), J₀ u] := ContinuousAlternatingMap.apply_vecCons_swap _ _ _
      _ = - G z (J₀ (J₀ v)) u := congrArg Neg.neg (hGΩ z hz _ _).symm
      _ = G z u v := by
        rw [J₀.apply_apply]
        simp [hG, gramInChart_comm φ z v u]
  have hGd : DifferentiableAt ℝ G z₀ :=
    (hc.contDiffAt (φ.open_target.mem_nhds hz₀)).differentiableAt (by simp)
  set A := fderiv ℝ G z₀ with hAdef
  -- Comparing derivatives of an entry of `G` with those of a function equal to it near `z₀`.
  have hder (u v : E) {f : E → ℝ} {f' : E →L[ℝ] ℝ} (hf : HasFDerivAt f f' z₀)
      (he : (fun z ↦ G z u v) =ᶠ[𝓝 z₀] f) (h : E) : A h u v = f' h := by
    have hd := (hGd.hasFDerivAt.clm_apply (hasFDerivAt_const u z₀)).clm_apply
      (hasFDerivAt_const v z₀)
    have := congrArg (· h) ((hd.congr_of_eventuallyEq he.symm).unique hf)
    simpa using this
  refine ⟨hGJ z₀ hz₀, fun h u v ↦ ?_, fun h u v ↦ ?_, fun h u v ↦ ?_⟩
  · have := hder u v ((hGd.hasFDerivAt.clm_apply (hasFDerivAt_const v z₀)).clm_apply
      (hasFDerivAt_const u z₀)) (Eventually.of_forall fun z ↦ gramInChart_comm φ z u v) h
    simpa using this
  · have := hder (J₀ u) (J₀ v) ((hGd.hasFDerivAt.clm_apply (hasFDerivAt_const u z₀)).clm_apply
      (hasFDerivAt_const v z₀))
      (eventually_of_mem (φ.open_target.mem_nhds hz₀) fun z hz ↦ hGJ z hz u v) h
    simpa using this
  · -- The closedness of `form`, read in the chart, as a cyclic identity for `A`.
    have hΩd : DifferentiableAt ℝ Ω z₀ :=
      ((SmoothForm.contDiffOn_mpullback form φ.open_target φ.symm.contMDiffOn).contDiffAt
        (φ.open_target.mem_nhds hz₀)).differentiableAt (by simp)
    have hcl : extDeriv Ω z₀ = 0 := SmoothForm.IsClosed.extDeriv_mpullback_eq_zero hform
      ((φ.symm.contMDiffOn.contMDiffAt (φ.open_target.mem_nhds hz₀)).of_le (by simp))
    have hΩe (a b k : E) : fderiv ℝ (fun z ↦ Ω z ![a, b]) z₀ k = - A k a (J₀ b) := by
      have he : (fun z ↦ Ω z ![a, b]) =ᶠ[𝓝 z₀] fun z ↦ - G z a (J₀ b) :=
        eventually_of_mem (φ.open_target.mem_nhds hz₀) fun z hz ↦ by
          have hb : J₀ (-(J₀ b)) = b := by rw [map_neg, J₀.apply_apply, neg_neg]
          have := hGΩ z hz a (-(J₀ b))
          rw [hb, map_neg] at this
          exact this.symm
      have hd := ((hGd.hasFDerivAt.clm_apply (hasFDerivAt_const a z₀)).clm_apply
        (hasFDerivAt_const (J₀ b) z₀)).neg
      rw [he.fderiv_eq]
      refine (congrArg (· k) hd.fderiv).trans ?_
      simp [hAdef]
    have h0 := congrArg (fun T ↦ T ![h, u, v]) hcl
    have r0 : Fin.removeNth 0 ![h, u, v] = ![u, v] := by ext i; fin_cases i <;> rfl
    have r1 : Fin.removeNth 1 ![h, u, v] = ![h, v] := by ext i; fin_cases i <;> rfl
    have r2 : Fin.removeNth 2 ![h, u, v] = ![h, u] := by ext i; fin_cases i <;> rfl
    rw [extDeriv_apply hΩd, Fin.sum_univ_three, r0, r1, r2] at h0
    simp only [Int.reduceNeg, Nat.reduceAdd, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
      pow_zero, Nat.succ_eq_add_one, Matrix.cons_val_zero, hΩe, smul_neg, one_smul, Nat.one_mod,
      pow_one, Matrix.cons_val_one, neg_smul, neg_neg, Nat.mod_succ, even_two, Even.neg_pow,
      one_pow, Matrix.cons_val, ContinuousAlternatingMap.coe_zero, Pi.zero_apply] at h0
    linarith

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- Let `Θ` be a partial diffeomorphism of `E` that fixes `z₀ ∈ φ.target`, with derivative
`id + Q (z - z₀)` at every `z`. If `G (Q h u) v + G u (Q h v) = A h u v`, where `G` is the metric in
the chart `φ` at `z₀` and `A` its derivative there, then the metric in the chart `φ.trans Θ` has
derivative zero at `z₀`. -/
private theorem fderiv_gramInChart_trans_eq_zero (φ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞)
    (Θ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (Q : E →L[ℝ] E →L[ℝ] E) {z₀ : E}
    (hz₀ : z₀ ∈ φ.target) (hz₀Θ : z₀ ∈ Θ.source) (hΘz₀ : Θ z₀ = z₀)
    (hΘd : ∀ z, HasFDerivAt Θ (ContinuousLinearMap.id ℝ E + Q (z - z₀)) z)
    (hGd : DifferentiableAt ℝ (gramInChart φ) z₀)
    (hG'd : DifferentiableAt ℝ (gramInChart (φ.trans Θ)) z₀)
    (hQ : ∀ h u v, gramInChart φ z₀ (Q h u) v + gramInChart φ z₀ u (Q h v) =
      fderiv ℝ (gramInChart φ) z₀ h u v) :
    fderiv ℝ (gramInChart (φ.trans Θ)) z₀ = 0 := by
  set G := gramInChart φ
  set G' := gramInChart (φ.trans Θ)
  -- Near `z₀`, `G` is the pullback of `G'` by `Θ`.
  have hid : ∀ᶠ z in 𝓝 z₀, ∀ u v, G z u v =
      G' (Θ z) ((ContinuousLinearMap.id ℝ E + Q (z - z₀)) u)
        ((ContinuousLinearMap.id ℝ E + Q (z - z₀)) v) := by
    filter_upwards [φ.open_target.mem_nhds hz₀, Θ.open_source.mem_nhds hz₀Θ] with z hz hzΘ u v
    have hl : Θ.symm (Θ z) = z := Θ.left_inv hzΘ
    have := gramInChart_trans_apply φ Θ (Θ.map_source hzΘ) (by rw [hl]; exact hz) u v
    rw [hl, (hΘd z).fderiv] at this
    exact this.symm
  have hG'z₀ (u v : E) : G' z₀ u v = G z₀ u v := by
    have := hid.self_of_nhds u v
    simpa [hΘz₀] using this.symm
  have hΘ' : HasFDerivAt (fun z ↦ G' (Θ z))
      ((fderiv ℝ G' z₀).comp (ContinuousLinearMap.id ℝ E + Q (z₀ - z₀))) z₀ :=
    (show HasFDerivAt G' (fderiv ℝ G' z₀) (Θ z₀) by
      rw [hΘz₀]; exact hG'd.hasFDerivAt).comp z₀ (hΘd z₀)
  have hD (w : E) : HasFDerivAt (fun z ↦ (ContinuousLinearMap.id ℝ E + Q (z - z₀)) w)
      (Q.flip w) z₀ := by
    have h1 := Q.hasFDerivAt.comp z₀ ((hasFDerivAt_id z₀).sub_const z₀)
    refine (((hasFDerivAt_const (ContinuousLinearMap.id ℝ E) z₀).add h1).clm_apply
      (hasFDerivAt_const w z₀)).congr_fderiv ?_
    ext k
    simp
  ext h u v
  -- Differentiate both sides of `hid` at `z₀`.
  have hf := (hΘ'.clm_apply (hD u)).clm_apply (hD v)
  have hd := (hGd.hasFDerivAt.clm_apply (hasFDerivAt_const u z₀)).clm_apply
    (hasFDerivAt_const v z₀)
  have hev : (fun z ↦ G z u v) =ᶠ[𝓝 z₀] fun z ↦ G' (Θ z)
      ((ContinuousLinearMap.id ℝ E + Q (z - z₀)) u) ((ContinuousLinearMap.id ℝ E + Q (z - z₀)) v) :=
    hid.mono fun z hz ↦ hz u v
  have := congrArg (· h) ((hd.congr_of_eventuallyEq hev.symm).unique hf)
  simp only [sub_self, map_zero, add_zero, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_id, ContinuousLinearMap.flip_add, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, zero_apply, hΘz₀,
    hG'z₀] at this ⊢
  linarith [hQ h u v]

/-- The construction of an osculating chart from a chart `φ` in which `J` is `J₀` and in which the
metric is `(u, v) ↦ ω(u, J₀ v)` for a closed form `ω`. The smoothness of the metric in charts
is a hypothesis, so that the proof runs without the scoped instances of `Bundle`. -/
private theorem exists_partialDiffeomorph_fderiv_gramInChart_eq_zero_aux
    (hc : ∀ ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞, ContDiffOn ℝ ∞ (gramInChart ψ) ψ.target)
    {J : SmoothAlmostComplexStructure I M} {form : SmoothTwoForm I M} (hform : form.IsClosed)
    (φ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) {J₀ : AlmostComplexStructure E}
    (hφJ : ∀ p ∈ φ.target, ∀ w : E, J.chartPushforward φ.toOpenPartialHomeomorph p w = J₀ w)
    {x₀ : M} (hx₀ : x₀ ∈ φ.source)
    (hGΩ : ∀ z ∈ φ.target, ∀ u v : E,
      gramInChart φ z u v = mpullback 𝓘(ℝ, E) I φ.symm form.val z ![u, J₀ v]) :
    ∃ (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (J₀ : AlmostComplexStructure E),
      x₀ ∈ ψ.source ∧
        (∀ p ∈ ψ.target, ∀ w : E, J.chartPushforward ψ.toOpenPartialHomeomorph p w = J₀ w) ∧
        fderiv ℝ (gramInChart ψ) (ψ x₀) = 0 := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  set z₀ := φ x₀ with hz₀
  have hz₀t : z₀ ∈ φ.target := φ.map_source hx₀
  obtain ⟨hGJ, hA, hAJ, hcyc⟩ := fderiv_gramInChart_symmetries hform φ (hc φ) hGΩ hz₀t
  have hG₀ (v : E) (hv : ∀ w, gramInChart φ z₀ v w = 0) : v = 0 := by
    by_contra h0
    exact (gramInChart_apply_self_pos φ hz₀t h0).ne' (hv v)
  obtain ⟨Q, hQs, hQJ, hQ⟩ := J₀.exists_symm_complexBilinear_apply_add_apply_eq _ hG₀
    (gramInChart_comm φ z₀) hGJ _ hA hAJ hcyc
  -- The holomorphic quadratic change of coordinates, and its local inverse.
  set Φ : E → E := fun z ↦ z + (2⁻¹ : ℝ) • Q (z - z₀) (z - z₀) with hΦ
  have hΦd (z : E) : HasFDerivAt Φ (ContinuousLinearMap.id ℝ E + Q (z - z₀)) z := by
    have h1 : HasFDerivAt (fun z ↦ z - z₀) (ContinuousLinearMap.id ℝ E) z :=
      (hasFDerivAt_id z).sub_const z₀
    have h2 := (Q.hasFDerivAt.comp z h1).clm_apply h1
    refine ((hasFDerivAt_id z).add (h2.const_smul (2⁻¹ : ℝ))).congr_fderiv ?_
    ext k
    simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, Function.comp_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.id_apply]
    rw [hQs k]
    module
  have hΦc : ContDiff ℝ ∞ Φ := contDiff_id.add
    (((Q.contDiff.comp (contDiff_id.sub contDiff_const)).clm_apply
      (contDiff_id.sub contDiff_const)).const_smul _)
  have hΦz₀ : Φ z₀ = z₀ := by simp [hΦ]
  obtain ⟨Θ, hΘc, hz₀Θ, -, hΘs⟩ := ContDiffOn.exists_openPartialHomeomorph
    (hΦc.contDiffOn (s := univ)) isOpen_univ (mem_univ z₀) (by simp)
    (e := ContinuousLinearEquiv.refl ℝ E)
    (by rw [(hΦd z₀).fderiv, sub_self, map_zero, add_zero, ContinuousLinearEquiv.coe_refl])
  let Θd := PartialDiffeomorph.ofOpenPartialHomeomorph Θ (hΘc ▸ hΦc.contDiffOn) hΘs
  have hΘdc : (Θd : E → E) = Φ := by
    simp only [Θd, PartialDiffeomorph.ofOpenPartialHomeomorph_toPartialEquiv,
      OpenPartialHomeomorph.coe_toPartialEquiv]
    exact hΘc
  have hz₀Θd : z₀ ∈ Θd.source := by simpa [Θd] using hz₀Θ
  have hΘdd (z : E) : HasFDerivAt Θd (ContinuousLinearMap.id ℝ E + Q (z - z₀)) z :=
    hΘdc ▸ hΦd z
  have hΘm (p a : E) : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Θd p a : E) =
      (ContinuousLinearMap.id ℝ E + Q (p - z₀)) a := by
    rw [← (hΘdd p).fderiv]
    exact (mvfderiv_apply_eq_mfderiv_apply (I := 𝓘(ℝ, E)) (F := E) (Θd : E → E) p a).symm.trans
      (TauCeti.mvfderiv_eq_fderiv_apply _ _ _)
  have hψx₀ : (φ.trans Θd) x₀ = z₀ := by
    rw [PartialDiffeomorph.coe_trans, Function.comp_apply, hΘdc, ← hz₀, hΦz₀]
  have hz₀ψ : z₀ ∈ (φ.trans Θd).target := hψx₀ ▸ (φ.trans Θd).map_source ⟨hx₀, hz₀Θd⟩
  refine ⟨φ.trans Θd, J₀, ⟨hx₀, hz₀Θd⟩, ?_, ?_⟩
  · -- The derivative of `Φ` is `J₀`-linear, so `J` stays `J₀` in the new chart.
    rw [J.forall_chartPushforward_apply_eq_iff]
    intro y hy v
    have hd (w : TangentSpace I y) : mfderiv I 𝓘(ℝ, E) (φ.trans Θd) y w =
        (ContinuousLinearMap.id ℝ E + Q (φ y - z₀)) (mfderiv I 𝓘(ℝ, E) φ y w) := by
      rw [PartialDiffeomorph.coe_trans]
      refine (congrArg (· w) (mfderiv_comp y
        (Θd.mdifferentiableAt hn (show φ y ∈ Θd.source from hy.2))
        (φ.mdifferentiableAt hn (show y ∈ φ.source from hy.1)))).trans ?_
      exact hΘm (φ y) (mfderiv I 𝓘(ℝ, E) φ y w)
    have hcomm (h a : E) : (ContinuousLinearMap.id ℝ E + Q h) (J₀ a) =
        J₀ ((ContinuousLinearMap.id ℝ E + Q h) a) := by
      rw [add_apply, add_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.id_apply, hQJ,
        J₀.apply_add]
    rw [hd, hd, (J.forall_chartPushforward_apply_eq_iff φ J₀).1 hφJ y hy.1 v]
    exact hcomm _ _
  · rw [hψx₀]
    exact fderiv_gramInChart_trans_eq_zero φ Θd Q hz₀t hz₀Θd (hΘdc ▸ hΦz₀) hΘdd
      ((hc φ).contDiffAt (φ.open_target.mem_nhds hz₀t) |>.differentiableAt (by simp))
      ((hc _).contDiffAt ((φ.trans Θd).open_target.mem_nhds hz₀ψ) |>.differentiableAt (by simp))
      hQ

end SymplecticGeometry

namespace TauCeti.SmoothAlmostComplexStructure

open SymplecticGeometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]

open Bundle in
/-- **Osculating holomorphic charts.** Let `J` be an integrable almost complex structure, let
`ω` be a closed two-form, and let the Riemannian metric be `g(v, w) = ω(v, J w)`. Then every
point `x₀` lies in the source of a chart `ψ` in which `J` is a constant linear complex structure
`J₀` of `E` on the whole target, and in which the metric, read in the chart, has derivative zero
at `ψ x₀`. -/
theorem IsIntegrable.exists_partialDiffeomorph_fderiv_gramInChart_eq_zero
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {J : SmoothAlmostComplexStructure I M} (hJ : J.IsIntegrable) {form : SmoothTwoForm I M}
    (hform : form.IsClosed) (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = form.val x ![v, J x w])
    (x₀ : M) :
    ∃ (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (J₀ : AlmostComplexStructure E),
      x₀ ∈ ψ.source ∧
        (∀ p ∈ ψ.target, ∀ w : E, J.chartPushforward ψ.toOpenPartialHomeomorph p w = J₀ w) ∧
        fderiv ℝ (gramInChart ψ) (ψ x₀) = 0 := by
  obtain ⟨φ, J₀, hx₀, hφJ⟩ := J.isIntegrable_def.1 hJ x₀
  exact exists_partialDiffeomorph_fderiv_gramInChart_eq_zero_aux
    (fun ψ ↦ contDiffOn_gramInChart ψ) hform φ hφJ hx₀
    fun z hz u v ↦ gramInChart_apply_eq_mpullback_symm_apply hg φ hφJ hz u v

end TauCeti.SmoothAlmostComplexStructure

end

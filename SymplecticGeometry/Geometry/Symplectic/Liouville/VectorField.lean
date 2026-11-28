/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Linearization
public import TauCeti.Geometry.Symplectic.Liouville.VectorField
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.LieDeriv
import TauCeti.Geometry.Manifold.VectorField.Chart.Linearization
import TauCeti.Geometry.Manifold.DifferentialForm.LieDeriv
import TauCeti.Geometry.Manifold.DifferentialForm.LocalPrimitive
import TauCeti.Geometry.Manifold.MFDeriv.Opens
import TauCeti.Geometry.Manifold.DifferentialForm.Opens
import SymplecticGeometry.Geometry.Manifold.VectorField.Pullback

/-!
# Liouville vector fields: pullback, linearization at a zero, linear fields, local differences

Let `Φ : M' → M` be a smooth map, `σ` a smooth two-form on `M` and `X` a Liouville vector field
of `σ`. If a vector field `Y` on `M'` is `Φ`-related to `X`, that is `dΦ_x (Y x) = X (Φ x)` for
every `x`, then `Y` is a Liouville vector field of `Φ^* σ`
(`TauCeti.IsLiouvilleVectorField.mpullback`). The form need not be closed, the differential of
`Φ` need not be invertible, and the models are arbitrary models with corners, so this applies
for instance to the inclusion of a regular sublevel set, a manifold with boundary, into the
ambient manifold.

The proof applies the naturality of the Lie derivative along related fields,
`TauCeti.mpullback_mlieDerivForm_of_related`: `Φ^* (L_X σ) = L_Y (Φ^* σ)`.

At a zero `p` of a Liouville vector field `Z` of a two-form `σ`, the condition `L_Z σ = σ`, read
at `p`, says that the linearization `A` of `Z` (Tau Ceti's `TauCeti.sectionLinearization`)
satisfies `σ_p (A u, v) + σ_p (u, A v) = σ_p (u, v)`
(`TauCeti.IsLiouvilleVectorField.apply_sectionLinearization_add`). The Lie derivative at a zero
of the field involves only the derivative of the field (`TauCeti.mlieDerivForm_apply_of_eq_zero`),
so no regularity of `Z` or `σ` is needed.

On a finite-dimensional real normed space `V`, with a linear symplectic form `σ` seen as a
constant form, a linear vector field `x ↦ A x` is Liouville as soon as
`σ (A u) v + σ u (A v) = σ u v` for all `u`, `v`
(`TauCeti.SymplecticForm.isLiouvilleVectorField_constSmooth`). Since the form is constant, its
Lie derivative along the field involves only the derivative `A` of the field. For linear fields
this is the converse of `TauCeti.IsLiouvilleVectorField.apply_sectionLinearization_add`, read at
the zero `0`.

Two smooth Liouville fields `X`, `X'` of one closed two-form `σ` differ, near any point, by a
Hamiltonian field (`TauCeti.IsLiouvilleVectorField.exists_eval₂_sub_eq_mvfderiv`). By
`TauCeti.isLiouvilleVectorField_iff_mextDeriv_interior_eq`, both `ι_X σ` and `ι_{X'} σ` are
primitives of `σ`, so `ι_{X' - X} σ` is closed, and Tau Ceti's local primitives of closed
`1`-forms, `TauCeti.exists_contMDiff_isPrimitiveOn`, write it near `p` as `dg`; the function
`K` is `g - g p`. In the convention of `TauCeti.SmoothTwoForm.IsHamiltonianVectorField`,
`σ (X' - X, ·) = dK`. The same holds when `X'` is only defined on an open set `U`, seen as a
manifold, with `K` smooth on `U`
(`TauCeti.IsLiouvilleVectorField.exists_eval₂_sub_eq_mvfderiv_opens`): restrict `X` to `U` and
apply the first statement there. Where `X'` and `X` agree at `p`, as when both vanish there,
`p` is a critical point of `K`
(`TauCeti.IsLiouvilleVectorField.exists_eval₂_sub_eq_mvfderiv_opens_of_eq`).

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.5
  (Liouville vector fields)
* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  §11.1, where Liouville fields are defined by `L_X ω = ω`. The identity at a zero is the
  derivative at `t = 0` of `e^t ω_p (v, w) = ω_p (e^{tA} v, e^{tA} w)`, the expansion of `ω_p`
  by the linearized flow in the proof of Proposition 11.9 (a). The radial field of
  Example 11.12 (1) and the field of Example 11.18 are linear Liouville fields. The local
  Hamiltonian of the difference of two Liouville fields is the first step of the proof of
  Lemma 12.9
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

variable {E H M E' H' M' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'}
  [IsManifold I 2 M] [IsManifold I' 2 M']

/-- **Liouville fields pull back along related fields.** Let `Φ : M' → M` be smooth, `σ` a
smooth two-form on `M`, and `X` a `C¹` Liouville vector field of `σ`. A differentiable vector
field `Y` on `M'` with `dΦ_x (Y x) = X (Φ x)` for every `x` is a Liouville vector field of the
pulled-back form `Φ^* σ`. No invertibility of `dΦ` is assumed, and `M'` may have a
boundary. -/
theorem IsLiouvilleVectorField.mpullback {Φ : M' → M} (hΦ : ContMDiff I' I ∞ Φ)
    {σ : SmoothForm I M ℝ 2} {X : (x : M) → TangentSpace I x}
    (hX : ContMDiff I I.tangent 1 (fun y ↦ (X y : TangentBundle I M)))
    (hXσ : IsLiouvilleVectorField σ.val X) {Y : (x : M') → TangentSpace I' x}
    (hY : MDifferentiable I' I'.tangent (fun y ↦ (Y y : TangentBundle I' M')))
    (hXY : ∀ x, mfderiv I' I Φ x (Y x) = X (Φ x)) :
    IsLiouvilleVectorField (SmoothForm.mpullback Φ hΦ σ).val Y := by
  rw [isLiouvilleVectorField_iff, SmoothForm.coe_mpullback,
    ← mpullback_mlieDerivForm_of_related (k := 2) (hΦ.of_le (by simp))
      (σ.isSmoothForm.of_le (by simp)) hX hY hXY, isLiouvilleVectorField_iff.mp hXσ]

section Linearization

variable {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [I.Boundaryless] [IsManifold I 1 N]

/-- **The linearized Liouville identity.** Let `Z` be a Liouville vector field of a two-form `σ`
(`L_Z σ = σ`) on a boundaryless manifold, and let `p` be a zero of `Z`, with linearization `A`.
Then `σ_p (A u, v) + σ_p (u, A v) = σ_p (u, v)` for all tangent vectors `u`, `v` at `p`: the
Lie derivative at a zero of the field is read off its linearization. -/
theorem IsLiouvilleVectorField.apply_sectionLinearization_add {σ : RoughForm I N ℝ 2}
    {Z : (x : N) → TangentSpace I x} (hZ : IsLiouvilleVectorField σ Z) {p : N} (hp : Z p = 0)
    (u v : TangentSpace I p) :
    σ p ![sectionLinearization (F := E) I id Z p u, v] +
        σ p ![u, sectionLinearization (F := E) I id Z p v] = σ p ![u, v] := by
  conv_rhs => rw [← isLiouvilleVectorField_iff.1 hZ]
  rw [mlieDerivForm_apply_of_eq_zero hp, Fin.sum_univ_two,
    sectionLinearization_apply_eq_vectorFieldChartDerivative,
    sectionLinearization_apply_eq_vectorFieldChartDerivative]
  -- Each entry of the updated pairs is computed by `Function.update` on `Fin 2`; the entries are
  -- tangent vectors at `p`, which `simp` does not match against vectors of `E`.
  congr 2 <;> funext i <;> fin_cases i <;> rfl

end Linearization

section Linear

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Linear Liouville fields.** Let `σ` be a linear symplectic form and `A` an operator with
`σ (A u) v + σ u (A v) = σ u v` for all `u`, `v`. Then the linear vector field `x ↦ A x` is a
Liouville vector field of the constant form `σ`. -/
theorem SymplecticForm.isLiouvilleVectorField_constSmooth (σ : SymplecticForm V)
    {A : V →L[ℝ] V} (hA : ∀ u v, σ (A u) v + σ u (A v) = σ u v) :
    IsLiouvilleVectorField σ.constSmooth.val
      (fun x ↦ A x : (x : V) → TangentSpace 𝓘(ℝ, V) x) := by
  refine isLiouvilleVectorField_iff.2 (funext fun x ↦ ?_)
  refine (mlieDerivForm_eq_lieDerivForm _ _ x).trans ?_
  ext v
  refine (lieDerivForm_apply _ v).trans ?_
  rw [Fin.sum_univ_two]
  -- The form, read in the model space, is the constant map `u ↦ σ (u 0) (u 1)`.
  set W : V → V [⋀^Fin 2]→L[ℝ] ℝ := σ.constSmooth.val
  have h (y : V) (u : Fin 2 → V) : W y u = σ (u 0) (u 1) := by
    have hu : u = ![u 0, u 1] := (FinVec.etaExpand_eq u).symm
    rw [hu]
    exact (SmoothBundleForm.eval₂_apply _ _ _ _).symm.trans (σ.constSmooth_apply y (u 0) (u 1))
  have hc : W = fun _ ↦ W x := funext fun y ↦ by ext u; rw [h, h]
  rw [hc]
  simp only [fderiv_fun_const, Pi.zero_apply, zero_apply, h, A.fderiv]
  simpa using hA (v 0) (v 1)

end Linear

section LocalHamiltonian

/-! ### The difference of two Liouville fields is locally Hamiltonian -/

open TopologicalSpace

variable {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [FiniteDimensional ℝ E]
  [IsManifold I ∞ N] [T2Space N]

/-- **The difference of two Liouville fields is locally Hamiltonian.** Let `σ` be a closed
two-form on `N`, and `X`, `X'` two smooth Liouville fields of `σ` on `N`. Then for every `p`
there are an open `V ∋ p` and a smooth function `K : N → ℝ` with `K p = 0` and
`σ (X' - X, v) = dK (v)` on `V`: on `V`, `X' - X` is the Hamiltonian field of `K` in the
convention of `SmoothTwoForm.IsHamiltonianVectorField`. -/
theorem IsLiouvilleVectorField.exists_eval₂_sub_eq_mvfderiv {σ : SmoothTwoForm I N}
    (hσ : σ.IsClosed) {X X' : (x : N) → TangentSpace I x} (hX : ContMDiff I I.tangent ∞ (T% X))
    (hXσ : IsLiouvilleVectorField σ.val X) (hX' : ContMDiff I I.tangent ∞ (T% X'))
    (hX'σ : IsLiouvilleVectorField σ.val X') (p : N) :
    ∃ V : Set N, IsOpen V ∧ p ∈ V ∧ ∃ K : N → ℝ, ContMDiff I 𝓘(ℝ) ∞ K ∧ K p = 0 ∧
      ∀ x ∈ V, ∀ v : TangentSpace I x,
        SmoothBundleForm.eval₂ σ x (X' x) v - SmoothBundleForm.eval₂ σ x (X x) v =
          mvfderiv I K x v := by
  have hdσ := (SmoothForm.isClosed_def σ).1 hσ
  -- Both `ι_X σ` and `ι_{X'} σ` are primitives of `σ`, so their difference is closed.
  set β : SmoothForm I N ℝ 1 :=
    ⟨RoughForm.interior X σ.val, (σ.isSmoothForm.interior hX).mem_smoothBundleForms⟩
  set β' : SmoothForm I N ℝ 1 :=
    ⟨RoughForm.interior X' σ.val, (σ.isSmoothForm.interior hX').mem_smoothBundleForms⟩
  have hβ : mextDeriv β.val = σ.val :=
    (isLiouvilleVectorField_iff_mextDeriv_interior_eq σ.mdifferentiable
      (hX.mdifferentiable (by simp)) hdσ).1 hXσ
  have hβ' : mextDeriv β'.val = σ.val :=
    (isLiouvilleVectorField_iff_mextDeriv_interior_eq σ.mdifferentiable
      (hX'.mdifferentiable (by simp)) hdσ).1 hX'σ
  have hcl : mextDeriv (β' - β).val = 0 := by
    rw [← mextDerivₗ_apply, map_sub, Submodule.coe_sub, mextDerivₗ_apply, mextDerivₗ_apply, hβ,
      hβ', sub_self]
  obtain ⟨g, hg, V, hpV, hgV⟩ := exists_contMDiff_isPrimitiveOn le_top (β' - β).isSmoothForm hcl p
  have hK := hgV.add_const (-g p)
  refine ⟨V, hK.isOpen, hpV, fun y ↦ g y + -g p, hg.add contMDiff_const, add_neg_cancel _,
    fun x hx v ↦ ?_⟩
  rw [mvfderiv_apply_eq_mfderiv_apply, ← mextDeriv_ofFunction_apply, hK.mextDeriv_eq x hx]
  simp [β, β', SmoothBundleForm.eval₂_apply, RoughForm.interior_apply]

/-- **The difference of two Liouville fields is locally Hamiltonian, on an open set.** Let `σ` be
a closed two-form on `N`, `X` a smooth Liouville field of `σ` on `N`, and `X'` a smooth Liouville
field, on an open set `U` seen as a manifold, of the restriction of `σ` to `U`. Then for every
`p ∈ U` there are an open `V` with `p ∈ V ⊆ U` and a function `K : N → ℝ`, smooth on `U`, with
`K p = 0` and `σ (X' - X, v) = dK (v)` on `V`: on `V`, `X' - X` is the Hamiltonian field of `K` in
the convention of `SmoothTwoForm.IsHamiltonianVectorField`. -/
theorem IsLiouvilleVectorField.exists_eval₂_sub_eq_mvfderiv_opens {σ : SmoothTwoForm I N}
    (hσ : σ.IsClosed) {X : (x : N) → TangentSpace I x} (hX : ContMDiff I I.tangent ∞ (T% X))
    (hXσ : IsLiouvilleVectorField σ.val X) {U : Opens N} {X' : (x : U) → TangentSpace I x}
    (hX' : ContMDiff I I.tangent ∞ (T% X'))
    (hX'σ : IsLiouvilleVectorField
      (SmoothForm.mpullback (Subtype.val : U → N) contMDiff_subtypeVal σ).val X')
    {p : N} (hp : p ∈ U) :
    ∃ V : Opens N, ∃ hVU : V ≤ U, p ∈ V ∧ ∃ K : N → ℝ, ContMDiffOn I 𝓘(ℝ) ∞ K U ∧ K p = 0 ∧
      ∀ x (hx : x ∈ V) (v : TangentSpace I x),
        SmoothBundleForm.eval₂ σ x (X' ⟨x, hVU hx⟩) v - SmoothBundleForm.eval₂ σ x (X x) v =
          mvfderiv I K x v := by
  classical
  -- Restrict `X` to `U`, where it is a Liouville field of the restriction of `σ`.
  set Y := VectorField.mpullback I I (Subtype.val : U → N) X
  have hY : ContMDiff I I.tangent ∞ (T% Y) :=
    VectorField.contMDiff_mpullback_subtypeVal hX.contMDiffOn
  have hYX (y : U) : Y y = X y := by
    have h := VectorField.mfderiv_subtypeVal_mpullback_subtypeVal X y
    rw [Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe,
      Manifold.tangentSpaceOpenEquiv_apply] at h
    exact h
  have hYσ := hXσ.mpullback contMDiff_subtypeVal (hX.of_le (by simp)) (hY.mdifferentiable (by simp))
    (VectorField.mfderiv_subtypeVal_mpullback_subtypeVal X)
  obtain ⟨W, hW, hpW, g, hg, hgp, hgW⟩ :=
    exists_eval₂_sub_eq_mvfderiv (hσ.mpullback _ contMDiff_subtypeVal) hY hYσ hX' hX'σ ⟨p, hp⟩
  -- `K` is `g` on `U`, extended by `0`.
  set K : N → ℝ := fun x ↦ if hx : x ∈ U then g ⟨x, hx⟩ else 0
  have hK : K ∘ (Subtype.val : U → N) = g := funext fun y ↦ dite_eq_left y.property
  refine ⟨⟨Subtype.val '' W, U.isOpen.isOpenMap_subtypeVal W hW⟩,
    by rintro _ ⟨y, -, rfl⟩; exact y.property, ⟨⟨p, hp⟩, hpW, rfl⟩, K, fun x hx ↦ ?_,
    by simp [K, hp, hgp], ?_⟩
  · refine (contMDiffAt_subtype_iff (x := ⟨x, hx⟩).1 ?_).contMDiffWithinAt
    exact (hK ▸ hg).contMDiffAt
  · rintro _ ⟨y, hyW, rfl⟩ v
    rw [← Manifold.mvfderiv_comp_subtype_val K y, hK]
    refine Eq.trans ?_ (hgW y hyW v)
    have h (a b : TangentSpace I y) : SmoothBundleForm.eval₂
        (SmoothForm.mpullback (Subtype.val : U → N) contMDiff_subtypeVal σ) y a b =
          SmoothBundleForm.eval₂ σ y a b := by
      rw [SmoothBundleForm.eval₂_apply, SmoothForm.coe_mpullback, mpullback_subtype_val_apply]
      exact (SmoothBundleForm.eval₂_apply σ y a b).symm
    -- The tangent spaces of `U` at `y` and of `N` at `↑y` are both `E`, which `rw` does not see
    -- through, so the two sides are matched by `h` term by term.
    exact congrArg₂ (· - ·) (h (X' y) v).symm ((h (Y y) v).trans (by rw [hYX])).symm

/-- If moreover `X'` and `X` agree at `p`, for instance when both vanish there, the function `K`
of `TauCeti.IsLiouvilleVectorField.exists_eval₂_sub_eq_mvfderiv_opens` also has `dK p = 0`: `p`
is a critical point of `K`. -/
theorem IsLiouvilleVectorField.exists_eval₂_sub_eq_mvfderiv_opens_of_eq {σ : SmoothTwoForm I N}
    (hσ : σ.IsClosed) {X : (x : N) → TangentSpace I x} (hX : ContMDiff I I.tangent ∞ (T% X))
    (hXσ : IsLiouvilleVectorField σ.val X) {U : Opens N} {X' : (x : U) → TangentSpace I x}
    (hX' : ContMDiff I I.tangent ∞ (T% X'))
    (hX'σ : IsLiouvilleVectorField
      (SmoothForm.mpullback (Subtype.val : U → N) contMDiff_subtypeVal σ).val X')
    {p : N} (hp : p ∈ U) (hXp : X' ⟨p, hp⟩ = X p) :
    ∃ V : Opens N, ∃ hVU : V ≤ U, p ∈ V ∧ ∃ K : N → ℝ, ContMDiffOn I 𝓘(ℝ) ∞ K U ∧ K p = 0 ∧
      mvfderiv I K p = 0 ∧ ∀ x (hx : x ∈ V) (v : TangentSpace I x),
        SmoothBundleForm.eval₂ σ x (X' ⟨x, hVU hx⟩) v - SmoothBundleForm.eval₂ σ x (X x) v =
          mvfderiv I K x v := by
  obtain ⟨V, hVU, hpV, K, hK, hKp, hdK⟩ :=
    hXσ.exists_eval₂_sub_eq_mvfderiv_opens hσ hX hX' hX'σ hp
  refine ⟨V, hVU, hpV, K, hK, hKp, ContinuousLinearMap.ext fun v ↦ ?_, hdK⟩
  rw [← hdK p hpV v, zero_apply, hXp, sub_self]

end LocalHamiltonian

end TauCeti

end

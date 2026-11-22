/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
public import SymplecticGeometry.Geometry.Manifold.Complex.Integrable
public import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Covariant
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Eigenbundle.Involutive
public import TauCeti.Geometry.Symplectic.Manifold.Surface
import TauCeti.Geometry.Manifold.VectorField.Related

/-!
# The Nijenhuis tensor: naturality and the formula through a connection

This file adds to Tau Ceti's Nijenhuis tensor `TauCeti.SmoothAlmostComplexStructure.nijenhuis`
of a smooth almost complex structure `J`, which with Mathlib's bracket `mlieBracket` is
`N_J(X, Y) = [JX, JY] - [X, Y] - J[JX, Y] - J[X, JY]`:

* `N_J(v, Jv) = 0`;
* naturality: for a diffeomorphism `h : M → N` and a structure `J` on `N`, the Nijenhuis tensor of
  the pullback `h^* J` is the pullback of the Nijenhuis tensor of `J`. Lie brackets commute with
  pullbacks along diffeomorphisms (Mathlib's `VectorField.mpullback_mlieBracket`), and `h^* J`
  maps pullbacks of vector fields to pullbacks;
* naturality for related vector fields: if a `C²` map `f : M → N` intertwines `J` with `K` near
  `x`, `df ∘ J = K ∘ df`, and the fields `X, Y` on `M` are `f`-related near `x` to fields `V, W`
  on `N`, then `df_x (N_J(X, Y) x) = N_K(V, W) (f x)`. The differential of `f` need not be
  invertible: each bracket is handled by Tau Ceti's
  `TauCeti.mfderiv_mlieBracket_of_eventually_related`;
* for a covariant derivative `∇` on `TM` whose torsion vanishes at `x`,
  `N_J(v, w) = (∇_{Jv} J) w - (∇_{Jw} J) v + (∇_v J) (J w) - (∇_w J) (J v)` at `x`, where
  `∇J` is the induced connection `CovariantDerivative.hom` applied to `J`. The brackets are
  replaced by `[X, Y] = ∇_X Y - ∇_Y X`, and the anticommutation of `∇_v J` with `J`
  (`apply_hom_toEndomorphism_apply`) brings the result to this form;
* the theorem `nijenhuis_tensor` that collects these with the properties of `N_J` that Tau Ceti and
  `IsIntegrable.nijenhuis_eq_zero` prove.

## Main declarations

* `TauCeti.SmoothAlmostComplexStructure.nijenhuis_self_apply`: `N_J(v, Jv) = 0`.
* `TauCeti.SmoothAlmostComplexStructure.nijenhuis_pullback`: naturality under pullback along a
  diffeomorphism, on tangent vectors.
* `TauCeti.SmoothAlmostComplexStructure.nijenhuis_mpullback`: the same on vector fields,
  `N_{h^* J}(h^* X, h^* Y) = h^* N_J(X, Y)`.
* `TauCeti.SmoothAlmostComplexStructure.mfderiv_nijenhuis_of_eventually_related`: naturality for
  related vector fields along any `C²` map intertwining two structures.
* `TauCeti.SmoothAlmostComplexStructure.nijenhuis_eq_hom_toEndomorphism`: the formula of `N_J`
  through a torsion-free covariant derivative.
* `TauCeti.SmoothAlmostComplexStructure.nijenhuis_tensor`: the properties of the Nijenhuis
  tensor, as one theorem.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 4.2.1, Exercise 4.2.3, Lemma 4.2.4 and equation (4.2.4).
-/

public section

open Bundle FiberBundle VectorField Module.End Filter
open scoped Manifold ContDiff Topology

namespace TauCeti

namespace SmoothAlmostComplexStructure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (J : SmoothAlmostComplexStructure I M)

/-- The Nijenhuis tensor vanishes on a vector and its image under `J`: `N_J(v, Jv) = 0`. -/
theorem nijenhuis_self_apply {x : M} (v : TangentSpace I x) : J.nijenhuis x v (J x v) = 0 := by
  simp

section Pullback

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]

/-- **Naturality of the Nijenhuis tensor.** For a diffeomorphism `h : M → N` and a smooth almost
complex structure `J` on `N`, the Nijenhuis tensor of the pullback `h^* J` at `x` is the Nijenhuis
tensor of `J` at `h x` read through the differential `dh_x`:
`N_{h^* J}(v, w) = (dh_x)⁻¹ N_J(dh_x v, dh_x w)`. -/
theorem nijenhuis_pullback (h : M ≃ₘ⟮I, I'⟯ N) (J : SmoothAlmostComplexStructure I' N) (x : M)
    (v w : TangentSpace I x) :
    (pullback h J).nijenhuis x v w = (mfderiv I I' h x).inverse
      (J.nijenhuis (h x) (mfderiv I I' h x v) (mfderiv I I' h x w)) := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hh : ContMDiffAt I I' ∞ h x := h.contMDiff x
  have : IsManifold I (minSmoothness ℝ 2) M := .of_le (n := ∞) (by simp)
  have : IsManifold I' (minSmoothness ℝ 2) N := .of_le (n := ∞) (by simp)
  have hinv (y : M) := h.isInvertible_mfderiv hn (x := y)
  -- Vector fields on `N` through `dh_x v` and `dh_x w`, and their pullbacks to `M`.
  set X' := extend E' (mfderiv I I' h x v)
  set Y' := extend E' (mfderiv I I' h x w)
  have hX' : MDiffAt (T% X') (h x) := mdifferentiableAt_extend ..
  have hY' : MDiffAt (T% Y') (h x) := mdifferentiableAt_extend ..
  have hX'x : X' (h x) = mfderiv I I' h x v := extend_apply_self ..
  have hY'x : Y' (h x) = mfderiv I I' h x w := extend_apply_self ..
  have hJX' := J.mdifferentiableAt_apply hX'
  have hJY' := J.mdifferentiableAt_apply hY'
  have hpb {V : Π z : N, TangentSpace I' z} (hV : MDiffAt (T% V) (h x)) :
      MDiffAt (T% (VectorField.mpullback I I' h V)) x :=
    hV.mpullback_vectorField hh (hinv x) (by simp)
  have hval {u : TangentSpace I x} :
      VectorField.mpullback I I' h (extend E' (mfderiv I I' h x u)) x = u := by
    rw [VectorField.mpullback_apply, extend_apply_self]
    exact (hinv x).inverse_apply_self u
  -- `h^* J` maps the pullback of a vector field to the pullback of its image under `J`.
  have hJ (V : Π z : N, TangentSpace I' z) :
      (fun y ↦ pullback h J y (VectorField.mpullback I I' h V y)) =
        VectorField.mpullback I I' h (fun z ↦ J z (V z)) := by
    funext y
    rw [pullback_apply, VectorField.mpullback_apply, VectorField.mpullback_apply,
      (hinv y).self_apply_inverse]
  have hbr {V W : Π z : N, TangentSpace I' z} (hV : MDiffAt (T% V) (h x))
      (hW : MDiffAt (T% W) (h x)) :
      mlieBracket I (VectorField.mpullback I I' h V) (VectorField.mpullback I I' h W) x =
        (mfderiv I I' h x).inverse (mlieBracket I' V W (h x)) := by
    rw [← mpullback_mlieBracket hV hW hh (by simp), VectorField.mpullback_apply]
  have hJinv (z : TangentSpace I' (h x)) :
      pullback h J x ((mfderiv I I' h x).inverse z) = (mfderiv I I' h x).inverse (J (h x) z) := by
    rw [pullback_apply, (hinv x).self_apply_inverse]
  conv_lhs => rw [← hval (u := v), ← hval (u := w)]
  rw [nijenhuis_apply _ (hpb hX') (hpb hY'), hJ, hJ, hbr hJX' hJY', hbr hX' hY', hbr hJX' hY',
    hbr hX' hJY', hJinv, hJinv]
  conv_rhs => rw [← hX'x, ← hY'x, J.nijenhuis_apply hX' hY']
  simp only [map_sub]

/-- **Naturality of the Nijenhuis tensor on vector fields.** For a diffeomorphism `h : M → N`, a
smooth almost complex structure `J` on `N` and vector fields `X`, `Y` on `N`,
`N_{h^* J}(h^* X, h^* Y) = h^* N_J(X, Y)`. -/
theorem nijenhuis_mpullback (h : M ≃ₘ⟮I, I'⟯ N) (J : SmoothAlmostComplexStructure I' N)
    (X Y : Π z : N, TangentSpace I' z) (x : M) :
    (pullback h J).nijenhuis x (VectorField.mpullback I I' h X x)
        (VectorField.mpullback I I' h Y x) =
      VectorField.mpullback I I' h (fun y ↦ J.nijenhuis y (X y) (Y y)) x := by
  have hinv := h.isInvertible_mfderiv (by simp) (x := x)
  simp only [nijenhuis_pullback, VectorField.mpullback_apply]
  rw [hinv.self_apply_inverse, hinv.self_apply_inverse]

/-- **Naturality of the Nijenhuis tensor for related vector fields.** Let `f : M → N` be `C²` at
`x` and intertwine `J` on `M` with `K` on `N` near `x`, `df_z ∘ J_z = K_{f z} ∘ df_z`. If the vector
fields `X, Y` on `M`, differentiable at `x`, are `f`-related near `x` to vector fields `V, W` on
`N`, differentiable at `f x`, then `df_x (N_J(X, Y) x) = N_K(V, W) (f x)`. The differential of `f`
need not be invertible. -/
theorem mfderiv_nijenhuis_of_eventually_related (K : SmoothAlmostComplexStructure I' N) {f : M → N}
    {x : M} (hf : ContMDiffAt I I' 2 f x)
    (hJK : ∀ᶠ z in 𝓝 x, ∀ v : TangentSpace I z,
      mfderiv I I' f z (J z v) = K (f z) (mfderiv I I' f z v))
    {X Y : Π z : M, TangentSpace I z} {V W : Π y : N, TangentSpace I' y}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hV : MDiffAt (T% V) (f x))
    (hW : MDiffAt (T% W) (f x)) (hXV : ∀ᶠ z in 𝓝 x, mfderiv I I' f z (X z) = V (f z))
    (hYW : ∀ᶠ z in 𝓝 x, mfderiv I I' f z (Y z) = W (f z)) :
    mfderiv I I' f x (J.nijenhuis x (X x) (Y x)) = K.nijenhuis (f x) (V (f x)) (W (f x)) := by
  have : IsManifold I (minSmoothness ℝ 2) M := .of_le (n := ∞) (by simp)
  have : IsManifold I' (minSmoothness ℝ 2) N := .of_le (n := ∞) (by simp)
  -- `J X` is related to `K V` near `x`, and likewise for `Y` and `W`.
  have hJ {A : Π z : M, TangentSpace I z} {B : Π y : N, TangentSpace I' y}
      (hAB : ∀ᶠ z in 𝓝 x, mfderiv I I' f z (A z) = B (f z)) :
      ∀ᶠ z in 𝓝 x, mfderiv I I' f z (J z (A z)) = K (f z) (B (f z)) := by
    filter_upwards [hJK, hAB] with z hz hzAB
    rw [hz, hzAB]
  have hbr {A B : Π z : M, TangentSpace I z} {A' B' : Π y : N, TangentSpace I' y}
      (hA : MDiffAt (T% A) x) (hB : MDiffAt (T% B) x) (hA' : MDiffAt (T% A') (f x))
      (hB' : MDiffAt (T% B') (f x)) (hAA' : ∀ᶠ z in 𝓝 x, mfderiv I I' f z (A z) = A' (f z))
      (hBB' : ∀ᶠ z in 𝓝 x, mfderiv I I' f z (B z) = B' (f z)) :
      mfderiv I I' f x (mlieBracket I A B x) = mlieBracket I' A' B' (f x) :=
    TauCeti.mfderiv_mlieBracket_of_eventually_related hf (by simp) hA hB hA' hB' hAA' hBB'
  have hJX := J.mdifferentiableAt_apply hX
  have hJY := J.mdifferentiableAt_apply hY
  have hKV := K.mdifferentiableAt_apply hV
  have hKW := K.mdifferentiableAt_apply hW
  rw [J.nijenhuis_apply hX hY, K.nijenhuis_apply hV hW, map_sub, map_sub, map_sub,
    hJK.self_of_nhds, hJK.self_of_nhds, hbr hJX hJY hKV hKW (hJ hXV) (hJ hYW),
    hbr hX hY hV hW hXV hYW, hbr hJX hY hKV hW (hJ hXV) hYW, hbr hX hJY hV hKW hXV (hJ hYW)]

end Pullback

section Connection

variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))

/-- **The Nijenhuis tensor through a torsion-free connection.** If the torsion of a covariant
derivative `∇` on `TM` vanishes at `x`, then with `∇J` the induced covariant derivative of `J`,
`N_J(v, w) = (∇_{Jv} J) w - (∇_{Jw} J) v + (∇_v J) (J w) - (∇_w J) (J v)`. -/
theorem nijenhuis_eq_hom_toEndomorphism {x : M} (hcov : cov.torsion x = 0)
    (v w : TangentSpace I x) :
    J.nijenhuis x v w =
      cov.hom cov J.toEndomorphism x (J x v) w - cov.hom cov J.toEndomorphism x (J x w) v +
        cov.hom cov J.toEndomorphism x v (J x w) - cov.hom cov J.toEndomorphism x w (J x v) := by
  -- Without torsion at `x`, the bracket is `[A, B] = ∇_A B - ∇_B A` there.
  have hbr {A B : Π y : M, TangentSpace I y} (hA : MDiffAt (T% A) x) (hB : MDiffAt (T% B) x) :
      mlieBracket I A B x = cov B x (A x) - cov A x (B x) := by
    have h := cov.torsion_apply hA hB
    rw [hcov, zero_apply, zero_apply] at h
    exact (sub_eq_zero.1 h.symm).symm
  -- The Leibniz rule `∇_u (J B) = (∇_u J) B + J (∇_u B)`.
  have hJ {B : Π y : M, TangentSpace I y} (hB : MDiffAt (T% B) x) (u : TangentSpace I x) :
      cov (fun y ↦ J y (B y)) x u = cov.hom cov J.toEndomorphism x u (B x) + J x (cov B x u) := by
    rw [cov.hom_apply cov (J.mdifferentiableAt_toEndomorphism x) hB u, sub_add_cancel]
  set X := extend E v
  set Y := extend E w
  have hX : MDiffAt (T% X) x := mdifferentiableAt_extend ..
  have hY : MDiffAt (T% Y) x := mdifferentiableAt_extend ..
  have hJX := J.mdifferentiableAt_apply hX
  have hJY := J.mdifferentiableAt_apply hY
  have hXx : X x = v := extend_apply_self ..
  have hYx : Y x = w := extend_apply_self ..
  conv_lhs => rw [← hXx, ← hYx]
  rw [J.nijenhuis_apply hX hY, hbr hJX hJY, hbr hX hY, hbr hJX hY, hbr hX hJY, hJ hX, hJ hY,
    hJ hX, hJ hY, hXx, hYx]
  have h₁ := J.apply_hom_toEndomorphism_apply cov x w v
  have h₂ := J.apply_hom_toEndomorphism_apply cov x v w
  beta_reduce at h₁ h₂
  simp only [map_add, map_sub, apply_apply, h₁, h₂]
  abel

end Connection

/-- **The Nijenhuis tensor.** Let `J` be a smooth almost complex structure on `M`. Brackets are
Mathlib's `mlieBracket`, and `N_J(X, Y) = [JX, JY] - [X, Y] - J[JX, Y] - J[X, JY]`.

1. `N_J` is a tensor, a continuous bilinear map on each tangent space, whose value on vector fields
   differentiable at a point is the expression above, and it is skew-symmetric.
2. `N_J(v, Jv) = 0`, `N_J(Jv, w) = N_J(v, Jw) = -J N_J(v, w)`, and `N_J = 0` in dimension two.
3. For a diffeomorphism `φ : M' → M` and vector fields `X`, `Y` on `M`,
   `N_{φ^* J}(φ^* X, φ^* Y) = φ^* N_J(X, Y)`.
4. A linear complex structure, constant on the model space `E`, has `N = 0`; so has `J` when it is
   integrable.
5. For every covariant derivative `∇` on `TM` without torsion,
   `N_J(v, w) = (∇_{Jv} J) w - (∇_{Jw} J) v + (∇_v J) (J w) - (∇_w J) (J v)`.
6. The bundle of `i`-eigenspaces of `J` in the complexified tangent bundle, whose sections are
   the fields `X - i J X`, is involutive if and only if `N_J = 0`.

Milestone: *Nijenhuis tensor*. -/
theorem nijenhuis_tensor :
    (∀ {X Y : Π x : M, TangentSpace I x} {x : M}, MDiffAt (T% X) x → MDiffAt (T% Y) x →
      J.nijenhuis x (X x) (Y x) =
        mlieBracket I (fun y ↦ J y (X y)) (fun y ↦ J y (Y y)) x - mlieBracket I X Y x -
          J x (mlieBracket I (fun y ↦ J y (X y)) Y x) -
          J x (mlieBracket I X (fun y ↦ J y (Y y)) x)) ∧
    (∀ (x : M) (v w : TangentSpace I x), J.nijenhuis x v w = -J.nijenhuis x w v) ∧
    (∀ (x : M) (v w : TangentSpace I x), J.nijenhuis x v (J x v) = 0 ∧
      J.nijenhuis x (J x v) w = -J x (J.nijenhuis x v w) ∧
      J.nijenhuis x v (J x w) = -J x (J.nijenhuis x v w)) ∧
    (Module.finrank ℝ E = 2 → J.nijenhuis = 0) ∧
    (∀ {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
      [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M']
      [ChartedSpace H' M'] [IsManifold I' ∞ M'] (φ : M' ≃ₘ⟮I', I⟯ M)
      (X Y : Π x : M, TangentSpace I x) (x : M'),
      (pullback φ J).nijenhuis x (VectorField.mpullback I' I φ X x)
          (VectorField.mpullback I' I φ Y x) =
        VectorField.mpullback I' I φ (fun y ↦ J.nijenhuis y (X y) (Y y)) x) ∧
    (∀ J₀ : AlmostComplexStructure E, J₀.constSmooth.nijenhuis = 0) ∧
    (J.IsIntegrable → J.nijenhuis = 0) ∧
    (∀ (cov : CovariantDerivative I E (TangentSpace I : M → Type _)), cov.torsion = 0 →
      ∀ (x : M) (v w : TangentSpace I x), J.nijenhuis x v w =
        cov.hom cov J.toEndomorphism x (J x v) w - cov.hom cov J.toEndomorphism x (J x w) v +
          cov.hom cov J.toEndomorphism x v (J x w) -
          cov.hom cov J.toEndomorphism x w (J x v)) ∧
    (IsInvolutiveComplexDistribution I
        (fun x ↦ eigenspace ((J.almostComplexStructureAt x).toLinearMap.baseChange ℂ) Complex.I) ↔
      J.nijenhuis = 0) := by
  exact ⟨fun hX hY ↦ J.nijenhuis_apply hX hY, fun x ↦ J.nijenhuis_antisymm,
    fun x v w ↦ ⟨J.nijenhuis_self_apply v, J.nijenhuis_apply_left v w,
      J.nijenhuis_apply_right v w⟩, J.nijenhuis_eq_zero_of_finrank_eq_two,
    fun φ X Y x ↦ nijenhuis_mpullback φ J X Y x, fun J₀ ↦ J₀.nijenhuis_constSmooth,
    IsIntegrable.nijenhuis_eq_zero,
    fun cov hcov x ↦ J.nijenhuis_eq_hom_toEndomorphism cov (congrFun hcov x),
    J.isInvolutiveComplexDistribution_eigenspace_I_iff⟩

end SmoothAlmostComplexStructure

end TauCeti

end

/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Lie.FundamentalVectorField

/-!
# The action of a group on `G × N` through the first factor

A group `G` acts on `G × N` by left multiplication of the first factor,
`g • (h, p) = (g * h, p)`. Mathlib has no such action, so this file defines one,
`SymplecticGeometry.prodFstMulAction`, which is not an instance, and shows that it is `Cⁿ`
whenever multiplication on `G` is (`SymplecticGeometry.contMDiffSMul_prodFstMulAction`).

For any action of a Lie group `G` on `G × N` given by `g • q = (g * q.1, q.2)`, the fundamental
vector field of `ξ` has the components `(ξ_G, 0)`, with `ξ_G` the fundamental vector field of
left multiplication on `G`:

* `TauCeti.mfderiv_fst_fundamentalVectorField_of_smul_eq`: its first component is `ξ_G`, by Tau
  Ceti's `TauCeti.mfderiv_fundamentalVectorField_of_map_smul`;
* `TauCeti.mfderiv_snd_fundamentalVectorField_of_smul_eq`: its second component is zero, by Tau
  Ceti's `TauCeti.mfderiv_fundamentalVectorField_eq_zero_of_smul_invariant`.

These two are stated for any such action, as Tau Ceti's
`TauCeti.fundamentalVectorField_prod_of_smul_eq` is, so that they apply to an action that is not
definitionally `prodFstMulAction`.
-/

public section

open scoped Manifold ContDiff

noncomputable section

namespace SymplecticGeometry

variable (G N : Type*) [Group G]

/-- The action of a group `G` on `G × N` by left multiplication of the first factor,
`g • (h, p) = (g * h, p)`. It is not a global instance, since `N` may carry an action of `G` of
its own: use it with `letI := prodFstMulAction G N`. -/
@[instance_reducible]
def prodFstMulAction : MulAction G (G × N) where
  smul g q := (g * q.1, q.2)
  one_smul q := Prod.ext (one_mul q.1) rfl
  mul_smul g h q := Prod.ext (mul_assoc g h q.1) rfl

variable {G N}

/-- The action of `G` on `G × N` through the first factor. Not a simp lemma: its left side is a
scalar multiplication by an action that is not an instance. -/
theorem prodFstMulAction_smul (g : G) (q : G × N) :
    letI := prodFstMulAction G N
    g • q = (g * q.1, q.2) :=
  (rfl)

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace G] [ChartedSpace H G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} [TopologicalSpace N] [ChartedSpace H' N] {n : ℕ∞ω}

/-- The action of `G` on `G × N` through the first factor is `Cⁿ` when multiplication on `G` is. -/
theorem contMDiffSMul_prodFstMulAction [ContMDiffMul I n G] :
    letI := prodFstMulAction G N
    ContMDiffSMul I (I.prod J) n G (G × N) :=
  letI := prodFstMulAction G N
  ⟨((contMDiff_fst.mul (contMDiff_fst.comp contMDiff_snd)).prodMk
    (contMDiff_snd.comp contMDiff_snd)).congr fun p ↦ prodFstMulAction_smul p.1 p.2⟩

end SymplecticGeometry

namespace TauCeti

variable {G N : Type*} [Group G]
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace G] [ChartedSpace H G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [MulAction G (G × N)] [ContMDiffSMul I (I.prod J) 1 G (G × N)]

/-- For an action of `G` on `G × N` by `g • q = (g * q.1, q.2)`, the first component of the
fundamental vector field of `ξ` is the fundamental vector field of `ξ` for left multiplication
on `G`. -/
theorem mfderiv_fst_fundamentalVectorField_of_smul_eq
    (hsmul : ∀ (g : G) (q : G × N), g • q = (g * q.1, q.2)) (ξ : GroupLieAlgebra I G)
    (q : G × N) :
    mfderiv (I.prod J) I Prod.fst q (fundamentalVectorField (I.prod J) ξ q) =
      fundamentalVectorField I ξ q.1 :=
  mfderiv_fundamentalVectorField_of_map_smul mdifferentiableAt_fst
    ((ContMDiffSMul.contMDiff_smul_const (n := 1) q).mdifferentiableAt one_ne_zero)
    (fun g ↦ by rw [hsmul, smul_eq_mul]) ξ

/-- For an action of `G` on `G × N` by `g • q = (g * q.1, q.2)`, the fundamental vector fields
have no component along `N`. -/
theorem mfderiv_snd_fundamentalVectorField_of_smul_eq
    (hsmul : ∀ (g : G) (q : G × N), g • q = (g * q.1, q.2)) (ξ : GroupLieAlgebra I G)
    (q : G × N) :
    mfderiv (I.prod J) J Prod.snd q (fundamentalVectorField (I.prod J) ξ q) = 0 :=
  mfderiv_fundamentalVectorField_eq_zero_of_smul_invariant mdifferentiableAt_snd
    ((ContMDiffSMul.contMDiff_smul_const (n := 1) q).mdifferentiableAt one_ne_zero)
    (fun g ↦ by rw [hsmul]) ξ

end TauCeti

end

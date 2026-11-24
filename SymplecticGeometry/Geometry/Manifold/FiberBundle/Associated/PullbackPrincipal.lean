/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Lie.FundamentalVectorField.Right
public import TauCeti.Geometry.Manifold.FiberBundle.Associated.Pullback
public import TauCeti.Geometry.Manifold.FiberBundle.Associated.Section
public import TauCeti.Geometry.Manifold.FiberBundle.Pullback.Basic
public import TauCeti.Geometry.Manifold.FiberBundle.Submersion
public import TauCeti.Geometry.Manifold.Submersion.Split
public import SymplecticGeometry.Geometry.Lie.FundamentalVectorField
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Basic

/-!
# The product `P × F` as the pull-back of `P` to `P ×_G F`

Let `P` be a principal `G`-bundle over `B`, let `G` act on the left on a manifold `F`, and let
`M = P ×_G F` be the associated bundle, with charted total space
`TauCeti.ManifoldTotalSpace F (AssociatedBundle G P F)` and projection `π_M : M → B`. The
pull-back `Q = π_M^* P` is a principal `G`-bundle over `M`, whose fibre over `[x, v]` is the fibre
of `P` through `x`. The map `Φ (x, v) = ([x, v], x)` identifies `P × F` with the total space of `Q`:
the class `[x, v]` and the point `y = x` of its fibre recover `v` as the unique `w` with
`[y, w] = [x, v]`. Under `Φ`, the projection of `Q` becomes the quotient map `q (x, v) = [x, v]`,
and the principal action of `G` on `Q` becomes the diagonal action `(x, v) · g = (x · g, g⁻¹ v)`.
So the derivative of `Φ` carries the fundamental vectors `(x ξ, -X_ξ(v))` of the diagonal action to
those of `Q`, and `q`, being `π_Q ∘ Φ`, is a surjective submersion.

## Main definitions and results

* `TauCeti.AssociatedBundle.pullbackProjDiffeomorph`: the `C^n` diffeomorphism `Φ` from
  `ManifoldTotalSpace G P × F` onto the charted total space of `Q`.
* `TauCeti.AssociatedBundle.pullbackProjDiffeomorph_apply` and
  `TauCeti.AssociatedBundle.pullbackProjDiffeomorph_symm_apply`: `Φ` and its inverse on points.
* `TauCeti.AssociatedBundle.proj_pullbackProjDiffeomorph`: `π_Q ∘ Φ = q`, at each point.
* `TauCeti.AssociatedBundle.pullbackProjDiffeomorph_smul`: `Φ` is equivariant for the diagonal
  action on the source and the principal action on the target.
* `TauCeti.AssociatedBundle.pullbackProjSection`: the tautological section `m ↦ m` of the
  bundle `Q ×_G F` over `M`, and `TauCeti.AssociatedBundle.contMDiff_pullbackProjSection`:
  it is `C^n`.
* `TauCeti.AssociatedBundle.sectionFunction_pullbackProjSection_eq_iff` and
  `TauCeti.AssociatedBundle.pullbackProjDiffeomorph_symm_snd_eq_iff`: the second coordinate of
  `Φ⁻¹ (m, y)` is the `w` with `[y, w] = m`.
* `TauCeti.AssociatedBundle.mfderiv_pullbackProjDiffeomorph_fundamental`: the derivative of `Φ`
  sends `(x ξ, -X_ξ(v))` to the fundamental vector of `ξ` on `Q` at `Φ (x, v)`.
* `TauCeti.AssociatedBundle.surjective_totalSpaceMk_mk` and
  `TauCeti.AssociatedBundle.isSubmersion_totalSpaceMk_mk`: `q` is a surjective submersion.

## Implementation notes

The fibre of `Q` over `Φ (x, v)` is that of `P` over the projection of `[x, v]`, which is the base
point of `x` only up to an equation (`TauCeti.ManifoldTotalSpace.homeomorph` does not unfold), so
`Φ` transports `x` along it. The forward map is smooth by the universal property of the pull-back
(`TauCeti.ManifoldTotalSpace.contMDiff_pullback_iff`). The second coordinate of the inverse is the
equivariant function `TauCeti.AssociatedBundle.sectionFunction` of the tautological section, so it
is smooth by `TauCeti.AssociatedBundle.contMDiff_sectionFunction`; the section itself is smooth
since Tau Ceti's comparison `TauCeti.AssociatedBundle.pullbackHomeomorph` of `Q ×_G F` with the
pull-back of `M` to `M` is smooth (`TauCeti.AssociatedBundle.contMDiff_pullbackHomeomorph_iff`).

Tau Ceti's lemmas composing a submersion with a local diffeomorphism need one model on both
sides, and `Φ` changes the model. So the submersion property of `q` is read off its derivative,
which is surjective as that of `π_Q` composed with an isomorphism; Tau Ceti's
`ContMDiff.isSubmersionOfComplement_of_surjective_mfderiv` turns this into a submersion, for
finite-dimensional manifolds without boundary.

The derivative of `Φ` on fundamental vectors comes from the chain rule along the orbit map of the
diagonal action, which `Φ` turns into the orbit map of `Q` (`pullbackProjDiffeomorph_smul`). Its
second component `g ↦ g⁻¹ • v` has derivative `ξ ↦ -X_ξ(v)` at `1`, by
`TauCeti.mfderiv_inv_smul_one_apply`.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter I, §5 (associated bundles).
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §6.3.
-/

public section

noncomputable section

open Bundle MulOpposite TauCeti
open scoped Manifold ContDiff

namespace TauCeti.AssociatedBundle

section

variable {n : ℕ∞ω} {𝕜 B G F : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] {HG : Type*} [TopologicalSpace HG]
  {IG : ModelWithCorners 𝕜 EG HG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners 𝕜 EF HF} [TopologicalSpace F] [ChartedSpace HF F] [MulAction G F]
  [ContinuousSMul G F]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]

/-- The projection `π_M` of the associated bundle, as a `C^n` map. -/
local notation "πM" => ManifoldTotalSpace.projContMDiffMap n F (AssociatedBundle G P F) IB IF

/-- The pull-back `Q = π_M^* P` of `P` to the associated bundle. -/
local notation "Q" => (πM : ManifoldTotalSpace F (AssociatedBundle G P F) → B) *ᵖ P

variable (n IB IF) in
/-- The point `([x, v], x)` of the total space of `Q`, before transport to its charted copy. -/
def pullbackProjMk (x : ManifoldTotalSpace G P × F) : TotalSpace G Q :=
  ⟨ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)
    ⟨((ManifoldTotalSpace.homeomorph G P).symm x.1).proj,
      mk G ((ManifoldTotalSpace.homeomorph G P).symm x.1).snd x.2⟩,
    cast (congrArg P (by simp)) ((ManifoldTotalSpace.homeomorph G P).symm x.1).snd⟩

variable (n IB IF) in
/-- The projection of `([x, v], x)` is the class `[x, v]`. -/
@[simp]
theorem pullbackProjMk_proj (x : ManifoldTotalSpace G P × F) :
    (pullbackProjMk n IB IF x).proj =
      ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)
        ⟨((ManifoldTotalSpace.homeomorph G P).symm x.1).proj,
          mk G ((ManifoldTotalSpace.homeomorph G P).symm x.1).snd x.2⟩ := (rfl)

variable (n IB IF) in
/-- The image of `([x, v], x)` in the total space of `P` is `x`. -/
@[simp]
theorem lift_pullbackProjMk (x : ManifoldTotalSpace G P × F) :
    Pullback.lift πM (pullbackProjMk n IB IF x) = (ManifoldTotalSpace.homeomorph G P).symm x.1 := by
  refine (Pullback.lift_mk _ _ _).trans ?_
  exact (TotalSpace.mk_cast (by simp) _).trans (TotalSpace.eta _)

/-- **The quotient map onto the associated bundle is surjective**: every point of `P ×_G F` is a
class `[x, v]`. -/
theorem surjective_totalSpaceMk_mk :
    Function.Surjective fun x : ManifoldTotalSpace G P × F ↦
      ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)
        ⟨((ManifoldTotalSpace.homeomorph G P).symm x.1).proj,
          mk G ((ManifoldTotalSpace.homeomorph G P).symm x.1).snd x.2⟩ := by
  intro y
  obtain ⟨⟨p, v⟩, hp⟩ := (isOpenQuotientMap_totalSpaceMk_mk G P F).surjective
    ((ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)).symm y)
  refine ⟨(ManifoldTotalSpace.homeomorph G P p, v), ?_⟩
  beta_reduce
  rw [Homeomorph.symm_apply_apply]
  exact (congrArg _ hp).trans (Homeomorph.apply_symm_apply _ _)

variable [∀ b, Nonempty (P b)]

variable (n IB IF) in
/-- The tautological section of the bundle associated with `Q` over `M`: at `m` it is `m`
itself, read in the fibre of `Q ×_G F` over `m` through Tau Ceti's `pullbackEquiv`. -/
def pullbackProjSection (m : ManifoldTotalSpace F (AssociatedBundle G P F)) :
    AssociatedBundle G Q F m :=
  (pullbackEquiv πM m).symm ((ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)).symm m).snd

variable (n IB IF) in
/-- Read in the fibre of `M` over `π_M m`, the tautological section at `m` is `m`. -/
@[simp]
theorem pullbackEquiv_pullbackProjSection (m : ManifoldTotalSpace F (AssociatedBundle G P F)) :
    pullbackEquiv πM m (pullbackProjSection n IB IF m) =
      ((ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)).symm m).snd :=
  Equiv.apply_symm_apply _ _

variable (n IB IF) in
/-- The tautological section is `C^n`, as a map into the charted total space of `Q ×_G F`. -/
theorem contMDiff_pullbackProjSection :
    ContMDiff (IB.prod IF) ((IB.prod IF).prod IF) n fun m ↦
      ManifoldTotalSpace.homeomorph F (AssociatedBundle G Q F)
        ⟨m, pullbackProjSection n IB IF m⟩ := by
  rcases isEmpty_or_nonempty F with hF | hF
  · -- With `F` empty, so is `M`.
    intro m
    obtain ⟨-, w, -⟩ :=
      exists_mk ((ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)).symm m).snd
    exact isEmptyElim w
  refine (contMDiff_pullbackHomeomorph_iff πM).2 <|
    (ManifoldTotalSpace.contMDiff_pullback_iff πM (πM).contMDiff).2
      ⟨contMDiff_id.congr fun m ↦ by simp only [pullbackHomeomorph_apply, id], ?_⟩
  refine contMDiff_id.congr fun m ↦ ?_
  rw [pullbackHomeomorph_apply]
  dsimp only
  rw [pullbackEquiv_pullbackProjSection]
  -- The image in `M` of `⟨m, a⟩` is `⟨π_M m, a⟩` by definition, and `π_M m` is the projection of
  -- the point of `M` that `m` stands for; `Pullback.lift_mk` does not rewrite here.
  exact (ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)).apply_symm_apply m

/-- The equivariant function of the tautological section takes the value `w` at a point
`z = (m, y)` of the total space of `Q` exactly when `m` is the class `[y, w]`, with `y` read in
the total space of `P`. -/
theorem sectionFunction_pullbackProjSection_eq_iff (z : TotalSpace G Q) (w : F) :
    sectionFunction (pullbackProjSection n IB IF) z = w ↔
      (ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)).symm z.proj =
        ⟨(Pullback.lift πM z).proj, mk G (Pullback.lift πM z).snd w⟩ := by
  obtain ⟨m, y⟩ := z
  rw [sectionFunction_eq_iff, ← (pullbackEquiv πM m).injective.eq_iff,
    pullbackEquiv_pullbackProjSection, pullbackEquiv_mk πM m y w]
  have key (t : TotalSpace F (AssociatedBundle G P F)) (a : AssociatedBundle G P F t.proj) :
      a = t.snd ↔ t = ⟨t.proj, a⟩ := by
    rw [eq_comm, ← TotalSpace.mk_inj (b := t.proj)]
  -- The image of `⟨m, y⟩` in `P` is `⟨π_M m, y⟩` by definition, and `π_M m` is the projection
  -- of the point of `M` that `m` stands for; `Pullback.lift_mk` does not rewrite here.
  exact key _ _

variable [LieGroup IG n G] [ContMDiffSMul IG IF n G F]

variable (n IB IG IF) in
/-- **`P × F` is the pull-back of `P` to the associated bundle.** The `C^n` diffeomorphism
`(x, v) ↦ ([x, v], x)` from `P × F` onto the total space of the pull-back `Q = π_M^* P` of `P` to
`M = P ×_G F`. -/
def pullbackProjDiffeomorph :
    (ManifoldTotalSpace G P × F) ≃ₘ^n⟮(IB.prod IG).prod IF, (IB.prod IF).prod IG⟯
      ManifoldTotalSpace G Q where
  toFun x := ManifoldTotalSpace.homeomorph G Q (pullbackProjMk n IB IF x)
  invFun z :=
    (ManifoldTotalSpace.homeomorph G P
        (Pullback.lift πM ((ManifoldTotalSpace.homeomorph G Q).symm z)),
      sectionFunction (pullbackProjSection n IB IF) ((ManifoldTotalSpace.homeomorph G Q).symm z))
  left_inv x := by
    refine Prod.ext ?_ ?_
    · simp [lift_pullbackProjMk]
    · refine (sectionFunction_pullbackProjSection_eq_iff _ _).2 ?_
      rw [Homeomorph.symm_apply_apply, lift_pullbackProjMk, pullbackProjMk_proj,
        Homeomorph.symm_apply_apply]
  right_inv z := by
    obtain ⟨y, rfl⟩ := (ManifoldTotalSpace.homeomorph G Q).surjective z
    simp only [Homeomorph.symm_apply_apply]
    congr 1
    refine Pullback.totalSpace_ext ?_ ?_
    · rw [pullbackProjMk_proj, Homeomorph.symm_apply_apply,
        ← (sectionFunction_pullbackProjSection_eq_iff y _).1 rfl, Homeomorph.apply_symm_apply]
    · rw [lift_pullbackProjMk, Homeomorph.symm_apply_apply]
  contMDiff_toFun := by
    refine (ManifoldTotalSpace.contMDiff_pullback_iff πM (πM).contMDiff).2 ⟨?_, ?_⟩
    · exact contMDiff_totalSpaceMk_mk n G F IB IG IF P
    · simp only [lift_pullbackProjMk, Homeomorph.apply_symm_apply]
      exact contMDiff_fst
  contMDiff_invFun := by
    refine (ManifoldTotalSpace.contMDiff_pullbackLift n IG πM (πM).contMDiff).prodMk ?_
    exact contMDiff_sectionFunction _ (contMDiff_pullbackProjSection n IB IF)

/-- `Φ (x, v)` is the point `([x, v], x)`. -/
theorem pullbackProjDiffeomorph_apply (x : ManifoldTotalSpace G P × F) :
    pullbackProjDiffeomorph n IB IG IF x =
      ManifoldTotalSpace.homeomorph G Q (pullbackProjMk n IB IF x) := (rfl)

/-- The inverse of `Φ` sends `(m, y)` to `(y, w)` with `[y, w] = m`. -/
theorem pullbackProjDiffeomorph_symm_apply (z : ManifoldTotalSpace G Q) :
    (pullbackProjDiffeomorph n IB IG IF).symm z =
      (ManifoldTotalSpace.homeomorph G P
          (Pullback.lift πM ((ManifoldTotalSpace.homeomorph G Q).symm z)),
        sectionFunction (pullbackProjSection n IB IF)
          ((ManifoldTotalSpace.homeomorph G Q).symm z)) := (rfl)

/-- The second coordinate of `Φ⁻¹ z`, for `z = (m, y)`, is `w` exactly when `m` is the class
`[y, w]`, with `y` read in the total space of `P`. -/
theorem pullbackProjDiffeomorph_symm_snd_eq_iff (z : ManifoldTotalSpace G Q) (w : F) :
    ((pullbackProjDiffeomorph n IB IG IF).symm z).2 = w ↔
      (ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)).symm
          ((ManifoldTotalSpace.homeomorph G Q).symm z).proj =
        ⟨(Pullback.lift πM ((ManifoldTotalSpace.homeomorph G Q).symm z)).proj,
          mk G (Pullback.lift πM ((ManifoldTotalSpace.homeomorph G Q).symm z)).snd w⟩ := by
  rw [pullbackProjDiffeomorph_symm_apply, sectionFunction_pullbackProjSection_eq_iff]

/-- **The projection of `Q` composed with `Φ` is the quotient map** `(x, v) ↦ [x, v]`. -/
-- Not `@[simp]`: at a point `(homeomorph G P p, v)` it leaves a dependent pair that `simp` cannot
-- reduce, where `proj_pullbackProjDiffeomorph_homeomorph` gives `[p, v]`.
theorem proj_pullbackProjDiffeomorph (x : ManifoldTotalSpace G P × F) :
    ((ManifoldTotalSpace.homeomorph G Q).symm (pullbackProjDiffeomorph n IB IG IF x)).proj =
      ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)
        ⟨((ManifoldTotalSpace.homeomorph G P).symm x.1).proj,
          mk G ((ManifoldTotalSpace.homeomorph G P).symm x.1).snd x.2⟩ := by
  rw [pullbackProjDiffeomorph_apply, Homeomorph.symm_apply_apply, pullbackProjMk_proj]

/-- The projection of `Φ (p, v)` is the class `[p, v]`, for a point `p` of the total space
of `P`. -/
@[simp]
theorem proj_pullbackProjDiffeomorph_homeomorph (p : TotalSpace G P) (v : F) :
    ((ManifoldTotalSpace.homeomorph G Q).symm
        (pullbackProjDiffeomorph n IB IG IF (ManifoldTotalSpace.homeomorph G P p, v))).proj =
      ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F) ⟨p.proj, mk G p.snd v⟩ := by
  rw [proj_pullbackProjDiffeomorph, Homeomorph.symm_apply_apply]

/-- The image of `Φ (p, v)` in the total space of `P` is `p`. -/
@[simp]
theorem lift_pullbackProjDiffeomorph_homeomorph (p : TotalSpace G P) (v : F) :
    Pullback.lift πM ((ManifoldTotalSpace.homeomorph G Q).symm
        (pullbackProjDiffeomorph n IB IG IF (ManifoldTotalSpace.homeomorph G P p, v))) = p := by
  rw [pullbackProjDiffeomorph_apply, Homeomorph.symm_apply_apply, lift_pullbackProjMk,
    Homeomorph.symm_apply_apply]

/-- **`Φ` is equivariant**, for the diagonal action `(x, v) · g = (x · g, g⁻¹ • v)` on
`P × F` and the principal action on `Q`. -/
theorem pullbackProjDiffeomorph_smul (g : G) (x : ManifoldTotalSpace G P × F) :
    pullbackProjDiffeomorph n IB IG IF (op g • x.1, g⁻¹ • x.2) =
      op g • pullbackProjDiffeomorph n IB IG IF x := by
  rw [pullbackProjDiffeomorph_apply, pullbackProjDiffeomorph_apply,
    ManifoldTotalSpace.smul_homeomorph]
  congr 1
  refine Pullback.totalSpace_ext ?_ ?_
  · rw [pullbackProjMk_proj, pullbackProjMk_proj, ManifoldTotalSpace.homeomorph_symm_smul,
      mk_smul_inv_smul]
  · rw [lift_pullbackProjMk, ManifoldTotalSpace.homeomorph_symm_smul]
    -- `Pullback.lift` of a point `⟨m, s⟩` is `⟨πM m, s⟩` by definition; `Pullback.lift_mk` does not
    -- rewrite here, since the fibre of `Q` is not reducibly that of `P`.
    exact congrArg (fun y : TotalSpace G P ↦ (⟨y.proj, op g • y.snd⟩ : TotalSpace G P))
      (lift_pullbackProjMk n IB IF x).symm

/-- **`Φ` carries fundamental fields to fundamental fields.** The derivative of `Φ` at `(x, v)`
sends the fundamental vector `(x ξ, -X_ξ(v))` of `ξ` for the diagonal action to the fundamental
vector of `ξ` for the principal action on `Q` at `Φ (x, v)`. -/
theorem mfderiv_pullbackProjDiffeomorph_fundamental (hn : 1 ≤ n) (ξ : GroupLieAlgebra IG G)
    (x : ManifoldTotalSpace G P × F) :
    mfderiv ((IB.prod IG).prod IF) ((IB.prod IF).prod IG) (pullbackProjDiffeomorph n IB IG IF) x
        (rightFundamentalVectorField (IB.prod IG) ξ x.1, -fundamentalVectorField IF ξ x.2) =
      rightFundamentalVectorField ((IB.prod IF).prod IG) ξ
        (pullbackProjDiffeomorph n IB IG IF x) := by
  have hn₀ : n ≠ 0 := (zero_lt_one.trans_le hn).ne'
  have : LieGroup IG 1 G := .of_le hn
  have : ContMDiffSMul IG IF 1 G F := .of_le hn
  have h₁ : MDifferentiableAt IG (IB.prod IG) (fun g : G ↦ op g • x.1) 1 :=
    PrincipalBundle.mdifferentiableAt_orbit (n := 1) one_ne_zero x.1 1
  have horbit : MDifferentiableAt IG IF (fun g : G ↦ g • x.2) 1 :=
    (ContMDiffSMul.contMDiff_smul_const (n := 1) x.2).mdifferentiableAt one_ne_zero
  have h₂ : MDifferentiableAt IG IF (fun g : G ↦ g⁻¹ • x.2) 1 :=
    horbit.comp_of_eq 1 ((contMDiff_inv IG 1).mdifferentiableAt one_ne_zero) inv_one
  -- The orbit map of `x` for the diagonal action sends `ξ` to `(x ξ, -X_ξ(v))`.
  have hγ : mfderiv IG ((IB.prod IG).prod IF) (fun g : G ↦ (op g • x.1, g⁻¹ • x.2)) 1 ξ =
      (rightFundamentalVectorField (IB.prod IG) ξ x.1, -fundamentalVectorField IF ξ x.2) := by
    rw [mfderiv_prodMk h₁ h₂]
    -- `(f.prod g) ξ` is `(f ξ, g ξ)` by definition; `ContinuousLinearMap.prod_apply` does not
    -- rewrite, since the tangent space of the product model is not reducibly a product.
    exact Prod.ext (rightFundamentalVectorField_apply ξ x.1).symm
      (mfderiv_inv_smul_one_apply horbit ξ)
  -- The orbit map of `Φ x` is `Φ` composed with the orbit map of `x` for the diagonal action.
  have hcomp : (fun g : G ↦ op g • pullbackProjDiffeomorph n IB IG IF x) =
      pullbackProjDiffeomorph n IB IG IF ∘ fun g : G ↦ (op g • x.1, g⁻¹ • x.2) :=
    funext fun g ↦ (pullbackProjDiffeomorph_smul g x).symm
  calc _ = mfderiv ((IB.prod IG).prod IF) ((IB.prod IF).prod IG)
        (pullbackProjDiffeomorph n IB IG IF) x (mfderiv IG ((IB.prod IG).prod IF)
          (fun g : G ↦ (op g • x.1, g⁻¹ • x.2)) 1 ξ) := by
        -- After the rewrite, the two vectors differ only in the tangent space they are typed in.
        rw [hγ]
        rfl
    _ = _ := by
        rw [rightFundamentalVectorField_apply, hcomp]
        exact (mfderiv_comp_apply_of_eq 1
          ((pullbackProjDiffeomorph n IB IG IF).mdifferentiable hn₀ x) (h₁.prodMk h₂)
          (by simp) ξ).symm

end

section Submersion

/-! ### The quotient map is a submersion -/

variable {n : ℕ∞ω} {𝕜 B G F : Type*} [RCLike 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [FiniteDimensional 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [IB.Boundaryless]
  [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB n B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] [FiniteDimensional 𝕜 EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners 𝕜 EG HG} [IG.Boundaryless]
  [Group G] [TopologicalSpace G] [ChartedSpace HG G] [LieGroup IG n G]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] [FiniteDimensional 𝕜 EF]
  {HF : Type*} [TopologicalSpace HF] {IF : ModelWithCorners 𝕜 EF HF} [IF.Boundaryless]
  [TopologicalSpace F] [ChartedSpace HF F] [IsManifold IF n F] [MulAction G F]
  [ContinuousSMul G F] [ContMDiffSMul IG IF n G F]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P] [∀ b, Nonempty (P b)]
  [ContMDiffFiberBundle n G P IB IG]

/-- The projection `π_M` of the associated bundle, as a `C^n` map. -/
local notation "πM" => ManifoldTotalSpace.projContMDiffMap n F (AssociatedBundle G P F) IB IF

/-- The pull-back `Q = π_M^* P` of `P` to the associated bundle. -/
local notation "Q" => (πM : ManifoldTotalSpace F (AssociatedBundle G P F) → B) *ᵖ P

/-- **The quotient map onto the associated bundle is a submersion.** For a `C^n` principal bundle
`P` (`1 ≤ n`) with finite-dimensional base and structure group, and a `C^n` action of `G` on a
finite-dimensional manifold `F`, all without boundary, the map `(x, v) ↦ [x, v]` from `P × F`
onto `P ×_G F` is a `C^n` submersion. -/
theorem isSubmersion_totalSpaceMk_mk (hn : 1 ≤ n) :
    Manifold.IsSubmersion ((IB.prod IG).prod IF) (IB.prod IF) n
      fun x : ManifoldTotalSpace G P × F ↦
        ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)
          ⟨((ManifoldTotalSpace.homeomorph G P).symm x.1).proj,
            mk G ((ManifoldTotalSpace.homeomorph G P).symm x.1).snd x.2⟩ := by
  have hn₀ : n ≠ 0 := (zero_lt_one.trans_le hn).ne'
  have : ContMDiffFiberBundle n F (AssociatedBundle G P F) IB IF := contMDiffFiberBundle IG
  -- The quotient map is the projection of `Q` composed with the diffeomorphism `Φ`.
  set Φ := pullbackProjDiffeomorph n IB IG IF (G := G) (F := F) (P := P)
  have hπ := ManifoldTotalSpace.isSubmersion_proj n G Q (IB.prod IF) IG
  rw [← funext (proj_pullbackProjDiffeomorph (n := n) (IB := IB) (IG := IG) (IF := IF))]
  refine (ContMDiff.isSubmersionOfComplement_of_surjective_mfderiv
    (hπ.contMDiff.comp Φ.contMDiff) hn fun x ↦ ?_).isSubmersion
  rw [mfderiv_comp x (hπ.contMDiff.mdifferentiableAt hn₀) (Φ.mdifferentiable hn₀ x)]
  exact (hπ.surjective_mfderiv hn₀ _).comp
    ((Φ.isLocalDiffeomorph x).isInvertible_mfderiv hn₀).surjective

end Submersion

end TauCeti.AssociatedBundle

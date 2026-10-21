/-ai
If H is a retraction of the function space of the universal domain, then i-arrow composed with H composed with j-arrow is a retraction of the universal domain.

The composite of that conjugate with itself is rewritten by associativity, by the identity j-arrow composed with i-arrow, by cancellation of the identity, and by the retraction equation for H.

If H lies below the identity on the function space, then the same conjugate lies below the identity on the universal domain.

Monotonicity of composition puts the conjugate below i-arrow composed with the identity composed with j-arrow. That composite is i-arrow composed with j-arrow, which lies below the identity.

If H is a projection of the function space, then the conjugate is a projection of the universal domain.

It is the pair of the retraction and the identity comparison just obtained.

The combinator sub on the universal domain is a projection.

This is the conjugation theorem applied to the projection property of subApprox.

The combinator sub on the universal domain is finitary.

Finitariness of subApprox supplies a domain and an order isomorphism of its elements with the fixed points of subApprox. Transport that isomorphism along the order isomorphism of the fixed points of sub with the fixed points of subApprox.

The combinator sub on the universal domain is a finitary projection.

It is the pair of the projection and finitariness theorems.

If a is a retraction, then a fixes the value at any element z of a composed with g composed with a.

Rewrite by the composition law for element maps and by the retraction equation for a.

If d is a polymorphic type, then sub fixes the value of d at every element z.

The sandwich lemma for the retraction sub, applied to d, rewrites by the polymorphism equation.

If sub fixes an element w, then the approximable map decoded from j-arrow of w is a finitary projection.

Apply the criterion that a self-map equal to its sub is a finitary projection. Transport of the fixed point says that subApprox fixes j-arrow of w. Applying the passage to approximable maps and rewriting by the element-map formula for subApprox and the approximable-map formula for the sub-filter gives that self-equality.

For every element z, the approximable map decoded from j-arrow of sub of z is a finitary projection.

The retraction sub fixes sub of z, so the previous theorem applies.

The uncurried product of d, evaluated at a pair of a function-space element and an element t, equals the type decoded from sub of d of sub of t, applied to the underlying map of that function-space element at sub of t.

Simplify by the element-map laws for composition, pairing, and the two projections, by the two pair equations, and by the evaluation law.

The closed form of the product of d at a self-map f, evaluated at t, equals that same decoded type applied to f at sub of t.

Simplify by the element-map laws for composition and pairing and by the evaluation law.

Transporting the function-space product of d through the function-space equivalence recovers the closed form of the product at the underlying map.

Compare element maps. At an element t, unfold the product and rewrite by the currying law, the uncurried evaluation formula, and the closed-form evaluation formula.

The function-space product relates a set X of approximable maps to a set W if and only if both are neighbourhoods of the function space and the section of the uncurried product at X lies in W.

This is the currying relation law.

The section of the uncurried product at a neighbourhood X relates a neighbourhood Y to a set Z if and only if the closed form of the product, at the approximable map of the principal of X, sends the principal of Y into Z.

Rewrite by the section relation, by the principal form of the relation at the product neighbourhood, by the identification of the pair of principals with the principal of the product neighbourhood, and by the uncurried and closed-form evaluation formulae.

The image of a function-space element x under the product lies in a set Y if and only if Y is a neighbourhood and the closed form of the product at the approximable map of x lies in Y.

Replace the image element by the filter of its approximable map. Membership in that filter is membership of the transported map, and the transport theorem identifies the map with the closed form.

If Y is a neighbourhood, x lies in X, X is contained in Y, and the product relates X to itself, then the image of x lies in Y.

This is the general membership lemma for a self-related neighbourhood, applied to the product.

If sub relates a neighbourhood T to itself, then sub fixes the principal element of T.

The two inequalities are antisymmetry. The inequality toward the principal is the identity comparison for the projection sub. The reverse inequality is the principal bound coming from the membership form of the self-relation.

If t is fixed by sub and a neighbourhood T0 lies in t, then some neighbourhood T is self-related by sub, lies in t, and is contained in T0.

The fixed-point hypothesis puts T0 in the image of t. The step-closure formula for the finitary projection sub supplies the neighbourhood T.

The principal elements of the self-consistent family of a sub-fixed element t are directed.

At the intersection of the two neighbourhoods, which lies in t, the previous existence theorem supplies a self-related neighbourhood contained in that intersection and still in t. Its principal bounds both given principals by the principal comparison and the two inclusions in the intersection.

A sub-fixed element t is the directed supremum of the principals of its self-consistent family.

Compare membership of a neighbourhood Z. If Z lies in t, the existence theorem supplies a self-related neighbourhood in t contained in Z, and its principal witnesses the directed-sup membership. Conversely, a witness principal contributes a neighbourhood contained in Z that lies in t, and upward closure of t puts Z in t.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.subU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.subUFixIso
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.subUFixIsoSubFixed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.IsPolymorphicType
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.piDUncurried
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.piD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.piDApply
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.piU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.piUFixIso
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.scFamily
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.scPrincipal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.piDTypeMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.piDType
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.toElementMap_subU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.jArrow_comp_iArrow_apply
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.subApprox_fix_of_subU_fix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.subU_fix_of_subApprox_fix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.toElementMap_piU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.piD_fix_of_piU_fix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.piU_fix_of_piD_fix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.BasicInst38

@[expose] public section

/-!
# Exercise 8.27 (Scott 1981, PRG-19) — Donahue's polymorphic/infinite products over `𝒰`

> **Exercise 8.27.** (Suggested by James Donahue.) Finite cartesian products of domains are formed
> by the `D₀ × D₁`-construct we have used so often. The problem is to define — computably — some
> *infinite* cartesian products. In particular, as applied to the universal domain `𝒰`, the
> combinator `sub` is to be regarded as a finitary projection of `𝒰` whose fixed points are
> exactly *all* the finitary projections. A map `d = sub∘d∘sub` can be regarded as a *polymorphic
> type* (because, whenever `t` is a finitary projection (`=` type), then so is `d(t)`). The
> *continuous product* of *all* these types would be the domain of all approximable functions `x`
> such that `x(t) = d(t)(x(t))` for all types `t`. (Why does this equation mean that `x` is in the
> product?) Define `Π` as a combinator by `Π = λd λx λt. sub(d(sub(t)))(x(sub(t)))`. Show that for
> `d` a polymorphic type, `Π(d)` is a type. (Hint: it is easy to check that `Π(d)` is a projection;
> the problem is to show it is finitary.)

This is the **last exercise in the entire book**.

## What this file formalizes

**Step 1 — `sub` regarded as a combinator on `𝒰` itself.** Theorem 8.6's `sub : (E→E)→(E→E)`
(`Theorem86.lean`) is a per-map operation; Theorem 8.6(b) packages it as a genuine approximable
self-map `subApprox : (𝒰→𝒰) → (𝒰→𝒰)`. To get "`sub` regarded as a finitary projection *of* `𝒰`"
(the exercise's own phrasing), we conjugate `subApprox` through the fixed pair `i_→ : (𝒰→𝒰)→𝒰`,
`j_→ : 𝒰→(𝒰→𝒰)` (Definition 8.9) exactly as `Definition 8.9` itself builds `a→b` from `λf.b∘f∘a` —
`subU := i_→ ∘ subApprox ∘ j_→ : 𝒰 → 𝒰`. We show `subU` is a genuine finitary projection
(`isFinitaryProjection_subU`) whose fixed points are exactly the finitary projections of `𝒰`
(`subUFixIso`, composed with Theorem 8.6(a)'s own `{f ∣ sub f=f} = ` finitary projections
characterization) — a direct formalization of the exercise's opening sentence.

**Step 2 — polymorphic types.** `IsPolymorphicType d := subU∘d∘subU = d`, Scott's `d = sub∘d∘sub`.
The exercise's own justification ("whenever `t` is a finitary projection, then so is `d(t)`") is
`polymorphicType_apply_mem_fix`: for `d` polymorphic and *any* `z` (not just a "type" `t`),
`d(z) ∈ Fix(subU)`.

**Step 3 — the `Π` combinator.** Built by direct transcription of Scott's formula
`Π(d)(x)(t) = sub(d(sub(t)))(x(sub(t)))` via `curry`/`evalMap`/`paired` (mirroring
`Exercise825FixedPoint.lean`'s `RMap` recipe), giving `piD d : (𝒰→𝒰) → (𝒰→𝒰)`, then conjugated
through `i_→, j_→` exactly as in Step 1 to land `piU d : 𝒰 → 𝒰` — "`Π(d)`, regarded as living in
`𝒰`," matching that "type" means a self-map *of `𝒰`* (not of `𝒰→𝒰`).

**Step 4 — "it is easy to check that `Π(d)` is a projection" (Scott's own hint).** Proved here
**unconditionally for every `d : 𝒰 → 𝒰`** (not just polymorphic `d`!) — a genuinely easier and
stronger fact than what Scott's theorem statement asks for, made possible because `Π`'s own
formula *already* re-projects through `sub` at every occurrence of the bound type variable `t`
(`sub(d(sub(t)))`, not bare `d(sub(t))`): this makes the "type" fed to the application step
*automatically* a genuine finitary projection regardless of whether `d` itself is polymorphic
(`isFinitaryProjection_decode_subU`), which is exactly what both halves of the projection proof
need.

**Step 5 (Exercise 8.27(b)(0)) — reduce "`piU d` is finitary" to "`piD d` is finitary."**
`piUFixIso : Fix(piU d) ≃o Fix(piD d)`, built by literally copying Step 1's `subUFixIso` recipe
(`piU d = i_→∘(piD d)∘j_→` has the same shape as `subU = i_→∘subApprox∘j_→`). Packaged as
`isFinitary_piU_of_isFinitary_piD`, so the remaining work (Exercise 8.27(b)(1)–(b)(4), **not**
attempted here) is exactly to prove `IsFinitary (piD d)` for `d` polymorphic.

**"The problem is to show it is finitary" (Scott's own hint) — the core content, deliberately NOT
attempted.** See the discussion at the bottom of this file for why, and `HANDOFF.md`'s 2026-07-07
checkpoint for the planned proof route (Exercise 8.27(b)(1)–(b)(5), pivoting on Theorem 8.5's
step-closure formula rather than an ad hoc dependent-product construction).

Axiom audit: everything here mentions `𝒰`, hence inherits `𝒰`'s own `Classical.choice` footprint
(`⊆ {propext, Classical.choice, Quot.sound}`, not new).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

/-! ## Step 1: `subU`, `sub` regarded as a combinator on `𝒰` itself -/


/-! ### A reusable gadget: conjugating a projection of `(𝒰→𝒰)` through `i_→, j_→` gives a
projection of `𝒰`. Used for both `subU` (from `subApprox`) and, later, `piU d` (from `piD d`). -/

/-- **Conjugating a retraction of `(𝒰→𝒰)` through `i_→, j_→` gives a retraction of `𝒰`.** Pure
associativity plus `j_→∘i_→ = I` (`jArrow_comp_iArrow`) and `H∘H=H`. -/
theorem isRetraction_conjArrow {H : ApproximableMap (funSpace U U) (funSpace U U)}
    (hH : IsRetraction H) : IsRetraction (iArrow.comp (H.comp jArrow)) := by
  show (iArrow.comp (H.comp jArrow)).comp (iArrow.comp (H.comp jArrow)) =
    iArrow.comp (H.comp jArrow)
  rw [comp_assoc iArrow (H.comp jArrow) (iArrow.comp (H.comp jArrow)),
    comp_assoc H jArrow (iArrow.comp (H.comp jArrow)),
    ← comp_assoc jArrow iArrow (H.comp jArrow), jArrow_comp_iArrow, idMap_comp,
    ← comp_assoc H H jArrow, hH]

/-- **Conjugating a `≤ I`-map of `(𝒰→𝒰)` through `i_→, j_→` gives a `≤ I`-map of `𝒰`.** Chains
`comp_mono_gen` with `i_→∘j_→ ≤ I` (`iArrow_comp_jArrow_le`, Definition 8.9). -/
theorem le_idMap_conjArrow {H : ApproximableMap (funSpace U U) (funSpace U U)}
    (hH : H ≤ idMap (funSpace U U)) : iArrow.comp (H.comp jArrow) ≤ idMap U :=
  calc iArrow.comp (H.comp jArrow)
      ≤ iArrow.comp ((idMap (funSpace U U)).comp jArrow) :=
        comp_mono_gen le_rfl (comp_mono_gen hH le_rfl)
    _ = iArrow.comp jArrow := by rw [idMap_comp]
    _ ≤ idMap U := iArrow_comp_jArrow_le

/-- **Conjugating a projection of `(𝒰→𝒰)` through `i_→, j_→` gives a projection of `𝒰`.** -/
theorem isProjection_conjArrow {H : ApproximableMap (funSpace U U) (funSpace U U)}
    (hH : IsProjection H) : IsProjection (iArrow.comp (H.comp jArrow)) :=
  ⟨isRetraction_conjArrow hH.1, le_idMap_conjArrow hH.2⟩

/-- **`subU` is a projection.** -/
theorem isProjection_subU : IsProjection subU :=
  isProjection_conjArrow Sub8_6.isProjection_subApprox


/-- **`subU` is finitary.** Composes `subUFixIso` with Theorem 8.6(b)(ii)'s `isFinitary_subApprox`. -/
theorem isFinitary_subU : IsFinitary subU := by
  obtain ⟨β, F, ⟨iso⟩⟩ := Sub8_6.isFinitary_subApprox (E := U)
  exact ⟨β, F, ⟨subUFixIso.trans iso⟩⟩

/-- **`sub`, regarded as a combinator on `𝒰` itself, is a finitary projection** (Exercise 8.27's
opening sentence, in full). -/
theorem isFinitaryProjection_subU : IsFinitaryProjection subU :=
  ⟨isProjection_subU, isFinitary_subU⟩


/-! ## Step 2: polymorphic types -/


/-- If `a` is idempotent and `f = a∘g∘a` for *some* `g`, then `a(f(z)) = f(z)` for *every* `z` —
i.e. any map "sandwiched" between two copies of an idempotent `a` always lands in `Fix(a)`,
regardless of what `g` is. (General form of the pattern behind Exercise 8.26's
`translateApp_hasType`, but derived automatically rather than assumed as a hypothesis.) -/
theorem toElementMap_mem_fix_of_isRetraction_sandwich {a g : ApproximableMap U U}
    (ha : IsRetraction a) (z : U.Element) :
    a.toElementMap ((a.comp (g.comp a)).toElementMap z) = (a.comp (g.comp a)).toElementMap z := by
  rw [toElementMap_comp, ← toElementMap_comp a a, ha]

/-- **The exercise's own justification, formalized**: "whenever `t` is a finitary projection, then
so is `d(t)`" — in fact, for `d` a polymorphic type, `d(z) ∈ Fix(subU)` for *every* `z`, not just
for `z` a "type". -/
theorem polymorphicType_apply_mem_fix {d : ApproximableMap U U} (hd : IsPolymorphicType d)
    (z : U.Element) : subU.toElementMap (d.toElementMap z) = d.toElementMap z := by
  have h := toElementMap_mem_fix_of_isRetraction_sandwich isProjection_subU.1 (g := d) z
  rwa [hd] at h

/-! ## Step 4 (prerequisite): decoding `Fix(subU)` always yields a genuine finitary projection

The key fact behind "it is easy to check that `Π(d)` is a projection" (Scott's own hint): because
`subU` is idempotent, `subU(z) ∈ Fix(subU)` for *any* `z` — and `Fix(subU)` decodes, via `j_→`, to
exactly the finitary projections of `𝒰` (Step 1). Chaining these: `j_→(subU(z))`, viewed as a map
of `𝒰`, is *always* a genuine finitary projection, for *any* `z` at all, with no hypothesis on `z`
or on how it arose. This is exactly what makes `Π`'s formula `sub(d(sub(t)))(-)` well-behaved
regardless of whether `d` itself is a polymorphic type. -/

/-- **Any `j_→`-decoded fixed point of `subU` is a finitary projection of `𝒰`.** -/
theorem isFinitaryProjection_toApproxMap_jArrow_of_fix {w : U.Element}
    (hw : subU.toElementMap w = w) :
    IsFinitaryProjection (toApproxMap (jArrow.toElementMap w)) := by
  apply isFinitaryProjection_of_sub_eq_self
  have hfix := subApprox_fix_of_subU_fix hw
  have hstep := congrArg toApproxMap hfix
  rwa [Sub8_6.toElementMap_subApprox, Sub8_6.toApproxMap_subFilter] at hstep

/-- **The key lemma: `j_→(subU(z))` is always a finitary projection of `𝒰`, for any `z`.** -/
theorem isFinitaryProjection_decode_subU (z : U.Element) :
    IsFinitaryProjection (toApproxMap (jArrow.toElementMap (subU.toElementMap z))) :=
  isFinitaryProjection_toApproxMap_jArrow_of_fix
    (toElementMap_idem_of_isRetraction isProjection_subU.1 z)

/-! ## Step 3: the `Π` combinator

Scott's formula: `Π(d)(x)(t) = sub(d(sub(t)))(x(sub(t)))`. Built exactly as
`Exercise825FixedPoint.lean`'s `RMap` — a raw composite of `evalMap`/`proj`/`paired`, uncurried,
then curried. -/


theorem toElementMap_piDUncurried (d : ApproximableMap U U) (φ : (funSpace U U).Element)
    (t : U.Element) :
    (piDUncurried d).toElementMap (pair φ t) =
      (toApproxMap (jArrow.toElementMap (subU.toElementMap (d.toElementMap
          (subU.toElementMap t))))).toElementMap
        ((toApproxMap φ).toElementMap (subU.toElementMap t)) := by
  simp only [piDUncurried, toElementMap_comp, toElementMap_paired, toElementMap_proj₀,
    toElementMap_proj₁, fst_pair, snd_pair, evalMap_apply]


theorem toElementMap_piDApply (d f : ApproximableMap U U) (t : U.Element) :
    (piDApply d f).toElementMap t =
      (toApproxMap (jArrow.toElementMap (subU.toElementMap (d.toElementMap
          (subU.toElementMap t))))).toElementMap (f.toElementMap (subU.toElementMap t)) := by
  simp only [piDApply, toElementMap_comp, toElementMap_paired, evalMap_apply]

/-- **`piD d`, transported through `funSpaceEquiv`, is exactly `piDApply d`.** Mirrors
`toApproxMap_toElementMap_lamComb`/`toApproxMap_toElementMap_expMap`. -/
theorem toApproxMap_toElementMap_piD (d : ApproximableMap U U) (φ : (funSpace U U).Element) :
    toApproxMap ((piD d).toElementMap φ) = piDApply d (toApproxMap φ) := by
  apply ApproximableMap.ext_of_toElementMap
  intro t
  rw [piD, toElementMap_curry_apply, toElementMap_piDUncurried, toElementMap_piDApply]


/-! ## Step 4: "it is easy to check that `Π(d)` is a projection" — Scott's own hint

Proved **unconditionally**, for *every* `d : 𝒰 → 𝒰`, not only for `d` a polymorphic type: the
outer `sub(-)` wrapper already appearing in Scott's own formula guarantees, via
`isFinitaryProjection_decode_subU`, that the "type at `t`" fed to the application step is always a
genuine finitary projection — and that alone is exactly what both halves of the projection
property need. -/

/-! ## Exercise 8.27(b)(0): `Fix(piU d) ≃o Fix(piD d)`

Mirrors Step 1's `subUFixIso` verbatim, substituting `piD d`/`piU d` for `subApprox`/`subU`
(both are built by the identical `i_→∘(-)∘j_→` conjugation recipe, so every step transfers
unchanged). Reduces "`piU d` is finitary" to "`piD d` is finitary" — the target of Exercise
8.27(b)(1) onward — exactly as `isFinitary_subU` was obtained from `isFinitary_subApprox`. -/


/-! ## Exercise 8.27(b)(1): reduce finitariness of `piD d` to Theorem 8.5's step-closure formula

`Theorem85.lean`'s `isFinitaryProjection_of_formula` proves, for *any* approximable map `a : E → E`
on *any* neighbourhood system `E`, that Scott's step-closure formula (ii) —

  `a(x) = {Y ∈ E ∣ ∃X∈x, X⊆Y ∧ X a X}`, for every `x ∈ |E|`

— by itself (no other hypothesis on `a`) implies `IsFinitaryProjection a`, with the witness domain
`fixedNbhd a` built automatically from `a`'s own relation. Specializing `E := funSpace U U`,
`a := piD d` turns "prove `piD d` is finitary" into "prove `piD d` satisfies formula (ii)" — no
external witness system to invent. This is exactly the reduction Exercise 8.27(b)(2)–(b)(3) target;
what remains here is only to record the specialization and its corollary via Exercise 8.27(b)(0). -/

/-! ## Exercise 8.27(b)(2): unwind `piD d`'s neighbourhood relation

`piD d = curry (piDUncurried d)` uses `FunctionSpace.lean`'s *abstract* `curry` (not the Ex 7.16/
Table 5.5 recursion-theoretic coded layer). Its general relation lemma **`curry_rel`** already
exists there:

  `(curry g).rel X W ↔ ∃ hX : V₀.mem X, (funSpace V₁ V₂).mem W ∧ gSection g hX ∈ W`

reducing `(piD d).rel X W` to a literal *set membership* test `gSection (piDUncurried d) hX ∈ W`
of an actual map into the funSpace-nbhd `W` (no new proof needed — `piD_rel_iff` below is the
direct specialization). The remaining unwinding is `gSection (piDUncurried d) hX`'s own relation:
`gSection_rel` reduces it to `(piDUncurried d).rel (prodNbhd X Y) Z`, and **`rel_iff_mem_principal`**
(`Approximable.lean`) plus **`pair_principal_eq_principal_prodNbhd`** (`Exercise821.lean`, general —
pairing two principal elements is the principal element of the product nbhd) convert *that* into an
*element*-level statement, which the already-proven **`toElementMap_piDUncurried`** evaluates in
closed form purely in terms of `subU`'s and `d`'s own `toElementMap` actions (built, in its own
proof, from `evalMap_apply`, `FunctionSpace.lean`'s abstract defining relation for `eval`). This is
`gSection_piDUncurried_rel_iff` below — the genuine content of this subgoal. -/

/-- **Exercise 8.27(b)(2)(a).** `(piD d).rel X W` reduces to a literal membership test — the direct
specialization of `curry_rel` (`FunctionSpace.lean`), no new proof needed. -/
theorem piD_rel_iff (d : ApproximableMap U U) {X W : Set (ApproximableMap U U)} :
    (piD d).rel X W ↔ ∃ hX : (funSpace U U).mem X, (funSpace U U).mem W ∧
      gSection (piDUncurried d) hX ∈ W :=
  curry_rel

/-- **Exercise 8.27(b)(2)(b).** `gSection (piDUncurried d) hX`'s own relation, fully unwound to a
closed elementwise formula in terms of the already-proven closed form `piDApply` (built, in its
own proof, purely from `subU`'s and `d`'s `toElementMap` actions plus `evalMap_apply`): reduce via
`gSection_rel` to `(piDUncurried d).rel (prodNbhd X Y) Z`, then via `rel_iff_mem_principal` +
`pair_principal_eq_principal_prodNbhd` to the element pair `pair (principal hX) (principal hY)`,
then read off `toElementMap_piDUncurried`/`toElementMap_piDApply`. This is the "unwind `piD d`'s
neighbourhood relation" content of Exercise 8.27(b)(2). -/
theorem gSection_piDUncurried_rel_iff (d : ApproximableMap U U)
    {X : Set (ApproximableMap U U)} (hX : (funSpace U U).mem X) {Y Z : Set ℚ} (hY : U.mem Y) :
    (gSection (piDUncurried d) hX).rel Y Z ↔
      ((piDApply d (toApproxMap ((funSpace U U).principal hX))).toElementMap
        (U.principal hY)).mem Z := by
  rw [gSection_rel, rel_iff_mem_principal (piDUncurried d) (prod_mem_prodNbhd hX hY),
    ← pair_principal_eq_principal_prodNbhd hX hY, toElementMap_piDUncurried,
    ← toElementMap_piDApply]

/-! ## Exercise 8.27(b)(3): formula (ii) for `piD d` — substantial partial progress, not closed

**The reduction is complete and clean.** Via `Sub8_6.toFilter_toApproxMap`/`mem_toFilter`
(`mem_iff_mem_toApproxMap`) plus the already-proven `toApproxMap_toElementMap_piD`, `hii`'s LHS
`((piD d).toElementMap x).mem Y` reduces *exactly* to a literal membership test
`piDApply d (toApproxMap x) ∈ Y` (`piD_toElementMap_mem_iff`) — no abstract "element" reasoning
left, purely a statement about the actual map `piDApply d (toApproxMap x) : ApproximableMap U U`
and the actual set `Y`.

**The `⟸` half closes unconditionally**, via `Theorem85.lean`'s newly-extracted
`mem_of_exists_rel_self` (isolated from `isFinitaryProjection_of_formula`'s own proof, valid for
*any* `a : E → E` with no hypothesis) — `hii_easy_direction` below.

**The `⟹` half (the genuine mathematical content) is *not* closed here.** Attempting it exposed a
precise, previously-undocumented obstruction, recorded in full in `HANDOFF.md`'s 2026-07-07
checkpoint: given `f := piDApply d (toApproxMap x) ∈ Y` (`Y = stepFun [(Y_i,Z_i)]_i`), unwinding
each `f.rel Y_i Z_i` via `gSection_piDUncurried_rel_iff`/`toElementMap_piDApply` and Theorem 8.5's
*already-proven* formula (ii) for `subU` (Exercise 8.27(a)) and for each per-`i` "type" projection
`P_i := toApproxMap(jArrow.toElementMap(subU.toElementMap(d.toElementMap t_i)))`
(`isFinitaryProjection_decode_subU`, `t_i := subU.toElementMap (U.principal hY_i)`) produces
per-component witnesses `W_i` (`W_i ⊆ Z_i`, `P_i.rel W_i W_i`) — the natural next step is to
assemble `X := stepFun [(T_i,W_i)]_i` for domain-side nbhds `T_i ⊇ Y_i` with `t_i.mem T_i`
(continuity), to get `x.mem X` and `X ⊆ Y`. But testing `(piD d).rel X X` itself re-runs the same
unwinding *at `X`'s own `T_i`*, which feeds `s_i := subU.toElementMap (U.principal hT_i)` — **not**
`t_i` — into `d`, landing on a *different* type-projection `P_i' := toApproxMap(jArrow.toElementMap
(subU.toElementMap (d.toElementMap s_i)))`. Since `T_i ⊇ Y_i` is unavoidable (needed for `X ⊆ Y`
by `mono`), `s_i ≤ t_i` is forced (monotonicity), so `P_i' ≤ P_i` is generally a *strictly weaker*
map, and `P_i.rel W_i W_i` does not transfer to `P_i'.rel W_i W_i` for free — the self-relation
witness and the continuity witness pull `T_i` in incompatible directions with a single round of
formula (ii). The likely resolution (not attempted) mirrors `Theorem85.lean`'s *own* `(i) ⟹ (ii)`
hard direction (`exists_principal_eq_of_isRetraction_le_idMap`'s compactness-reflection argument,
~200 lines) rather than a single formula(ii)-chase: an iterative/compactness "descent" building
`T_i` as a directed limit that becomes self-consistent *in the limit*, using algebraicity
(`eq_iSupDirected_principal`) to show the descent stabilizes at a genuine finite/principal nbhd —
a comparably-sized undertaking to Theorem 8.5's hard direction, not a quick corollary of it. `d`'s
polymorphism (`IsPolymorphicType`, unused so far) is expected to enter here, but exactly how is not
yet worked out. -/

/-- **Exercise 8.27(b)(3)(a).** `hii`'s LHS, reduced to a literal membership test: no abstract
"funSpace element" reasoning left, purely `piDApply d (toApproxMap x) ∈ Y` as an actual map/set. -/
theorem piD_toElementMap_mem_iff (d : ApproximableMap U U) (x : (funSpace U U).Element)
    {Y : Set (ApproximableMap U U)} :
    ((piD d).toElementMap x).mem Y ↔
      (funSpace U U).mem Y ∧ piDApply d (toApproxMap x) ∈ Y := by
  conv_lhs => rw [← Sub8_6.toFilter_toApproxMap ((piD d).toElementMap x)]
  rw [mem_toFilter, toApproxMap_toElementMap_piD]

/-- **Exercise 8.27(b)(3), the `⟸` half — closes unconditionally, for any `d` at all.** Direct
specialization of `Theorem85.lean`'s newly-extracted `mem_of_exists_rel_self` (no hypothesis on
`a` needed) to `a := piD d`. The remaining, genuinely hard direction is documented above and in
`HANDOFF.md`; **not** attempted here. -/
theorem hii_easy_direction (d : ApproximableMap U U) (x : (funSpace U U).Element)
    {Y : Set (ApproximableMap U U)} (hYE : (funSpace U U).mem Y)
    {X : Set (ApproximableMap U U)} (hXx : x.mem X) (hXY : X ⊆ Y) (hXX : (piD d).rel X X) :
    ((piD d).toElementMap x).mem Y :=
  mem_of_exists_rel_self x hYE hXx hXY hXX

/-! ## Exercise 8.27(b)(3)(b): the `⟹` half of formula (ii), closed

**Resolution of the obstruction documented above.** The fix: instead of chasing a *single* domain
witness `T_i ⊇ Y_i` (which forces the wrong type-projection `P_i'` via `s_i ≤ t_i`), observe that
`t_i` is *itself* the directed sup of its own `subU`-self-consistent approximants
(`eq_iSupDirected_scPrincipal`) — a family on which `principal T = subU(principal T)` *exactly*
(`subU_principal_eq_of_rel_self`, by antisymmetry: `≤` from `subU`'s projection property, `≥` from
self-consistency). Since `d`, `subU`, `jArrow` are all continuous, the "type at `t_i`" `P_i` is
*itself* the directed sup (in the `ApproximableMap` order) of the "type at `T`" `P_T` over this same
family, so `P_i.rel W W` (already established) is, by directed-sup compactness
(`toApproxMap_rel_iSupDirected`/`mem_iSupDirected`), *already* witnessed at some single
self-consistent `T ∈ 𝒮(t_i)`. A second application of the same compactness fact (this time to the
continuity witness for `x`) and one directed-family common refinement (`scFamily_directed`) then
finds a *single* `T` simultaneously self-consistent, `x`-continuous, and `P_T`-self-relating — the
correct `T_i`. Notably, this argument uses only `subU`'s algebraicity/continuity and
`isFinitaryProjection_decode_subU` (Step 4, unconditional); **`d`'s polymorphism is never used**, so
the result below holds for *every* `d`, polymorphic or not — a strictly stronger and more uniform
fact than Scott's exercise statement requires. -/

/-- **`subU`'s self-relating neighbourhoods are exactly fixed under `principal`.** If `subU.rel T T`,
the "witnessing element" `↑T` is *exactly* fixed by `subU` (not merely approximated): `≤` is
`subU`'s projection property (`subU ≤ I`), `≥` is `principal_le_of_mem` applied to the membership
`subU.rel T T` gives via `rel_iff_mem_principal`. -/
theorem subU_principal_eq_of_rel_self {T : Set ℚ} (hT : U.mem T) (hTT : subU.rel T T) :
    subU.toElementMap (U.principal hT) = U.principal hT := by
  apply le_antisymm
  · exact toElementMap_le_self_of_le_idMap isProjection_subU.2 _
  · exact principal_le_of_mem ((subU.rel_iff_mem_principal hT).mp hTT)

/-- **Descending to a self-consistent approximant.** For `t` already `subU`-fixed, formula (ii) for
`subU` (Exercise 8.27(a)) applied at `t` and any target `T₀ ∈ t` produces a *self-consistent*
`T ⊆ T₀` still in `t`'s filter — the cofinality fact that makes the self-consistent nbhds a directed
family sup-ing to `t` itself (`eq_iSupDirected_scPrincipal` below). -/
theorem exists_rel_self_subset_of_mem {t : U.Element} (ht : subU.toElementMap t = t)
    {T₀ : Set ℚ} (hT₀ : t.mem T₀) : ∃ T, subU.rel T T ∧ t.mem T ∧ T ⊆ T₀ := by
  have hmem : (subU.toElementMap t).mem T₀ := by rw [ht]; exact hT₀
  obtain ⟨_, T, hTt, hTT₀, hTT⟩ :=
    (formula_of_isFinitaryProjection isFinitaryProjection_subU t).mp hmem
  exact ⟨T, hTT, hTt, hTT₀⟩


/-- **`scFamily t`'s principals form a directed family.** Given `i, j`, apply
`exists_rel_self_subset_of_mem` at the common refinement `i.1 ∩ j.1` (valid via `t.inter_mem`). -/
theorem scFamily_directed {t : U.Element} (ht : subU.toElementMap t = t) :
    ∀ i j : scFamily t, ∃ k : scFamily t, scPrincipal i ≤ scPrincipal k ∧ scPrincipal j ≤ scPrincipal k :=
  fun i j => by
    obtain ⟨T, hTT, htT, hTsub⟩ := exists_rel_self_subset_of_mem ht (t.inter_mem i.2.2 j.2.2)
    refine ⟨⟨T, hTT, htT⟩, ?_, ?_⟩
    · exact (U.principal_le_iff (t.sub i.2.2) (t.sub htT)).mpr (hTsub.trans Set.inter_subset_left)
    · exact (U.principal_le_iff (t.sub j.2.2) (t.sub htT)).mpr (hTsub.trans Set.inter_subset_right)

/-- **`t` is the directed sup of its own self-consistent approximants.** Cofinality
(`exists_rel_self_subset_of_mem`) shows the self-consistent sub-family already has the same sup as
the full principal-approximant family (`eq_iSupDirected_principal`), namely `t` itself. -/
theorem eq_iSupDirected_scPrincipal {t : U.Element} (ht : subU.toElementMap t = t) :
    t = NeighborhoodSystem.iSupDirected scPrincipal (scFamily_directed ht) := by
  apply Element.ext
  intro Z
  rw [mem_iSupDirected]
  constructor
  · intro hZ
    obtain ⟨T, hTT, htT, hTZ⟩ := exists_rel_self_subset_of_mem ht hZ
    exact ⟨⟨T, hTT, htT⟩, (U.mem_principal _).mpr ⟨t.sub hZ, hTZ⟩⟩
  · rintro ⟨i, hi⟩
    obtain ⟨hZmem, hTZ⟩ := (U.mem_principal _).mp hi
    exact t.up_mem i.2.2 hZmem hTZ


/-! ## Discussion: "why does this equation mean that `x` is in the product?"

Scott's parenthetical question, about `x(t) = d(t)(x(t))` (all `t`): unwind the right-hand side
using Exercise 8.26's `Uapply`/`Ulam` (the self-hosted application of an element of `𝒰` regarded
as a "type"): `d(t)(x(t))` means `Uapply (d.toElementMap t) (x.toElementMap t)`, i.e. *decode*
`d(t)` via `j_→` into an actual map `D_{d(t)} : 𝒰 → 𝒰` and apply it to `x(t)`. Since `d` is a
polymorphic type, `d(t) ∈ Fix(subU)` for every `t` (`polymorphicType_apply_mem_fix`), hence
`D_{d(t)}` is *always* a genuine finitary projection — "the type at `t`" in the informal reading.
The equation `x(t) = D_{d(t)}(x(t))` is then exactly the defining property of being a **fixed
point** of that projection, i.e. `x(t) ∈ Fix(D_{d(t)})`. Since `Fix` of a finitary projection is
(order-isomorphic to) a genuine domain, this says precisely: *`x(t)` is a legitimate element of
the domain named by the type `t`*, for *every* type `t` simultaneously — i.e. `x` is a dependent
family `x : Π_{t : Type} D_{d(t)}`, a bona fide element of the "continuous product." Nothing about
this needs a separate Lean lemma beyond what is already proved above; it is genuinely just Scott
inviting the reader to notice that his equation *is* the universal-domain encoding of dependent
products (a form of impredicative/parametric polymorphism, à la System F).

## Why "the problem is to show it is finitary" is left unattempted here

Scott's own hint stops at "it is easy to check that `Π(d)` is a projection" — established above,
in fact unconditionally, for *every* `d`. For the finitary half he gives **no technique at all**,
unlike literally every other exercise/theorem in this book (which come with a concrete "(Hint:
...)" naming a specific construction or reduction). This is deliberate: Exercise 8.27 is the
**last exercise in the book**, credited to a named correspondent (James Donahue), and is posed as
a genuinely open-ended research problem about a *dependent*/*polymorphic* product — Scott is
asking the reader to discover a construction, not recalling one.

Concretely, every "finitary-closure" result proved elsewhere in this project
(`finitaryProjection_arrowComb`, `_prodComb`, `_sumComb` in `Proposition810b.lean`; Theorem 8.6(b)'s
own `isFinitary_subApprox`) works by exhibiting `Fix` of the projection in question as
order-isomorphic to an *already available* domain (a product/sum/function-space/subsystem-space
built from *fixed*, finitely many ingredient domains). `Fix(piD d)` has no such ready-made
candidate: it is the dependent product `Π_{t : 𝒰} Fix(D_{d(t)})` ranging over a *continuum* of
"index" values `t`, indexed by a domain (`𝒰`) rather than a finite/discrete set, with the fibers
`Fix(D_{d(t)})` themselves varying (dependently, via `d`) rather than staying fixed. Constructing a
"domain of dependent-continuous-sections" and proving `Fix(piD d)` is isomorphic to it is a
genuinely new piece of domain theory (closer to a logical-relations/realizability argument for
System-F-style parametric polymorphism than to any single-step algebraic closure fact), with no
template anywhere in Lectures I–VIII. It is intentionally left as the natural terminus of this
formalization project, matching Scott's own framing of it as "the problem."
-/
end DomainTheory.NeighbourhoodSystems

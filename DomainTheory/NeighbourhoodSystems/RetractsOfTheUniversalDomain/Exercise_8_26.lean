module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition_8_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

section
/- concordance: source L5246 EXERCISE 8.26 untyped calculus in U -/
-- Exercise826/Uapply.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

/-- **Self-application inside `𝒰`** (the end-of-lecture equation `u(x) := j_→(u)(x)`): decode
`u : 𝒰` into an actual function `𝒰 → 𝒰` via `j_→` (`jArrow`, Definition 8.9), then apply it to
`x`. -/
noncomputable def Uapply (u x : U.Element) : U.Element :=
  (evalMap U U).toElementMap (pair (jArrow.toElementMap u) x)

end DomainTheory.NeighbourhoodSystems
end

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

section
/-- **Self-abstraction inside `𝒰`** (the end-of-lecture equation `λx.τ ≅ i_→(λx.τ)`): given the
"outside" function `f : 𝒰 → 𝒰` (`τ`'s ordinary denotation as an approximable map), encode it into
`𝒰` via `i_→` (`iArrow`, Definition 8.9). -/
noncomputable def Ulam (f : ApproximableMap U U) : U.Element :=
  iArrow.toElementMap (toFilter f)
end

section
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

/-- **Scott's translation recipe for a `λ`-abstraction**, `λx^{D_a}.σ ↦ λx. b(σ'[a(x)/x])`: given
the further-translated body `body : E → E` (Scott's `σ'`, the untyped realization of `σ` as a
function of `x`), form the projection-sandwiched abstraction `b∘body∘a`. Stated for an arbitrary
neighbourhood system `E` and arbitrary `a, b : E → E` — specializes to Scott's `𝒰`/finitary
projections, but needs nothing special about `E`. -/
def translateAbs (a b body : ApproximableMap E E) : ApproximableMap E E :=
  b.comp (body.comp a)
end

section
/-- **Faithfulness (`β`-soundness) of the self-hosted encoding.** Applying the self-hosted
abstraction of `f` recovers `f` itself: `Uapply (Ulam f) x = f(x)`. The internal `λ`-calculus of
`𝒰` literally computes the same thing as the "outside" one it is modelling — this is the actual
content of "the pay-off," beyond bare notation. Uses only `jArrow_comp_iArrow : j_→∘i_→ = I` (the
retraction half of Definition 8.9's fixed pair) and `evalMap`'s defining equation
(`evalMap_apply`). -/
theorem Uapply_Ulam (f : ApproximableMap U U) (x : U.Element) :
    Uapply (Ulam f) x = f.toElementMap x := by
  have hround : toApproxMap (toFilter f) = f := by
    have he := (funSpaceEquiv U U).apply_symm_apply f
    rwa [funSpaceEquiv_apply, funSpaceEquiv_symm_apply] at he
  unfold Uapply Ulam
  have h1 : jArrow.toElementMap (iArrow.toElementMap (toFilter f))
      = (jArrow.comp iArrow).toElementMap (toFilter f) :=
    (toElementMap_comp jArrow iArrow (toFilter f)).symm
  rw [h1, jArrow_comp_iArrow, toElementMap_idMap, evalMap_apply, hround]
end

section
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

/-- **A sanity check: the identity abstraction translates to the identity, and the recipe applied
to `body = id` (the trivial "translation" of a bare variable `σ = x`) already has the right type
for free** — `translateAbs a b (idMap E) = b∘a`, matching that a bare variable of type `D_a` fed
through the `a`-then-`b` sandwich needs no further work. Included as a `0`-th case of the
induction discussed above (the base case: variables). -/
theorem translateAbs_idMap {a b : ApproximableMap E E} : translateAbs a b (idMap E) = b.comp a := by
  unfold translateAbs
  rw [idMap_comp]
end

section
set_option linter.unusedVariables false

theorem example_826.{u} : ∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  {a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
  @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
    (@DomainTheory.NeighbourhoodSystems.translateAbs α E a b
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α E))
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α E E E b a) :=
  @DomainTheory.NeighbourhoodSystems.translateAbs_idMap
end

section
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

/-- **"Be sure to show that this result has the right type."** `translateAbs a b body` always
satisfies the defining sandwich equation `f = b∘f∘a` of Scott's `D_a → D_b` translation scheme
(the "sense defined above" — see `Proposition810b.elementIsoOfProjectionPair`/
`arrowComb_elementIso`), **regardless of `body`** — the *only* thing this uses is idempotence of
`a` and `b` (true of every retraction, Definition 8.1, in particular every finitary projection,
Definition 8.3). Pure associativity + idempotence, mirroring the book's own one-line proof
("`(a×b)∘(a×b) = ... = a×b`," `Proposition 8.10`'s proof) transplanted to the abstraction case. -/
theorem translateAbs_sandwich {a b body : ApproximableMap E E}
    (ha : Retraction a) (hb : Retraction b) :
    b.comp ((translateAbs a b body).comp a) = translateAbs a b body := by
  show b.comp ((b.comp (body.comp a)).comp a) = b.comp (body.comp a)
  rw [comp_assoc b (body.comp a) a, comp_assoc body a a, ha.out, ← comp_assoc b b (body.comp a), hb.out]
end

section
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

/-- **The matching claim for application**: if `f` already "has the right type" (`f = b∘f∘a`) and
`x` already "has type `D_a`" (`a(x) = x`), then `f(x)` already "has type `D_b`" (`b(f(x)) = f(x)`).
Together with `translateAbs_sandwich`, this is the type-soundness invariant that both the
`λ`-abstraction and application clauses of the typed-to-untyped translation preserve. -/
theorem translateApp_hasType {a b f : ApproximableMap E E} (hsandwich : b.comp (f.comp a) = f)
    {x : E.Element} (hx : a.toElementMap x = x) :
    b.toElementMap (f.toElementMap x) = f.toElementMap x := by
  conv_rhs => rw [← hsandwich, toElementMap_comp, toElementMap_comp, hx]
end

end DomainTheory.NeighbourhoodSystems
end

section
end

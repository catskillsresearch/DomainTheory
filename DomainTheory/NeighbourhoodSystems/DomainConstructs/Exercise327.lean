/-ai
This file gathers and re-exports the ingredients of Exercise 3.27: graphs of approximable maps, the family of all such graphs, meets and joins of families of maps, closure of that family under nonempty intersections and directed unions, and the representation isomorphism of Exercise 2.22 together with the function-space equivalence, so the function space is presented as a domain.

A nonempty directed family of members of C has its union in C.

The numbered name example_327 is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.C_dir

@[expose] public section

/-!
# Exercise 3.27 (Scott 1981, PRG-19, §3) — `(𝒟₀ → 𝒟₁)` is a domain, via Exercise 2.22

(*For set theorists.*) Scott asks for *another* proof that the family of approximable mappings
`f : 𝒟₀ → 𝒟₁` is isomorphic to a domain, "by employing the general argument of Exercise 2.22"
(the abstract representation theorem: any family of sets closed under non-empty intersections and
directed unions is inclusion-isomorphic to a domain).

The set-theoretic content: identify each approximable map `f` with its **graph**
`graph f = {(X, Y) ∣ X f Y} ⊆ 𝒫(Δ₀) × 𝒫(Δ₁)`, and let `C = {graph f}` be the family of all such
graphs. Then

* `C` is closed under **non-empty intersections** — the pointwise *meet* `⋀ 𝒮` of a family of
  approximable maps (relate `X` to `Y` iff every member does) is again approximable (`meetMap`);
* `C` is closed under **directed unions** — the *join* `⋁ 𝒮` of a directed family (relate `X` to `Y`
  iff some member does) is again approximable, the consistency condition using directedness
  (`joinMap`).

So Exercise 2.22 (`reprIso`) re-presents `C` — hence, via `graph` and Theorem 3.10 (`funSpaceEquiv`),
the whole function space `|𝒟₀ → 𝒟₁|` — as the domain of a neighbourhood system, *without* writing
down the step-set neighbourhoods of Definition 3.8 explicitly. This is exactly Scott's "compare with
3.9/3.10" alternative.

**Axioms.** As flagged by Scott ("for set theorists"), this inherits `Classical.choice` from
Exercise 2.22 and from the `graph`-inversion.
-/

namespace DomainTheory.NeighbourhoodSystems.Exercise327

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}






/-! ### The meet of a non-empty family of maps. -/




/-! ### The join of a directed family of maps. -/




/-! ### `C ≅ Hom(𝒟₀, 𝒟₁) ≅ |𝒟₀ → 𝒟₁|`. -/


/-! ### Exercise 3.27. -/


end DomainTheory.NeighbourhoodSystems.Exercise327

namespace DomainTheory.NeighbourhoodSystems.Exercise327

set_option linter.unusedVariables false

theorem example_327.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β} (𝒮 : Set (Set (Prod (Set α) (Set β)))),
  @Set.Nonempty (Set (Prod (Set α) (Set β))) 𝒮 →
    @LE.le (Set (Set (Prod (Set α) (Set β)))) (@Set.instLE (Set (Prod (Set α) (Set β)))) 𝒮
        (@DomainTheory.NeighbourhoodSystems.Exercise327.C α β V₀ V₁) →
      @DirectedOn (Set (Prod (Set α) (Set β)))
          (fun (x1 x2 : Set (Prod (Set α) (Set β))) =>
            @LE.le (Set (Prod (Set α) (Set β))) (@Set.instLE (Prod (Set α) (Set β))) x1 x2)
          𝒮 →
        @Membership.mem (Set (Prod (Set α) (Set β))) (Set (Set (Prod (Set α) (Set β))))
          (@Set.instMembership (Set (Prod (Set α) (Set β))))
          (@DomainTheory.NeighbourhoodSystems.Exercise327.C α β V₀ V₁) (@Set.sUnion (Prod (Set α) (Set β)) 𝒮) :=
  @DomainTheory.NeighbourhoodSystems.Exercise327.C_dir

end DomainTheory.NeighbourhoodSystems.Exercise327

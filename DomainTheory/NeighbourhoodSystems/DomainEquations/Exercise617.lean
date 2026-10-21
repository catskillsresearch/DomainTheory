/-ai
This file gathers and re-exports Exercise 6.17, the proof that the domain C of finite or infinite binary sequences is the initial algebra for the functor sending a domain X to the separated sum of the unit with two copies of X. It re-exports the category of neighbourhood systems with no empty neighbourhood and of strict approximable maps, the three-way separated sum with its sum map, canonical injections, and shape lemmas, the functor and the algebra structure on C, the descent map into an arbitrary algebra and the algebra homomorphism it induces, and the commutation and uniqueness lemmas for that homomorphism, including the head recursion on cones and singletons, strictness, the identification of the bottom element, and the two composites of the domain-equation equivalence.

Every algebra homomorphism out of the algebra on C equals the descent homomorphism.

The numbered name example_617 is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.descAlgHom_uniq

@[expose] public section

/-!
# Exercise 6.17 (Scott 1981, PRG-19, §6) — the algebras for which `C` is initial

> **EXERCISE 6.17.** What are the algebras for which `C` is initial? If `A` of 6.2 is a generalization
> of `B`, what is the corresponding generalization of `C`? Prove that it exists and explain what are
> the algebras involved.

`C` (Example 4.4: finite-or-infinite binary sequences) satisfies the domain equation
`C ≅ {{Λ}} + C + C` (Example 6.2, `Example62C.lean`). So `C` is a solution of the domain equation for
the functor

`T(X) = 𝟙 + X + X`   (one terminator + two successor copies).

This module proves that **`C` is the *initial* `T`-algebra**: for every `T`-algebra `(E, k)` there is a
*unique* homomorphism `C → E`. Concretely a `T`-algebra is a strict map `k : 𝟙 + E + E → E`, which by
the universal property of the separated sum is the same data as

* a distinguished element `e ∈ |E|` (the image of the terminator `𝟙`), and
* two strict endomaps `f₀, f₁ : E → E` (the two successor branches);

so **the algebras for which `C` is initial are the domains carrying a point and two strict unary
operations**, and the unique homomorphism `C → E` interprets a finite-or-infinite binary sequence
`b₀b₁b₂…` as `f_{b₀}(f_{b₁}(… e …))`.

## Why a bespoke category of `∅`-free domains

Scott's separated sum `𝒟₀ + 𝒟₁` (Exercise 3.18) is a neighbourhood system **only** under the standing
assumption `∅ ∉ 𝒟` (an empty neighbourhood of one summand would become a spurious consistency witness
for the other tag, breaking `inter_mem`). Consequently the functor `T(X) = 𝟙 + X + X` does **not**
extend to a total endofunctor of the all-systems category `DomainObj`, and the existence Theorem 6.14
(stated over `DomainObj`) cannot be instantiated directly.

Following Scott — who restricts to the category of `∅`-free systems and *strict* maps in Exercise 6.19
— we instantiate the abstract categorical vocabulary (Definitions 6.3–6.5) on the bespoke object type
`StrictDomainObj` of neighbourhood systems with **no empty neighbourhood**, with **strict approximable
maps** as morphisms. The functor `T` then reuses the existing `sum3` (Example 6.2, the genuine
three-way separated sum) and a three-way sum map, and initiality of `C` is proved **directly** (we
construct the homomorphism and prove its uniqueness by the finite-approximant argument), rather than
routing through the colimit construction of Theorem 6.14.

Everything is choice-free where it is data; the homomorphism/uniqueness layer reuses the project's
established machinery.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510


/-! ## The category of `∅`-free domains and strict maps -/


/-! ## The functor `T(X) = 𝟙 + X + X` on objects -/


/-! ### Membership-shape lemmas for `sum3` (no nesting through the wrong tag) -/

section ShapeLemmas

open Example62C

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ} {h₀ : ∀ X, V₀.mem X → X.Nonempty}
  {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty} {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}


end ShapeLemmas

/-! ### The three-way sum map `f₀ + f₁ + f₂` -/

section SumMap3

open Example62C

variable {α β γ α' β' γ' : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
  {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'} {V₂' : NeighborhoodSystem γ'}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}
  {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}
  {h₂' : ∀ Z, V₂'.mem Z → Z.Nonempty}


end SumMap3

/-! ### The canonical injections `D_i ↪ D₀+D₁+D₂` -/

section SumInj

open Example62C

variable {α β γ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}


end SumInj

/-! ### Monotonicity of the injections, and the action of `f₀+f₁+f₂` on them -/

section SumInjMap

open Example62C

variable {α β γ α' β' γ' : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
  {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'} {V₂' : NeighborhoodSystem γ'}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}
  {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}
  {h₂' : ∀ Z, V₂'.mem Z → Z.Nonempty}


end SumInjMap

/-! ## The functor `T(X) = 𝟙 + X + X` -/


/-! ## `C` as a `T`-algebra -/


/-! ## Initiality of `(C, i)`: the unique homomorphism into any `T`-algebra

We first relate the domain-equation isomorphism `toCC = ccEquiv` to the separated-sum injections:
the terminator `Λ̂` lands on the `𝟙`-copy, and prepending a bit (`consMap b`) lands on the `b`-th
`C`-copy. -/

namespace Example62C

open Example44 ExampleB Example62


end Example62C

/-! ### The homomorphism `desc : C → E` for a `T`-algebra `B = (E, k)` -/

section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)


/-! ### The homomorphism square and uniqueness -/


end Initial


end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_617 : ∀
  (B :
    @DomainTheory.NeighbourhoodSystems.TAlgebra DomainTheory.NeighbourhoodSystems.StrictDomainObj
      DomainTheory.NeighbourhoodSystems.instCategoryStrictDomainObj DomainTheory.NeighbourhoodSystems.Tc)
  (h' :
    @DomainTheory.NeighbourhoodSystems.AlgHom DomainTheory.NeighbourhoodSystems.StrictDomainObj
      DomainTheory.NeighbourhoodSystems.instCategoryStrictDomainObj DomainTheory.NeighbourhoodSystems.Tc
      DomainTheory.NeighbourhoodSystems.Calg B),
  @Eq
    (@DomainTheory.NeighbourhoodSystems.AlgHom DomainTheory.NeighbourhoodSystems.StrictDomainObj
      DomainTheory.NeighbourhoodSystems.instCategoryStrictDomainObj DomainTheory.NeighbourhoodSystems.Tc
      DomainTheory.NeighbourhoodSystems.Calg B)
    h' (DomainTheory.NeighbourhoodSystems.descAlgHom B) :=
  DomainTheory.NeighbourhoodSystems.descAlgHom_uniq

end DomainTheory.NeighbourhoodSystems

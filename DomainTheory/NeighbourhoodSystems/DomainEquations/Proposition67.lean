module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition63
public import DomainTheory.NeighbourhoodSystems.DomainEquations.strHom
public import DomainTheory.NeighbourhoodSystems.DomainEquations.lambek
public import DomainTheory.NeighbourhoodSystems.DomainEquations.tStr
public import DomainTheory.NeighbourhoodSystems.DomainEquations.str_comp_desc

@[expose] public section

/-!
# Lecture VI — Proposition 6.7 (Scott 1981, PRG-19): Lambek's lemma

**Proposition 6.7.** If `i : T(D) → D` is an initial `T`-algebra, then so is `T(i) : T²(D) → T(D)`
and `i` is the isomorphism from `T(D)` to `D`.

We formalise the second (and decisive) half: the structure map of an initial algebra is an
isomorphism. Writing `A = (D, i)`, the functor turns `i` into a new algebra `(T(D), T(i))` (`tStr`),
and `i` itself is a homomorphism `(T(D), T(i)) → (D, i)` (`strHom`). Initiality supplies a
homomorphism `j : (D,i) → (T(D),T(i))`, and the composite `i ∘ j : (D,i) → (D,i)` must be the
identity (`str_comp_desc`). Functoriality then gives `T(i) ∘ T(j) = T(i ∘ j) = I`, and the
homomorphism square for `j` yields `j ∘ i = I`. Hence `i` and `j` are mutually inverse: `i` is an
isomorphism (`lambek`).

This is exactly Scott's remark that "if we are going to have initial algebras at all we have to
satisfy the domain equation `D ≅ T(D)`".

Choice-free (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems

universe u

variable {Obj : Type u} [Category Obj] {T : Endofunctor Obj}





end DomainTheory.NeighbourhoodSystems

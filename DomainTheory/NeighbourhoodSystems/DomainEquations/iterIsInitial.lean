/-ai
For the product endofunctor, the infinite iterate with its cons map is an initial algebra, and the mediating morphism is the descent homomorphism. Any other strict homomorphism commutes with the cons map in the same way as the descent map, so the uniqueness theorem for maps with that commutation identifies its underlying map with the descent map, and the two homomorphisms agree.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_zero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.component_bot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.imap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise618.descMap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise618.descMap_strict
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descMap_comm
public import DomainTheory.NeighbourhoodSystems.DomainEquations.comm_unique
public import DomainTheory.NeighbourhoodSystems.DomainEquations.iterAlg
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise618.descAlgHom

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510


namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- **Exercise 6.18 (initial-algebra half) — `𝒟^∞` is the initial `T`-algebra for `T(X) = 𝒟 × X`.**
For every `T`-algebra `(E, k)` the descent map `h(⟨x₀,x₁,…⟩) = k(x₀, k(x₁, …))` is the *unique*
strict homomorphism `𝒟^∞ → E`. Together with Exercise 3.16's `𝒟^∞ ≅ 𝒟 × 𝒟^∞` (the domain-equation
half), this exhibits `𝒟^∞` both as the canonical solution of the domain equation and as the initial
algebra (determined up to iso by Proposition 6.6). -/
def iterIsInitial (Dom : StrictDomainObj.{w}) : IsInitial (iterAlg Dom) where
  desc := descAlgHom Dom
  uniq B h := by
    obtain ⟨hom, comm⟩ := h
    have hcomm : hom.1.comp (imap Dom.sys)
        = B.str.1.comp (prodMap (idMap Dom.sys) hom.1) := congrArg Subtype.val comm
    have hg : hom.1 = descMap B.str.1 :=
      comm_unique B.str.1 hom.2 (descMap_strict B.str.1 B.str.2) hcomm (descMap_comm B.str.1)
    have hhom : hom = ⟨descMap B.str.1, descMap_strict B.str.1 B.str.2⟩ := Subtype.ext hg
    subst hhom
    rfl

end Exercise618

end DomainTheory.NeighbourhoodSystems

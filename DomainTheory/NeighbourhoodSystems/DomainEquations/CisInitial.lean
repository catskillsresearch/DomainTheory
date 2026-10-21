/-ai
The algebra of finite and infinite binary sequences is an initial algebra for the endofunctor that sends a domain to the unit domain summed with the domain summed with itself. The homomorphism into an arbitrary algebra is the descent homomorphism, given by head recursion on sequences, and every algebra homomorphism equals that descent homomorphism.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition63
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import DomainTheory.NeighbourhoodSystems.DomainEquations.StrictDomainObj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Inst3
public import DomainTheory.NeighbourhoodSystems.DomainEquations.id_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.comp_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.tcObj_sys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj0_mem_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj1_mem_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj2_mem_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Tc_obj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Tc_map_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Calg
public import DomainTheory.NeighbourhoodSystems.DomainEquations.ccEquiv_apply
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descMap_strBot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descMap_strElem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617.descAlgHom
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descAlgHom_uniq

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510


/-- **Exercise 6.17 (existence half) — `(C, i)` is an initial `T`-algebra for `T(X) = 𝟙 + X + X`.**
The descent map `φ : C → E` is the closed-form head-recursion `φ(Λ) = e`, `φ(b·x) = f_b(φ x)`
(`f_b = k ∘ inj_b`), built choice-free via `liftC`; it is the unique `T`-algebra homomorphism, so `C`
is determined (up to iso, Proposition 6.6) as the initial algebra of `X ↦ 𝟙 + X + X`. -/
def CisInitial : IsInitial Calg where
  desc := descAlgHom
  uniq := fun B h => descAlgHom_uniq B h

end DomainTheory.NeighbourhoodSystems

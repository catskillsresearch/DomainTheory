/-ai
The algebra structure map of the domain C is the inverse of the domain-equation isomorphism of Example 6.2, from the sum of the unit system with two copies of C back to C, realized as an approximable map by the isomorphism construction and strict by the strictness of that construction. It sends the terminator to the lifted empty string and each bit-copy of an element to the corresponding successor.
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
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Tc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Tc_obj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Tc_map_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.isStrict_ofIso
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Cobj

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

open Example44 Example62C in
/-- **The `T`-algebra structure on `C`.** `(tcObj Cobj).sys = 𝟙 + C + C` (definitionally Example 6.2's
`CC`), and the structure map `i : 𝟙 + C + C → C` is the inverse of the domain-equation isomorphism
`ccEquiv` (Example 6.2), realised as an approximable map by `ofIso`; it is strict by `isStrict_ofIso`.
Concretely `i` sends the terminator to `Λ̂` and each `b`-copy of `x` to `b·x`. -/
abbrev cStr : ((Tc.obj Cobj) ⟶ Cobj) :=
  ⟨ofIso (by exact ccEquiv.symm), isStrict_ofIso _⟩

end DomainTheory.NeighbourhoodSystems

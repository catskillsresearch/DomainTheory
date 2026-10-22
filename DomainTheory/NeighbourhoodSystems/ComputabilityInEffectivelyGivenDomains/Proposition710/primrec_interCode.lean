/-ai
If the consistency function is primitive recursive, then the map sending a pair code to the intersection code of its two components is primitive recursive.

It is the primitive-recursive fold of the primitive-recursive outer step, with the right projection as the parameter, the constant 0 as the starting accumulator, and the left projection as the folded code, and this fold is the intersection code.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.interCode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.primrec_outerInterStp

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

variable (P : ComputablePresentation V)

theorem primrec_interCode (cons : ℕ → ℕ) (hconsp : Nat.Primrec cons) :
    Nat.Primrec (fun t => V.interCode P cons t.unpair.1 t.unpair.2) :=
  (primrec_foldCode (V.primrec_outerInterStp P cons hconsp) Nat.Primrec.right
    (Nat.Primrec.const 0) Nat.Primrec.left).of_eq (fun _ => rfl)

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems

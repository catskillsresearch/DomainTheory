/-ai
If the consistency function is primitive recursive, then the outer intersection step is primitive recursive.

It is the primitive-recursive fold of the primitive-recursive inner step, reading the left projection as the outer index, the left projection of the right as the accumulator, and the right projection of the right as the parameter, and this fold is the outer step.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.outerInterStp
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.primrec_innerInterStp

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

variable (P : ComputablePresentation V)

theorem primrec_outerInterStp (cons : ℕ → ℕ) (hconsp : Nat.Primrec cons) :
    Nat.Primrec (V.outerInterStp P cons) :=
  (primrec_foldCode (V.primrec_innerInterStp P cons hconsp) Nat.Primrec.left
    (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.right.comp Nat.Primrec.right)).of_eq
    (fun _ => rfl)

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems

/-ai
Every element of the generated semigroup lies in the intersection of the recursively enumerable elements and the functional elements.

The proof is by induction on the generation. The generators R, L, and G-bar are each combinatory and functional. A composite of two such elements is combinatory by the combinatory property of enumeration composition, and functional by the functional property of that composition.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.Rcomb_combinatory
public import DomainTheory.DataTypesAsLattices.Enumeration.Lcomb_combinatory
public import DomainTheory.DataTypesAsLattices.Enumeration.Rcomb_mem_FUN
public import DomainTheory.DataTypesAsLattices.Enumeration.Lcomb_mem_FUN
public import DomainTheory.DataTypesAsLattices.Enumeration.Gbar_combinatory
public import DomainTheory.DataTypesAsLattices.Enumeration.Gbar_mem_FUN
public import DomainTheory.DataTypesAsLattices.Enumeration.enumComp_combinatory
public import DomainTheory.DataTypesAsLattices.Enumeration.enumComp_mem_FUN

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem generatedSemigroup_mem_RE_FUN {u : Pomega} (hu : GeneratedSemigroup u) :
    u ∈ RE ∩ FUN := by
  induction hu with
  | R => exact ⟨Rcomb_combinatory, Rcomb_mem_FUN⟩
  | L => exact ⟨Lcomb_combinatory, Lcomb_mem_FUN⟩
  | Gbar => exact ⟨Gbar_combinatory, Gbar_mem_FUN⟩
  | comp _ _ ihu ihv =>
      exact ⟨enumComp_combinatory ihu.1 ihv.1, enumComp_mem_FUN _ _⟩

end DomainTheory.DataTypesAsLattices

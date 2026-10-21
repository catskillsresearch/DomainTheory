/-ai
Every component of a finite list of elements of Pω lies in the degree of the single generator of that list.

Theorem 3.6 supplies, as its first component, the hypothesis required by the theorem that the components of a packed list lie in a degree.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.theorem_3_6_finite
public import DomainTheory.DataTypesAsLattices.Enumeration.packList_components_mem_Deg

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code






















































theorem generators_mem_singleGenerator_degree (xs : List Pomega) :
    ∀ x, x ∈ xs → x ∈ Deg (singleGenerator xs) :=
  packList_components_mem_Deg (theorem_3_6_finite xs).1

end DomainTheory.DataTypesAsLattices

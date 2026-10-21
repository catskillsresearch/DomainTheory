/-ai
The second recursion value of an element u is the graph of the map sending x to the union, over m in x, of u applied to the numeral of apply(m)(num(m)). In Scott's Theorem 3.3 (i) this is the set denoted by the code v(n).
ai-/

module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.applyNat
public import DomainTheory.DataTypesAsLattices.Enumeration.num

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, Theorem 3.3 (i).** The set denoted by the code `v(n)`. -/
def secondRecVal (u : Pomega) : Pomega :=
  graph (fun x => ⋃ m ∈ x, funOf u (ofNat (applyNat m (num m))))

end DomainTheory.DataTypesAsLattices

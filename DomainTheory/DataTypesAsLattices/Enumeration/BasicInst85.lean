/-ai
This instance decides the relation beforeHalt: it holds of m and j exactly when the halt enumeration differs from m at every index strictly below j + 1, by passing between that bounded statement and quantification over the corresponding initial segment.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.haltEnum
public import DomainTheory.DataTypesAsLattices.Enumeration.beforeHalt

@[expose] public section

set_option linter.unusedSectionVars false

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

instance : DecidableRel beforeHalt :=
  fun m j => decidable_of_iff (∀ i : Fin (j + 1), haltEnum i.val ≠ m)
    ⟨fun h i hi => h ⟨i, hi⟩, fun h i => h i.val i.isLt⟩

end DomainTheory.DataTypesAsLattices

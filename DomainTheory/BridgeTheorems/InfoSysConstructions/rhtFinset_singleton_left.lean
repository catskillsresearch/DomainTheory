/-ai
The right part of a singleton consisting of one left token is empty.

A right token in that right part would be a member of the singleton and hence a left token, which is impossible, and the empty set has no members.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import Mathlib.Order.Sum.Order
import all Mathlib.Order.Sum.Order
public import Mathlib.Order.WithBot
import all Mathlib.Order.WithBot
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)

omit [DecidableEq α] in

theorem rhtFinset_singleton_left (x : α) :
    rhtFinset ({SumToken.left x} : Finset (SumToken α β)) = ∅ := by
  ext y
  constructor
  · intro hy
    have : SumToken.right y ∈ ({SumToken.left x} : Finset _) := (mem_rhtFinset).1 hy
    exact False.elim (nomatch Finset.mem_singleton.mp this)
  · intro hy
    exact False.elim (Finset.notMem_empty y hy)

end InfoSysConstructions

end DomainTheory.BridgeTheorems

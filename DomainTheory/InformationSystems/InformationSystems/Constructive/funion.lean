module

public import Mathlib.Data.Finset.Basic
public import DomainTheory.InformationSystems.InformationSystems.Constructive.instLeftCommutativeInsert

@[expose] public section

namespace DomainTheory.InformationSystems.Constructive

variable {α : Type*} [DecidableEq α]

def funion (u v : Finset α) : Finset α := Multiset.foldr insert u v.1

end DomainTheory.InformationSystems.Constructive

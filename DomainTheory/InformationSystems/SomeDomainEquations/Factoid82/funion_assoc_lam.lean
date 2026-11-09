module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.functionSystem
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst23
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst27

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem funion_assoc_lam (a b c : Finset (RawLamToken α)) :
    (a ∪' b) ∪' c = a ∪' (b ∪' c) := by
  ext x
  constructor
  · intro hx
    rcases funion.mem.mp hx with h | h
    · rcases funion.mem.mp h with h | h
      · exact funion.mem.mpr (Or.inl h)
      · exact funion.mem.mpr (Or.inr (funion.mem.mpr (Or.inl h)))
    · exact funion.mem.mpr (Or.inr (funion.mem.mpr (Or.inr h)))
  · intro hx
    rcases funion.mem.mp hx with h | h
    · exact funion.mem.mpr (Or.inl (funion.mem.mpr (Or.inl h)))
    · rcases funion.mem.mp h with h | h
      · exact funion.mem.mpr (Or.inl (funion.mem.mpr (Or.inr h)))
      · exact funion.mem.mpr (Or.inr h)

end InfoSys

end DomainTheory.InformationSystems

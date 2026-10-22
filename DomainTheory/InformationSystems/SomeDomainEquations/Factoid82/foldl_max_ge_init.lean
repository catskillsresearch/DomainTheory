module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst9
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst10
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst17
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst18
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.rawDepth

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

omit [DecidableEq α] in

theorem foldl_max_ge_init (u : List (RawLamToken α)) (init : ℕ) :
    init ≤ List.foldl (fun d t => Nat.max d (rawDepth t)) init u := by
  induction u generalizing init with
  | nil => exact le_rfl
  | cons a as ih =>
    exact Nat.le_trans (Nat.le_max_left init (rawDepth a)) (ih _)

end InfoSys

end DomainTheory.InformationSystems

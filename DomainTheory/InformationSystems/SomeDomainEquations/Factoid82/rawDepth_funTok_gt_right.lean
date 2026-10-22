/-ai
A raw token occurring in the right argument list of a function token has depth strictly less than the depth of that function token.

The fold bound for list membership, together with the right argument of a maximum being at most the maximum, places the token's depth at most at the maximum of the two folded depths. Unfolding the depth of the function token, that maximum is strictly less than one plus itself.
ai-/
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
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.foldl_list_le_of_mem

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

omit [DecidableEq α] in

theorem rawDepth_funTok_gt_right {u v : List (RawLamToken α)} {t : RawLamToken α}
    (ht : t ∈ v) : rawDepth t < rawDepth (.funTok u v) := by
  have h : rawDepth t ≤
      Nat.max (List.foldl (fun d t => Nat.max d (rawDepth t)) 0 u)
        (List.foldl (fun d t => Nat.max d (rawDepth t)) 0 v) :=
    Nat.le_trans (foldl_list_le_of_mem ht) (Nat.le_max_right _ _)
  simp only [rawDepth]
  exact Nat.lt_of_le_of_lt h (Nat.lt_add_of_pos_left (Nat.succ_pos 0))

end InfoSys

end DomainTheory.InformationSystems

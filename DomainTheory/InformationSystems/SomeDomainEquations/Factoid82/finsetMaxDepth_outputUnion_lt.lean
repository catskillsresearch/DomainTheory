/-ai
If a finite set of input-output pairs is contained in the function set of a finite set of raw lambda tokens, and that function set is nonempty, then the finset depth of the output union of the pairs is strictly below the finset depth of the token set.

Some function token of the set has positive raw depth, so the finset depth is positive. Each token of the output union lies on the output list of a pair from the function set, and its raw depth is strictly below the raw depth of the corresponding function token, hence strictly below the finset depth. The strict right-fold bound then applies.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst9
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst10
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamFunFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.mem_listToFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.mem_lamFunFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst17
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst18
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamOutputUnion
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.mem_lamOutputUnion
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.rawDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.rawDepth_funTok_gt_right
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst31
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.finsetMaxDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.le_finsetMaxDepth_of_mem
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.foldr_max_lt_of_forall

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem finsetMaxDepth_outputUnion_lt {u : Finset (RawLamToken α)}
    {s : Finset (List (RawLamToken α) × List (RawLamToken α))}
    (hs : s ⊆ lamFunFinset u) (hfun : lamFunFinset u ≠ ∅) :
    finsetMaxDepth (lamOutputUnion s) < finsetMaxDepth u := by
  obtain ⟨p0, hp0⟩ := Finset.nonempty_of_ne_empty hfun
  have htok0 : .funTok p0.1 p0.2 ∈ u := mem_lamFunFinset.1 hp0
  have hpos : 0 < finsetMaxDepth u := by
    have hraw : 0 < rawDepth (.funTok p0.1 p0.2) := by
      simp only [rawDepth]
      exact Nat.add_pos_left (Nat.succ_pos 0) _
    exact Nat.lt_of_lt_of_le hraw (le_finsetMaxDepth_of_mem htok0)
  refine foldr_max_lt_of_forall (s := (lamOutputUnion s).1) hpos ?_
  intro t ht
  have ht' : t ∈ lamOutputUnion s := Finset.mem_def.2 ht
  rcases (mem_lamOutputUnion).1 ht' with ⟨p, hp, htp⟩
  have htok : .funTok p.1 p.2 ∈ u := mem_lamFunFinset.1 (hs hp)
  exact Nat.lt_of_lt_of_le
    (rawDepth_funTok_gt_right ((mem_listToFinset).1 htp))
    (le_finsetMaxDepth_of_mem htok)

end InfoSys

end DomainTheory.InformationSystems

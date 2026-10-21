/-ai
By Scott's Theorem 7.3(ii), applying an approximable endomap f to its fixed-point element yields an element below that fixed point.

A token a of the image comes from a set u contained in the fixed-point element and related by f to a. That containment yields a consistent set of function tokens in the element of f and a reachable set that entails u. Monotonicity of the relation of f moves the input to that reachable set and the output to the singleton of a. Extending the witnessing chain by this one step produces a longer chain whose value is that singleton, which entails a, so a lies in the fixed-point element.
ai-/

module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixChain_step_of_rel

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)


namespace ApproximableMap


/-- **Theorem 7.3(ii).** `f(fix(f)) ⊆ fix(f)`. -/
theorem toElement_fixElement_le (f : ApproximableMap A A) :
    f.toElement (fixElement A f) ≤ fixElement A f := by
  intro a ⟨u, hu, hrel⟩
  obtain ⟨w, hw, ⟨hwCon, _, v0, hv0, hEnt⟩⟩ :=
    exists_rel_of_subset_image (fixMap A) (approxMap_toElement A A f) u hu
  -- v0 entails u, and f.rel u {a}; mono to get f.rel v0 {a} after adjusting
  have hv0C := fixReach_con A hv0
  have huC : u ∈ A.Con := f.rel_dom hrel
  have hrel' : f.rel v0 {a} :=
    f.mono hrel hEnt
      (proposition_2_3_iii A (f.rel_cod hrel)) hv0C (f.rel_cod hrel)
  obtain ⟨n, hn⟩ := hv0
  obtain ⟨w', hw', hw'Con, hchain⟩ := fixChain_step_of_rel A f hw hn hrel'
  refine ⟨w', hw', ⟨hw'Con, A.con_sing a, {a}, ⟨n + 1, hchain⟩, ?_⟩⟩
  exact proposition_2_3_iii A (A.con_sing a)

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems

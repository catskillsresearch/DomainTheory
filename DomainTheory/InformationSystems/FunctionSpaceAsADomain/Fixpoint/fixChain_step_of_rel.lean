
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)


namespace ApproximableMap


/-- Extend a chain by one `f`-step using a token from `approxMap_toElement f`. -/
theorem fixChain_step_of_rel (f : ApproximableMap A A)
    {w : Finset (FunToken A A)} {n : Nat} {u v : Finset α}
    (hw : ↑w ⊆ (approxMap_toElement A A f).carrier)
    (hu : FixChain A w n u) (hrel : f.rel u v) :
    ∃ w' : Finset (FunToken A A),
      ↑w' ⊆ (approxMap_toElement A A f).carrier ∧
        FunCon A A w' ∧ FixChain A w' (n + 1) v := by
  let p := mkFunToken A A u v (f.rel_dom hrel) (f.rel_cod hrel)
  have hp : p ∈ (approxMap_toElement A A f).carrier := by
    change f.rel u v
    exact hrel
  let w' := insert p w
  have hw' : ↑w' ⊆ (approxMap_toElement A A f).carrier := by
    intro q hq
    rcases Finset.mem_insert.mp (Finset.mem_coe.1 hq) with rfl | hq
    · exact hp
    · exact hw (Finset.mem_coe.2 hq)
  have hw'Con : FunCon A A w' :=
    (approxMap_toElement A A f).consistent w' hw'
  have hwCon : FunCon A A w :=
    (approxMap_toElement A A f).consistent w hw
  have hu' : FixChain A w' n u :=
    fixChain_mono_w A hwCon hw'Con hu
      (fun q hq => (functionSystem A A).ent_refl hw'Con (Finset.mem_insert_of_mem hq))
  refine ⟨w', hw', hw'Con, u, hu', f.rel_dom hrel, f.rel_cod hrel, ?_⟩
  refine ⟨hw'Con, {p}, ?_, ?_, ?_⟩
  · intro q hq
    cases Finset.mem_singleton.mp hq
    exact Finset.mem_insert_self _ _
  · intro q hq
    cases Finset.mem_singleton.mp hq
    exact proposition_2_3_iii A (f.rel_dom hrel)
  · rw [funOutputUnion_singleton]
    exact proposition_2_3_iii A (f.rel_cod hrel)

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems

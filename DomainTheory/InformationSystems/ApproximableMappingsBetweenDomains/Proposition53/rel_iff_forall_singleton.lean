/-ai
For consistent finite sets, an approximable mapping relates them if and only if it relates the domain set to the singleton of every token in the codomain set.

If the relation holds, monotonicity with reflexivity of entailment on the domain set and the entailment of a chosen token gives the relation to that singleton. Conversely, induct on the codomain set. The empty set is reached by monotonicity from the empty relation and the empty entailments. For an insertion of a token into a finite set, the hypothesis gives the singleton, the inductive hypothesis gives the remaining set, and closure under union on the right, with the identity of a singleton union and insertion, gives the inserted set.
ai-/
module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys
namespace ApproximableMap

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable {A : InfoSys α} {B : InfoSys β}


/-- **Singleton reduction** (Scott, before Def 5.2). -/
theorem rel_iff_forall_singleton (f : ApproximableMap A B)
    {u : Finset α} {v : Finset β} (hu : u ∈ A.Con) (hv : v ∈ B.Con) :
    f.rel u v ↔ ∀ Y ∈ v, f.rel u ({Y} : Finset β) := by
  constructor
  · intro hrel Y hY
    exact f.mono hrel (proposition_2_3_iii A hu)
      (fun Z hZ => by
        rw [Finset.mem_singleton] at hZ
        subst hZ
        exact B.ent_refl hv hY)
      hu (B.con_sing Y)
  · intro hsing
    induction v using Finset.induction_on with
    | empty =>
      exact f.mono f.empty_rel (A.entSet_empty u) (B.entSet_empty ∅) hu B.con_empty
    | insert a s ha ih =>
      have hv' : insert a s ∈ B.Con := hv
      have hsCon : s ∈ B.Con := B.con_subset hv' (Finset.subset_insert a s)
      have h1 : f.rel u {a} := hsing a (Finset.mem_insert_self a s)
      have h2 : f.rel u s :=
        ih hsCon fun Y hY => hsing Y (Finset.mem_insert_of_mem hY)
      have hU : f.rel u ({a} ∪' s) := f.union_right h1 h2
      simpa [singleton_funion_eq] using hU

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems

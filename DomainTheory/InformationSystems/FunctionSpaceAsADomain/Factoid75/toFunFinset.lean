module

public import Mathlib.Data.Multiset.MapFold
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.InformationSystems.Factoid25
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BoolToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BoolPoint
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.StrictFunToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BasicInst22

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable (A : InfoSys α) (B : InfoSys β)

def toFunFinset (w : Finset (StrictFunToken A B)) : Finset (FunToken A B) :=
  ⟨Multiset.map (Subtype.val : StrictFunToken A B → FunToken A B) w.1,
    (Multiset.nodup_map_iff_of_injective Subtype.val_injective).2 w.nodup⟩

theorem mem_toFunFinset {w : Finset (StrictFunToken A B)} {p : FunToken A B} :
    p ∈ toFunFinset A B w ↔ ∃ q ∈ w, q.val = p := by
  change (p ∈ Multiset.map (Subtype.val : StrictFunToken A B → FunToken A B) w.1) ↔ _
  constructor
  · intro hp
    rcases Multiset.mem_map.mp hp with ⟨q, hq, heq⟩
    refine ⟨q, hq, heq⟩
  · intro ⟨q, hq, heq⟩
    exact Multiset.mem_map.mpr ⟨q, hq, heq⟩

theorem toFunFinset.empty :
    toFunFinset A B (∅ : Finset (StrictFunToken A B)) = (∅ : Finset (FunToken A B)) := by
  ext p
  constructor
  · intro hp
    rcases (mem_toFunFinset A B).1 hp with ⟨_, hq, _⟩
    exact False.elim (Finset.notMem_empty _ hq)
  · intro hp
    exact False.elim (Finset.notMem_empty _ hp)

theorem toFunFinset.insert (w : Finset (StrictFunToken A B)) (p : StrictFunToken A B) :
    toFunFinset A B (Insert.insert p w) = Insert.insert p.val (toFunFinset A B w) := by
  ext q
  constructor
  · intro hq
    rcases (mem_toFunFinset A B).1 hq with ⟨r, hr, rfl⟩
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem ((mem_toFunFinset A B).2 ⟨r, hr, rfl⟩)
  · intro hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact (mem_toFunFinset A B).2 ⟨p, Finset.mem_insert_self _ _, rfl⟩
    · rcases (mem_toFunFinset A B).1 hq with ⟨r, hr, rfl⟩
      exact (mem_toFunFinset A B).2 ⟨r, Finset.mem_insert_of_mem hr, rfl⟩

theorem toFunFinset.singleton (p : StrictFunToken A B) :
    toFunFinset A B ({p} : Finset (StrictFunToken A B)) = {p.val} := by
  ext q
  constructor
  · intro hq
    rcases (mem_toFunFinset A B).1 hq with ⟨r, hr, rfl⟩
    exact Finset.mem_singleton.mpr (congrArg Subtype.val (Finset.mem_singleton.mp hr))
  · intro hq
    have : q = p.val := Finset.mem_singleton.mp hq
    subst this
    exact (mem_toFunFinset A B).2 ⟨p, Finset.mem_singleton_self p, rfl⟩

theorem toFunFinset.subset {s w : Finset (StrictFunToken A B)} (h : s ⊆ w) :
    toFunFinset A B s ⊆ toFunFinset A B w := by
  intro p hp
  rcases (mem_toFunFinset A B).1 hp with ⟨q, hq, rfl⟩
  exact (mem_toFunFinset A B).2 ⟨q, h hq, rfl⟩

end InfoSys

end DomainTheory.InformationSystems

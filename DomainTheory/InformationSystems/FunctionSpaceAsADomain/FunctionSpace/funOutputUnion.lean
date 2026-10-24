module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.FunToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.BasicInst7
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.instLeftCommutativeFunInput
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.instLeftCommutativeFunOutput
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.mem_foldr_funOutput

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]
variable (A : InfoSys α) (B : InfoSys β)
universe u v

/-- Union of output components of a finite set of function-space tokens. -/
def funOutputUnion (s : Finset (FunToken A B)) : Finset β :=
  Multiset.foldr (fun p : FunToken A B => funion p.val.2) (∅ : Finset β) s.1

theorem funOutputUnion.empty : funOutputUnion A B (∅ : Finset (FunToken A B)) = ∅ :=
  rfl

theorem mem_funOutputUnion {s : Finset (FunToken A B)} {y : β} :
    y ∈ funOutputUnion A B s ↔ ∃ p ∈ s, y ∈ p.val.2 := by
  simpa [funOutputUnion] using mem_foldr_funOutput A B s.1 y

theorem funOutputUnion.funion (s t : Finset (FunToken A B)) :
    funOutputUnion A B (s ∪' t) = funOutputUnion A B s ∪' funOutputUnion A B t := by
  ext y
  constructor
  · intro hy
    rcases (mem_funOutputUnion A B).1 hy with ⟨p, hp, hy'⟩
    rcases mem_funion.mp hp with hp | hp
    · exact mem_funion.mpr (Or.inl ((mem_funOutputUnion A B).2 ⟨p, hp, hy'⟩))
    · exact mem_funion.mpr (Or.inr ((mem_funOutputUnion A B).2 ⟨p, hp, hy'⟩))
  · intro hy
    rcases mem_funion.mp hy with hy | hy
    · rcases (mem_funOutputUnion A B).1 hy with ⟨p, hp, hy'⟩
      exact (mem_funOutputUnion A B).2 ⟨p, mem_funion.mpr (Or.inl hp), hy'⟩
    · rcases (mem_funOutputUnion A B).1 hy with ⟨p, hp, hy'⟩
      exact (mem_funOutputUnion A B).2 ⟨p, mem_funion.mpr (Or.inr hp), hy'⟩

theorem funOutputUnion.singleton (p : FunToken A B) :
    funOutputUnion A B {p} = p.val.2 := by
  ext y
  constructor
  · intro hy
    rcases (mem_funOutputUnion A B).1 hy with ⟨q, hq, hy'⟩
    have : q = p := Finset.mem_singleton.mp hq
    subst this
    exact hy'
  · intro hy
    exact (mem_funOutputUnion A B).2 ⟨p, Finset.mem_singleton_self p, hy⟩

theorem funOutputUnion.insert (s : Finset (FunToken A B)) (p : FunToken A B) :
    funOutputUnion A B (Insert.insert p s) = p.val.2 ∪' funOutputUnion A B s := by
  have h : Insert.insert p s = ({p} : Finset (FunToken A B)) ∪' s := by
    ext q
    constructor
    · intro hq
      rcases Finset.mem_insert.mp hq with hqp | hq
      · exact mem_funion.mpr (Or.inl (hqp ▸ Finset.mem_singleton_self p))
      · exact mem_funion.mpr (Or.inr hq)
    · intro hq
      rcases mem_funion.mp hq with hq | hq
      · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hq))
      · exact Finset.mem_insert_of_mem hq
  rw [h, funOutputUnion.funion, funOutputUnion.singleton]

end InfoSys


end DomainTheory.InformationSystems
